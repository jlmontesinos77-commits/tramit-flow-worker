#!/usr/bin/env python3
"""TramitFlow - trabajador externo (corre en GitHub Actions).

Vive en un repositorio PUBLICO (tramit-flow-worker) a proposito: en los
repositorios publicos GitHub no cobra los minutos de Actions, y en el privado
el trabajador se comia la cuota del mes en pocos dias. Aqui no hay nada
secreto: la clave va en el secreto TRABAJADOR_CLAVE del repositorio y los
registros de la ejecucion (que son publicos) solo llevan direcciones de
documentos oficiales e identificadores, nunca textos ni claves.

Hace lo que una edge function de Supabase no puede:
  - bajar de servidores que cortan a la IP de Supabase o que solo negocian
    TLS antiguo (portaldogc: renegociacion insegura, la causa real del
    "error sending request" de Deno),
  - leer PDFs de boletin a dos columnas, paginas ISO-8859-1 sin declarar,
  - dar capa de texto a PDFs escaneados (qpdf + ocrmypdf, binarios).

Habla SOLO con la edge function pf-trabajador-externo. Nunca ve la clave de
servicio: se identifica con la cabecera x-trabajador-clave (secreto
TRABAJADOR_CLAVE del repositorio = pf_credencial.trabajador_externo).

Uso:
  python externo.py contar      -> escribe hay=true|false en $GITHUB_OUTPUT
  python externo.py trabajar    -> toma tareas, las hace y devuelve resultado

Solo biblioteca estandar de Python; los binarios (pdftotext, qpdf, ocrmypdf)
los instala el workflow unicamente si hay trabajo.
"""
from __future__ import annotations

import html
import html.parser
import json
import os
import re
import shutil
import signal
import ssl
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
import warnings

warnings.filterwarnings("ignore", category=DeprecationWarning)

PUERTA = os.environ.get(
    "TRAMITFLOW_PUERTA",
    "https://bblvjqekflyytsfneisd.supabase.co/functions/v1/pf-trabajador-externo",
)
CLAVE = os.environ.get("TRABAJADOR_CLAVE", "")
UA_TOKEN = "TramitFlow"
UA = "Mozilla/5.0 (compatible; TramitFlow-externo/1.0; +https://kolven.es)"

MAX_BYTES = 300 * 1024 * 1024          # planes generales escaneados: el de Lugo pesa 198 MB
MAX_SUBIDA = 49 * 1024 * 1024          # el bucket 'normas' admite 50 MB por fichero
MIN_TEXTO = 500                         # por debajo, la puerta la cierra como fallida
PRESUPUESTO_S = int(os.environ.get("PRESUPUESTO_MIN", "150")) * 60
PAUSA_HOST_S = 1.5                      # cortesia con cada servidor
OCR_TIMEOUT_S = 40 * 60
# Un servidor que empieza a dar timeouts suele estar limitando: se le deja
# respirar y, si sigue, no se le toca mas en esta ejecucion. Las filas que no
# se hacen se devuelven a la cola al final, sin gastar intento (soltar()).
PAUSA_TRAS_TIMEOUT_S = 30
TIMEOUTS_PARA_SOLTAR = 3
# ocrmypdf rasteriza cada pagina a la resolucion de su imagen y, si la pagina
# tiene vectores o texto, a 400 ppp como minimo. Un plano vectorial de 225 x 85
# cm sale a 474 Mpx y tesseract se come mas de 5 GB: el runner (7 GB) muere y
# con el toda la ejecucion (27/09: tres ejecuciones seguidas tumbadas por el
# mismo plano, que la cola volvia a dar a las 6 h). Por encima de este tamano la
# pagina se rasteriza antes con ghostscript a la resolucion que quepa.
MAX_MPX_OCR = 150
MPX_UN_SOLO_PROCESO = 60               # paginas grandes: una a una, no dos a la vez
# Red de seguridad: si aun asi ocrmypdf pasa de esta fraccion de la memoria de
# la maquina, se le mata y el documento se da por fallido. Nunca el runner.
FRACCION_MEMORIA_OCR = 0.70
# 30/09: los textos largos (planes parciales, textos refundidos de 60-200
# paginas) pasaban de la memoria aun con las paginas acotadas: ocrmypdf va
# acumulando. Por encima de este numero de paginas el PDF se parte en trozos,
# cada trozo se pasa por el OCR por separado y luego se vuelven a unir. El pico
# de memoria pasa a depender del trozo, no del documento.
PAGINAS_POR_TROZO = 20

INICIO = time.time()


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


def queda() -> float:
    return PRESUPUESTO_S - (time.time() - INICIO)


# --------------------------------------------------------------------------
# TLS: contexto que admite servidores antiguos
# --------------------------------------------------------------------------
def _ctx_moderno() -> ssl.SSLContext:
    return ssl.create_default_context()


def _ctx_antiguo() -> ssl.SSLContext:
    c = ssl.create_default_context()
    # renegociacion insegura (portaldogc) y cifrados viejos; sigue verificando
    # el certificado: no se desactiva la verificacion.
    c.options |= getattr(ssl, "OP_LEGACY_SERVER_CONNECT", 0x4)
    try:
        c.set_ciphers("DEFAULT:@SECLEVEL=1")
    except ssl.SSLError:
        pass
    c.minimum_version = ssl.TLSVersion.TLSv1
    return c


CTX = [_ctx_moderno(), _ctx_antiguo()]


# --------------------------------------------------------------------------
# puerta
# --------------------------------------------------------------------------
# Esperas entre reintentos de la puerta. La base de datos de Supabase tiene
# ratos de carga (crones de paginado y troceo a la vez) en los que una consulta
# normal pasa del statement_timeout: el 26/09 la ejecucion #17 murio entera con
# "textos: canceling statement due to statement timeout" en la primera peticion.
# Es pasajero: se espera y se repite.
ESPERAS_PUERTA = (20, 60, 120)


class PuertaNoDisponible(Exception):
    pass


def puerta(cuerpo: dict, timeout: int = 120) -> dict:
    datos = json.dumps(cuerpo).encode()
    ultimo = ""
    for intento, espera in enumerate((0, *ESPERAS_PUERTA)):
        if espera:
            log(f"   puerta: {ultimo[:160]} -> reintento en {espera} s")
            time.sleep(espera)
        req = urllib.request.Request(
            PUERTA, data=datos, method="POST",
            headers={"Content-Type": "application/json", "x-trabajador-clave": CLAVE},
        )
        try:
            with urllib.request.urlopen(req, timeout=timeout, context=CTX[0]) as r:
                return json.loads(r.read().decode() or "{}")
        except urllib.error.HTTPError as e:
            ultimo = f"puerta {e.code}: {e.read().decode(errors='replace')[:500]}"
            if e.code < 500:
                # 401, 400, 404: no es carga, repetir no lo arregla
                raise RuntimeError(ultimo) from None
        except (urllib.error.URLError, ConnectionError, TimeoutError) as e:
            ultimo = f"puerta sin respuesta: {e}"
    # Las operaciones son repetibles: si "tareas" cae por timeout, la
    # transaccion se deshace y no queda nada tomado; "texto" repetido lo
    # detecta pf-ingesta-texto por el hash (sin_cambios).
    raise PuertaNoDisponible(ultimo)


# --------------------------------------------------------------------------
# robots.txt - parser propio
# urllib.robotparser cierra el grupo en la linea en blanco y deja pasar
# ficheros como el de bocyl, donde hay blancos dentro del grupo de '*'.
# --------------------------------------------------------------------------
_ROBOTS: dict[str, list[tuple[bool, str]] | None] = {}


def _robots_reglas(texto: str) -> list[tuple[bool, str]]:
    grupos: list[tuple[list[str], list[tuple[bool, str]]]] = []
    agentes: list[str] = []
    reglas: list[tuple[bool, str]] = []
    en_reglas = False
    for linea in texto.splitlines():
        linea = linea.split("#", 1)[0].strip()
        if not linea or ":" not in linea:
            continue  # los blancos NO cierran el grupo
        campo, valor = linea.split(":", 1)
        campo, valor = campo.strip().lower(), valor.strip()
        if campo == "user-agent":
            if en_reglas:
                grupos.append((agentes, reglas))
                agentes, reglas, en_reglas = [], [], False
            agentes.append(valor.lower())
        elif campo in ("allow", "disallow"):
            en_reglas = True
            if campo == "disallow" and not valor:
                continue  # "Disallow:" vacio = todo permitido
            reglas.append((campo == "allow", valor))
    if agentes:
        grupos.append((agentes, reglas))

    propio = [r for a, r in grupos if any(x != "*" and x in UA_TOKEN.lower() for x in a)]
    if propio:
        return [x for r in propio for x in r]
    return [x for a, r in grupos if "*" in a for x in r]


def _patron(p: str) -> re.Pattern:
    fin = p.endswith("$")
    if fin:
        p = p[:-1]
    rx = "".join(".*" if ch == "*" else re.escape(ch) for ch in p)
    return re.compile(rx + ("$" if fin else ""))


def robots_permite(url: str) -> tuple[bool, str]:
    u = urllib.parse.urlsplit(url)
    base = f"{u.scheme}://{u.netloc}"
    if base not in _ROBOTS:
        try:
            cuerpo, _, cod = _bajar_crudo(base + "/robots.txt", comprobar_robots=False, maximo=512 * 1024)
            _ROBOTS[base] = _robots_reglas(_decodificar(cuerpo, None)) if cod == 200 else []
        except Exception:
            _ROBOTS[base] = []  # sin robots.txt legible = sin restricciones
    reglas = _ROBOTS[base] or []
    ruta = (u.path or "/") + (("?" + u.query) if u.query else "")
    mejor: tuple[int, bool] | None = None
    for permitir, p in reglas:
        if _patron(p).match(ruta):
            largo = len(p)
            if mejor is None or largo > mejor[0] or (largo == mejor[0] and permitir):
                mejor = (largo, permitir)
    return (True if mejor is None else mejor[1]), (u.hostname or "")


# --------------------------------------------------------------------------
# descarga
# --------------------------------------------------------------------------
_ULTIMO_HOST: dict[str, float] = {}


_TIMEOUTS_SEGUIDOS: dict[str, int] = {}


class Vetado(Exception):
    pass


class HostSaturado(Exception):
    """El servidor no contesta: la tarea no se cierra; se devuelve a la cola al final."""


def _es_timeout(e: Exception) -> bool:
    return isinstance(e, TimeoutError) or "timed out" in str(e).lower()


def host_saturado(url: str) -> bool:
    return _TIMEOUTS_SEGUIDOS.get(urllib.parse.urlsplit(url).hostname or "", 0) >= TIMEOUTS_PARA_SOLTAR


def _bajar_crudo(url: str, comprobar_robots: bool = True, maximo: int = MAX_BYTES):
    if comprobar_robots:
        ok, host = robots_permite(url)
        if not ok:
            raise Vetado(f"robots.txt de {host} prohibe {urllib.parse.urlsplit(url).path}")
    host = urllib.parse.urlsplit(url).hostname or ""
    if _TIMEOUTS_SEGUIDOS.get(host, 0) >= TIMEOUTS_PARA_SOLTAR:
        raise HostSaturado(f"{host} no contesta ({TIMEOUTS_PARA_SOLTAR} timeouts seguidos)")
    espera = PAUSA_HOST_S - (time.time() - _ULTIMO_HOST.get(host, 0))
    if espera > 0:
        time.sleep(espera)
    ultimo_error: Exception | None = None
    for ctx in CTX:
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "*/*",
                                                       "Accept-Language": "es-ES,es;q=0.9"})
            with urllib.request.urlopen(req, timeout=90, context=ctx) as r:
                _ULTIMO_HOST[host] = time.time()
                datos = r.read(maximo + 1)
                if len(datos) > maximo:
                    raise RuntimeError(f"fichero mayor de {maximo // 1048576} MB")
                _TIMEOUTS_SEGUIDOS[host] = 0
                return datos, r.headers, r.status
        except urllib.error.HTTPError as e:
            _ULTIMO_HOST[host] = time.time()
            _TIMEOUTS_SEGUIDOS[host] = 0
            if e.code in (404, 410):
                raise RuntimeError(f"HTTP {e.code}: no existe") from None
            ultimo_error = RuntimeError(f"HTTP {e.code}")
            break
        except (ssl.SSLError, urllib.error.URLError, ConnectionError, TimeoutError) as e:
            ultimo_error = e
            if _es_timeout(e):
                # un timeout no es cosa del TLS: repetir con el contexto
                # antiguo solo duplica la espera y la carga del servidor.
                _TIMEOUTS_SEGUIDOS[host] = _TIMEOUTS_SEGUIDOS.get(host, 0) + 1
                _ULTIMO_HOST[host] = time.time() + PAUSA_TRAS_TIMEOUT_S
                # Un timeout es pasajero: no se cierra la fila como fallida
                # (la puerta la daria por perdida). Se retiene y se devuelve a
                # la cola al final de la ejecucion, sin gastar intento.
                raise HostSaturado(f"{host} no contesta (timeout {_TIMEOUTS_SEGUIDOS[host]})") from None
            continue  # segundo intento con TLS antiguo
    raise RuntimeError(f"no se ha podido bajar: {ultimo_error}")


def _charset_cabecera(cab) -> str | None:
    if not cab:
        return None
    m = re.search(r"charset=([\w\-]+)", cab.get("Content-Type", ""), re.I)
    return m.group(1) if m else None


def _decodificar(datos: bytes, cab) -> str:
    cs = _charset_cabecera(cab)
    if not cs:
        m = re.search(rb"<meta[^>]+charset=[\"']?([\w\-]+)", datos[:4096], re.I)
        cs = m.group(1).decode() if m else None
    if cs:
        try:
            return datos.decode(cs)
        except (LookupError, UnicodeDecodeError):
            pass
    try:
        return datos.decode("utf-8")
    except UnicodeDecodeError:
        return datos.decode("cp1252", errors="replace")  # Lexnavarra: ISO-8859-1 sin declarar


def es_pdf(datos: bytes) -> bool:
    return datos[:1024].lstrip().startswith(b"%PDF") or b"%PDF-" in datos[:1024]


# --------------------------------------------------------------------------
# HTML -> texto
# --------------------------------------------------------------------------
class _Html(html.parser.HTMLParser):
    BLOQUES = {"p", "div", "br", "li", "tr", "h1", "h2", "h3", "h4", "h5", "h6",
               "section", "article", "table", "blockquote", "dd", "dt", "pre"}
    FUERA = {"script", "style", "noscript", "nav", "header", "footer", "form", "select", "button"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.partes: list[str] = []
        self.enlaces: list[tuple[str, str]] = []
        self._fuera = 0
        self._href: str | None = None
        self._txt: list[str] = []

    def handle_starttag(self, tag, attrs):
        if tag in self.FUERA:
            self._fuera += 1
        if tag in self.BLOQUES:
            self.partes.append("\n")
        if tag == "a":
            self._href = dict(attrs).get("href")
            self._txt = []

    def handle_endtag(self, tag):
        if tag in self.FUERA and self._fuera:
            self._fuera -= 1
        if tag in self.BLOQUES:
            self.partes.append("\n")
        if tag == "a" and self._href:
            self.enlaces.append((self._href, " ".join(self._txt).strip()))
            self._href = None

    def handle_data(self, data):
        if self._href is not None:
            self._txt.append(data.strip())
        if not self._fuera:
            self.partes.append(data)


def html_a_texto(texto_html: str) -> tuple[str, list[tuple[str, str]]]:
    p = _Html()
    p.feed(texto_html)
    t = "".join(p.partes)
    t = re.sub(r"[ \t ]+", " ", t)
    t = re.sub(r"\n\s*\n\s*(\n\s*)+", "\n\n", t)
    return html.unescape(t).strip(), p.enlaces


# --------------------------------------------------------------------------
# PDF -> texto
# --------------------------------------------------------------------------
RX_ENCABEZADO = re.compile(
    r"^\s*(Art[ií]culo|ARTÍCULO|ARTICULO|Art\.|Article|Artigo|Artikulua)\s*\d", re.M)


def pdftotext(ruta: str) -> tuple[str, str]:
    """Prueba tres modos y se queda con el que reconoce mas encabezados de
    articulo (los boletines a dos columnas salen mezclados en -layout y bien
    en modo por defecto; las tablas, al reves)."""
    mejor = ("", "")
    mejor_n = -1
    for nombre, flags in (("pdftotext", []), ("pdftotext-layout", ["-layout"]), ("pdftotext-raw", ["-raw"])):
        try:
            r = subprocess.run(["pdftotext", "-enc", "UTF-8", *flags, ruta, "-"],
                               capture_output=True, timeout=600)
        except subprocess.TimeoutExpired:
            continue
        # -layout rellena con espacios hasta la columna: el Texto Refundido de
        # Torrejon salia con 24 millones de caracteres para 110.000 de texto.
        # Dos espacios bastan para separar columnas.
        t = re.sub(r"[ \t]{3,}", "  ", r.stdout.decode("utf-8", errors="replace"))
        n = len(RX_ENCABEZADO.findall(t))
        # a igualdad de encabezados manda el texto util, no la longitud con relleno
        if n > mejor_n or (n == mejor_n and texto_util(t) > texto_util(mejor[0])):
            mejor, mejor_n = (t, nombre), n
    return mejor


def texto_util(t: str) -> int:
    return len(re.sub(r"\s+", "", t))


# Palabras que aparecen en cualquier texto normativo en castellano, valenciano/
# catalan o gallego. En un texto legible son bastante mas del 15 % de las
# palabras; en una capa de texto rota, casi ninguna.
_COMUNES = set("""
de la el en que los las del por con se un una para al es lo su sus como
no sobre este esta dicho cada ser sera seran articulo art
per amb dels els les aquest aquesta serà
da do das dos na ao os as polo pola
""".split())


def ilegible(t: str) -> bool:
    """Capa de texto rota: el PDF tiene texto, pero la fuente no trae bien la
    tabla de caracteres. En el BOP de Valencia sale «)LUPDGR» donde pone
    «Firmado» (cada letra corrida 29 posiciones). pdftotext lo da por bueno y
    sin OCR la norma no se puede trocear.
    Solo se declara ilegible con texto de sobra para juzgar (300 palabras) y
    menos de un 3 % de palabras comunes: un texto legible, aunque sea una tabla
    o un anexo, no baja de ahi."""
    # Solo palabras de dos letras o mas: la basura se parte en letras sueltas
    # («d», «l», «o») que coincidirian con articulos y conjunciones.
    palabras = [w for w in re.findall(r"[a-záéíóúàèìòùüñç·]+", t.lower()) if len(w) >= 2]
    if len(palabras) < 300:
        return False
    comunes = sum(1 for w in palabras if w in _COMUNES)
    return comunes / len(palabras) < 0.03


def _error_ocr(stderr: bytes) -> str:
    """La ultima linea con nombre de excepcion, no los ultimos 300 bytes del
    traceback (que dejaban notas como «pression_bomb_check(im.size)…»)."""
    txt = stderr.decode(errors="replace")
    lineas = [l.strip() for l in txt.splitlines() if re.search(r"\b\w+(Error|Exception)\b", l)]
    return (lineas[-1] if lineas else txt.strip()[-300:])[:300]


def _paginas(ruta: str) -> list[tuple[float, float]]:
    """Tamano de cada pagina en puntos (caja de recorte, la que se ve)."""
    r = subprocess.run(["pdfinfo", "-f", "1", "-l", "100000", ruta], capture_output=True, timeout=300)
    tam = re.findall(r"^Page\s+\d+\s+size:\s+([\d.]+)\s+x\s+([\d.]+)\s+pts",
                     r.stdout.decode(errors="replace"), re.M)
    return [(float(w), float(h)) for w, h in tam]


def _ppp_imagenes(ruta: str) -> dict[int, float]:
    """Resolucion maxima de las imagenes de cada pagina (pdfimages -list)."""
    r = subprocess.run(["pdfimages", "-list", ruta], capture_output=True, timeout=300)
    ppp: dict[int, float] = {}
    for linea in r.stdout.decode(errors="replace").splitlines()[2:]:
        c = linea.split()
        # page num type width height color comp bpc enc interp object ID x-ppi y-ppi size ratio
        if len(c) >= 14 and c[0].isdigit():
            try:
                ppp[int(c[0])] = max(ppp.get(int(c[0]), 0.0), float(c[12]), float(c[13]))
            except ValueError:
                pass
    return ppp


def _mpx(w: float, h: float, ppp: float) -> float:
    return (w / 72 * ppp) * (h / 72 * ppp) / 1e6


def _paginas_con_texto(ruta: str) -> set[int]:
    """Paginas que ya traen capa de texto: con --skip-text ocrmypdf no las
    rasteriza, asi que no cuentan (y no hay que tocarlas: perderian el texto)."""
    try:
        r = subprocess.run(["pdftotext", "-enc", "UTF-8", ruta, "-"], capture_output=True, timeout=600)
    except subprocess.TimeoutExpired:
        return set()
    trozos = r.stdout.decode("utf-8", errors="replace").split("\f")
    return {n for n, t in enumerate(trozos, start=1) if t.strip()}


def acotar_paginas(entrada: str, salida: str, forzar: bool = False) -> tuple[str, float, str]:
    """Rasteriza con ghostscript las paginas que ocrmypdf pondria por encima de
    MAX_MPX_OCR, a la resolucion que cabe, y deja el resto como esta.
    Devuelve (ruta a usar, Mpx de la pagina mas grande que vera ocrmypdf, nota).
    La estimacion es la de ocrmypdf: la resolucion maxima de las imagenes de la
    pagina (un logotipo a 1.858 ppp arrastra la pagina entera a esa resolucion)
    y, como minimo, 400 ppp (su VECTOR_PAGE_DPI); se toma siempre el minimo de
    400 para quedar del lado seguro. Con --skip-text las paginas que ya tienen
    texto no se rasterizan, asi que no cuentan."""
    paginas = _paginas(entrada)
    if not paginas:
        return entrada, 0.0, ""
    con_texto = set() if forzar else _paginas_con_texto(entrada)
    ppp_img = _ppp_imagenes(entrada)
    grandes: dict[int, int] = {}
    mayor = 0.0
    for n, (w, h) in enumerate(paginas, start=1):
        if n in con_texto:
            continue
        mpx = _mpx(w, h, max(400.0, ppp_img.get(n, 0.0)))
        if mpx > MAX_MPX_OCR:
            # la resolucion que deja la pagina en MAX_MPX_OCR (72 ppp como suelo:
            # por debajo no se lee nada y un plano de 5 m no cabe de otra forma)
            ppp = max(72, int((MAX_MPX_OCR * 1e6 / ((w / 72) * (h / 72))) ** 0.5))
            grandes[n] = ppp
            mpx = _mpx(w, h, ppp)
        mayor = max(mayor, mpx)
    if not grandes:
        return entrada, mayor, ""

    d = os.path.dirname(salida)
    trozos: dict[int, str] = {}
    for n, ppp in grandes.items():
        t = os.path.join(d, f"pagina-{n}.pdf")
        r = subprocess.run(["gs", "-q", "-dNOPAUSE", "-dBATCH", "-dSAFER", "-dUseCropBox",
                            "-sDEVICE=pdfimage24", f"-r{ppp}", f"-dFirstPage={n}", f"-dLastPage={n}",
                            "-sOutputFile=" + t, entrada],
                           capture_output=True, timeout=1800)
        if r.returncode != 0 or not os.path.exists(t):
            raise RuntimeError(f"ghostscript no ha podido rasterizar la pagina {n}: "
                               + r.stderr.decode(errors="replace").strip()[-200:])
        trozos[n] = t
    # se recompone el documento: las paginas normales salen del original
    args: list[str] = []
    for n in range(1, len(paginas) + 1):
        if n in trozos:
            args += [trozos[n], "1"]
        else:
            args += [entrada, str(n)]
    r = subprocess.run(["qpdf", "--empty", "--pages", *args, "--", salida], capture_output=True, timeout=600)
    if r.returncode not in (0, 3) or not os.path.exists(salida):
        raise RuntimeError("qpdf no ha podido recomponer el documento: "
                           + r.stderr.decode(errors="replace").strip()[-200:])
    resumen = ", ".join(f"p{n} a {p} ppp" for n, p in list(grandes.items())[:5])
    if len(grandes) > 5:
        resumen += f" y {len(grandes) - 5} mas"
    return salida, mayor, f"paginas de gran formato rasterizadas ({resumen})"


def _memoria_total() -> int:
    try:
        with open("/proc/meminfo") as fh:
            for linea in fh:
                if linea.startswith("MemTotal:"):
                    return int(linea.split()[1]) * 1024
    except OSError:
        pass
    return 7 * 1024 ** 3  # runner estandar de GitHub


def _rss_grupo(pgid: int) -> int:
    """Memoria residente de todos los procesos del grupo (ocrmypdf lanza
    tesseract, gs y sus propios procesos hijos)."""
    total = 0
    for pid in os.listdir("/proc"):
        if not pid.isdigit():
            continue
        try:
            with open(f"/proc/{pid}/stat") as fh:
                campos = fh.read().rsplit(")", 1)[1].split()
            # tras el nombre: estado(0) ppid(1) pgrp(2) ... rss(21), en paginas
            if int(campos[2]) == pgid:
                total += int(campos[21]) * os.sysconf("SC_PAGE_SIZE")
        except (OSError, IndexError, ValueError):
            continue
    return total


def ejecutar_vigilado(cmd: list[str], timeout: int) -> tuple[int, bytes]:
    """Como subprocess.run, pero en su propio grupo de procesos y con techo de
    memoria: si el grupo pasa de FRACCION_MEMORIA_OCR de la maquina, se mata el
    grupo entero y se lanza un error normal. El OOM killer del sistema, en
    cambio, se lleva por delante el runner y la ejecucion completa."""
    techo = int(_memoria_total() * FRACCION_MEMORIA_OCR)
    with tempfile.TemporaryFile() as err:
        proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=err, start_new_session=True)
        limite = time.time() + timeout
        pico = 0
        motivo = ""
        try:
            while proc.poll() is None:
                time.sleep(2)
                rss = _rss_grupo(proc.pid)
                pico = max(pico, rss)
                if rss > techo:
                    motivo = (f"memoria agotada: {rss / 1024 ** 3:.1f} GB de {techo / 1024 ** 3:.1f} GB "
                              "permitidos (MemoryError)")
                elif time.time() > limite:
                    motivo = f"mas de {timeout // 60} min (TimeoutExpired)"
                if motivo:
                    raise RuntimeError(f"{cmd[0]}: {motivo}")
        except BaseException:
            # tambien si GitHub corta la ejecucion (SystemExit de _cortar):
            # el grupo de ocrmypdf no se queda huerfano comiendo memoria.
            try:
                os.killpg(proc.pid, 9)
            except ProcessLookupError:
                pass
            proc.wait()
            raise
        err.seek(0)
        return proc.returncode, err.read()


def _ocr_trozo(plano: str, salida: str, forzar: bool) -> tuple[int, str]:
    """Acota las paginas de gran formato y pasa ocrmypdf, vigilado.
    Devuelve (codigo de ocrmypdf, nota del acotado)."""
    plano, mayor, nota_acotar = acotar_paginas(plano, plano + ".acotado.pdf", forzar)
    trabajos = 1 if mayor > MPX_UN_SOLO_PROCESO else (os.cpu_count() or 2)
    codigo, err = ejecutar_vigilado(
        ["ocrmypdf", "-l", "spa", "--force-ocr" if forzar else "--skip-text", "--optimize", "0", "--output-type", "pdf",
         "--invalidate-digital-signatures", "--max-image-mpixels", "2000",
         "--jobs", str(trabajos), plano, salida],
        timeout=OCR_TIMEOUT_S)
    if codigo not in (0, 6) or not os.path.exists(salida):
        raise RuntimeError("ocrmypdf: " + _error_ocr(err))
    return codigo, nota_acotar


def _qpdf_paginas(args: list[str], salida: str, que: str):
    r = subprocess.run(["qpdf", "--empty", "--pages", *args, "--", salida], capture_output=True, timeout=900)
    if r.returncode not in (0, 3) or not os.path.exists(salida):
        raise RuntimeError(f"qpdf no ha podido {que}: " + r.stderr.decode(errors="replace").strip()[-200:])


def dar_capa_texto(entrada: str, salida: str, forzar: bool = False) -> str:
    """Prepara el PDF con qpdf y le da capa de texto con ocrmypdf.

    - --decrypt: muchos PDFs municipales llevan cifrado de propietario (sin
      contrasena de apertura) y ocrmypdf los rechaza (EncryptedPdfError).
    - --flatten-rotation: las paginas escaneadas vienen con /Rotate 180 y sin
      aplanar la capa de texto sale girada respecto a la imagen.
    - --invalidate-digital-signatures: los firmados con @firma
      (DigitalSignatureError). Solo se invalida la firma de NUESTRA copia
      (fuente-externo.pdf); el original sigue intacto y enlazado.
    - --max-image-mpixels: los planos escaneados pasan del limite de Pillow
      (DecompressionBombError); son documentos oficiales, no una bomba.
    - forzar: solo cuando la capa de texto existente es ilegible (ver
      ilegible()). --skip-text dejaria esas paginas como estan; --force-ocr
      las rasteriza y las lee otra vez. En el resto no cambia nada.
    - paginas de gran formato: ver acotar_paginas(). Y ocrmypdf corre
      vigilado (ejecutar_vigilado): un documento que se come la memoria
      falla el solo, no la ejecucion.
    - 30/09, documentos largos: por encima de PAGINAS_POR_TROZO paginas se
      parten en trozos, cada trozo va al OCR por separado y se vuelven a unir.
    """
    plano = entrada + ".plano.pdf"
    r = subprocess.run(["qpdf", "--decrypt", "--flatten-rotation", entrada, plano],
                       capture_output=True, timeout=600)
    if r.returncode not in (0, 3) or not os.path.exists(plano):  # 3 = avisos
        shutil.copy(entrada, plano)

    n = len(_paginas(plano))
    if n <= PAGINAS_POR_TROZO:
        codigo, nota_acotar = _ocr_trozo(plano, salida, forzar)
        trozos_nota = ""
    else:
        d = os.path.dirname(salida)
        hechos: list[str] = []
        codigos: set[int] = set()
        acotados: list[str] = []
        for i, desde in enumerate(range(1, n + 1, PAGINAS_POR_TROZO), start=1):
            hasta = min(desde + PAGINAS_POR_TROZO - 1, n)
            trozo = os.path.join(d, f"trozo-{i}.pdf")
            _qpdf_paginas([plano, f"{desde}-{hasta}"], trozo, f"separar las paginas {desde}-{hasta}")
            ocr = os.path.join(d, f"trozo-{i}-ocr.pdf")
            try:
                c, na = _ocr_trozo(trozo, ocr, forzar)
            except RuntimeError as e:
                raise RuntimeError(f"paginas {desde}-{hasta}: {e}") from None
            codigos.add(c)
            if na:
                acotados.append(f"p{desde}-{hasta}: {na}")
            os.remove(trozo)
            hechos.append(ocr)
            log(f"   trozo {i}: paginas {desde}-{hasta} hechas")
        args: list[str] = []
        for h in hechos:
            args += [h, "1-z"]
        _qpdf_paginas(args, salida, "unir los trozos")
        for h in hechos:
            os.remove(h)
        codigo = 0 if 0 in codigos else 6
        nota_acotar = "; ".join(acotados)[:300]
        trozos_nota = f"en {len(hechos)} trozos de {PAGINAS_POR_TROZO} paginas"

    if forzar:
        nota = "ocr forzado (capa de texto ilegible)"
    else:
        nota = "ocr" if codigo == 0 else "ya tenia texto"
    for extra in (trozos_nota, nota_acotar):
        if extra:
            nota += "; " + extra
    return nota


def ajustar_tamano(ruta: str, d: str) -> tuple[str, str]:
    """El bucket admite 50 MB. Si la copia pasa, se recomprime la imagen con
    ghostscript (la capa de texto se conserva). Devuelve la ruta final y una
    nota."""
    if os.path.getsize(ruta) <= MAX_SUBIDA:
        return ruta, ""
    for ajuste in ("/ebook", "/screen"):
        salida = os.path.join(d, "reducido" + ajuste.strip("/") + ".pdf")
        r = subprocess.run(["gs", "-q", "-dNOPAUSE", "-dBATCH", "-dSAFER", "-sDEVICE=pdfwrite",
                            "-dPDFSETTINGS=" + ajuste, "-sOutputFile=" + salida, ruta],
                           capture_output=True, timeout=1800)
        if r.returncode == 0 and os.path.exists(salida) and os.path.getsize(salida) <= MAX_SUBIDA:
            return salida, f"recomprimido {ajuste}"
    raise RuntimeError(f"la copia pesa {os.path.getsize(ruta) // 1048576} MB incluso recomprimida y el bucket admite 50 MB")


def texto_de_pdf(datos: bytes) -> tuple[str, str]:
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, "doc.pdf")
        with open(f, "wb") as fh:
            fh.write(datos)
        t, modo = pdftotext(f)
        roto = texto_util(t) >= 2000 and ilegible(t)
        if texto_util(t) >= 2000 and not roto:
            return t, modo
        o = os.path.join(d, "ocr.pdf")
        if roto:
            # capa de texto rota: se lee la imagen y se descarta la capa
            log("   capa de texto ilegible, OCR forzado…")
            dar_capa_texto(f, o, forzar=True)
            t2, modo2 = pdftotext(o)
            if not ilegible(t2):
                return t2, modo2 + "+ocr forzado"
            return t, modo
        # sin capa de texto (o casi): OCR
        log("   sin capa de texto, OCR…")
        dar_capa_texto(f, o)
        t2, modo2 = pdftotext(o)
        if texto_util(t2) > texto_util(t):
            return t2, modo2 + "+ocr"
        return t, modo


# --------------------------------------------------------------------------
# resolutores por via
# --------------------------------------------------------------------------
def _absoluta(base: str, href: str) -> str:
    return urllib.parse.urljoin(base, html.unescape(href.strip()))


def _pdfs_enlazados(base: str, enlaces: list[tuple[str, str]]) -> list[str]:
    """Los PDFs enlazados desde una ficha, ordenados: primero el castellano,
    el consolidado y el propio boletin."""
    vistos, cand = set(), []
    for href, txt in enlaces:
        if not href or href.startswith(("mailto:", "javascript:", "#")):
            continue
        u = _absoluta(base, href)
        low = (u + " " + txt).lower()
        if not (".pdf" in low or "pdf" in txt.lower() or "descargar" in low or "blob" in low):
            continue
        if u in vistos:
            continue
        vistos.add(u)
        p = 0
        if re.search(r"(_es|/es/|lang=es|castellano|español|espanol|\bes\b)", low):
            p -= 3
        if re.search(r"(_gl|/gl/|galego|_eu|/eu/|euskara|valencià|_va\b|/ca/|català)", low):
            p += 3
        if "consolid" in low:
            p -= 2
        if "dog" in low or "boletin" in low or "boe" in low:
            p -= 1
        cand.append((p, len(cand), u))
    return [u for _, _, u in sorted(cand)]


def resolver(url: str, via: str, profundidad: int = 0, robots: bool = True) -> tuple[str, str]:
    """Devuelve (texto, formato). Sigue como mucho un salto: de la ficha al PDF.

    robots=False solo para lo aportado a mano (06/10): un enlace que pega una
    persona, o un documento que Jose deja guardado, no lo trae un robot, y se
    baja aunque el robots.txt del portal lo prohiba (criterio de Jose, 29/09).
    """
    datos, cab, _ = _bajar_crudo(url, comprobar_robots=robots)
    if es_pdf(datos):
        return texto_de_pdf(datos)

    pagina = _decodificar(datos, cab)
    texto, enlaces = html_a_texto(pagina)

    # Lexnavarra: el buscador devuelve una lista; la ficha lleva el numero.
    if via == "lexnavarra" and profundidad == 0 and len(RX_ENCABEZADO.findall(texto)) < 3:
        for href, _ in enlaces:
            if re.search(r"(ficha|detalle|Legislacion.*\d)", href, re.I):
                try:
                    return resolver(_absoluta(url, href), via, profundidad + 1, robots)
                except Vetado:
                    raise
                except Exception as e:
                    log("   ficha lexnavarra:", e)
                break

    suficiente = len(RX_ENCABEZADO.findall(texto)) >= 3 and texto_util(texto) >= 3000
    if suficiente or profundidad > 0:
        return texto, "html"

    # ficha sin articulado: seguir el PDF enlazado (lex.gal -> DOG en castellano
    # o consolidado; BOC Cantabria; repositorio del IEA -> consolidado /f/;
    # boletines con visor)
    for pdf in _pdfs_enlazados(url, enlaces)[:4]:
        try:
            t, modo = resolver(pdf, via, profundidad + 1, robots)
            if texto_util(t) > texto_util(texto):
                return t, modo + " (enlazado)"
        except Vetado:
            raise
        except Exception as e:
            log("   enlace", pdf[:120], "->", e)
    return texto, "html"


# --------------------------------------------------------------------------
# seguir donde se dejo
# --------------------------------------------------------------------------
# Lo tomado y no hecho se devuelve a la cola al acabar -por presupuesto, por un
# servidor que no contesta o porque GitHub corta la ejecucion (cancelada,
# tiempo agotado)- sin gastar intento: la siguiente ejecucion sigue donde lo
# dejo esta. Si ni eso se puede avisar (runner muerto de golpe), la base lo
# devuelve sola a las 3 h, tambien sin gastar intento.
EN_MANO: dict[str, set] = {"textos": set(), "pdfs": set()}
RETENIDAS: dict[str, set] = {"textos": set(), "pdfs": set()}


def soltar(motivo: str):
    textos = sorted(EN_MANO["textos"] | RETENIDAS["textos"])
    pdfs = sorted(EN_MANO["pdfs"] | RETENIDAS["pdfs"])
    if not textos and not pdfs:
        return
    # Una sola peticion y corta: tras la senal de cancelar GitHub da unos 10 s
    # antes de matar el proceso. No se usa puerta(), que reintenta con esperas.
    datos = json.dumps({"modo": "soltar", "textos": textos, "pdfs": pdfs, "motivo": motivo}).encode()
    req = urllib.request.Request(PUERTA, data=datos, method="POST",
                                 headers={"Content-Type": "application/json", "x-trabajador-clave": CLAVE})
    try:
        with urllib.request.urlopen(req, timeout=6, context=CTX[0]) as r:
            log("soltadas:", r.read().decode(errors="replace")[:200])
        for k in ("textos", "pdfs"):
            EN_MANO[k].clear()
            RETENIDAS[k].clear()
    except Exception as e:
        log(f"no se han podido soltar {len(textos)} textos y {len(pdfs)} pdfs "
            f"(volveran solas a las 3 h, sin gastar intento): {str(e)[:160]}")


def _cortar(signum, _frame):
    # GitHub manda SIGINT y luego SIGTERM al cancelar: se sale por el finally de
    # trabajar(), que devuelve lo que quede en mano.
    raise SystemExit(f"senal {signum}: GitHub corta la ejecucion")


# --------------------------------------------------------------------------
# tareas
# --------------------------------------------------------------------------
def hacer_texto(t: dict):
    url, via = t.get("url"), t.get("via") or "?"
    a_mano = bool(t.get("a_mano"))
    log(f"texto {t['id']} [{via}]{' [aportado a mano: sin robots.txt]' if a_mano else ''} {url}")
    try:
        texto, formato = resolver(url, via, robots=not a_mano)
        texto = texto.replace("\x00", "")
        if texto_util(texto) < MIN_TEXTO:
            res = puerta({"modo": "texto", "id": t["id"],
                          "error": f"texto vacio o demasiado corto ({texto_util(texto)} chars, {formato})"})
        else:
            res = puerta({"modo": "texto", "id": t["id"], "texto": texto, "formato": formato}, timeout=300)
    except HostSaturado as e:
        log("   se retiene y se devuelve al final:", e)
        RETENIDAS["textos"].add(t["id"])
        return
    except Vetado as e:
        res = puerta({"modo": "texto", "id": t["id"], "error": str(e)})
    except Exception as e:
        res = puerta({"modo": "texto", "id": t["id"], "error": str(e)[:300]})
    log("   ->", json.dumps(res, ensure_ascii=False)[:300])


def hacer_pdf(p: dict):
    log(f"pdf {p['documento_id']} ({p.get('motivo') or ''})")
    try:
        # el PDF viene de nuestro propio Storage o de la url oficial ya
        # registrada: si es de fuera, se respeta robots igualmente.
        propio = "supabase.co/storage/" in p["descarga"]
        datos, _, _ = _bajar_crudo(p["descarga"], comprobar_robots=not propio)
        if not es_pdf(datos):
            raise RuntimeError("la descarga no es un PDF")
        with tempfile.TemporaryDirectory() as d:
            f, o = os.path.join(d, "in.pdf"), os.path.join(d, "out.pdf")
            with open(f, "wb") as fh:
                fh.write(datos)
            if p.get("solo_comprimir"):
                # 30/09: normas cuyo PDF pasa de 50 MB y que ya tienen su texto
                # en la base (PGOU con los planos dentro). Solo hace falta
                # nuestra copia: se comprime con ghostscript, SIN OCR (el OCR
                # de esas paginas de plano solo daba errores de memoria).
                final, reduccion = ajustar_tamano(f, d)
                nota = "solo compresion, sin OCR" + ("; " + reduccion if reduccion else "")
                t, modo = pdftotext(final)
            else:
                previo, _ = pdftotext(f)
                nota = dar_capa_texto(f, o, forzar=texto_util(previo) >= 2000 and ilegible(previo))
                t, modo = pdftotext(o)
                if texto_util(t) < 200:
                    raise RuntimeError("tras el OCR sigue sin texto legible")
                final, reduccion = ajustar_tamano(o, d)
                if reduccion:
                    nota += "; " + reduccion
            with open(final, "rb") as fh:
                cuerpo = fh.read()
        req = urllib.request.Request(p["subida"], data=cuerpo, method="PUT",
                                     headers={"Content-Type": "application/pdf", "x-upsert": "true"})
        try:
            with urllib.request.urlopen(req, timeout=600, context=CTX[0]) as r:
                r.read()
        except urllib.error.HTTPError as e:
            # el motivo esta en el cuerpo (tamano, token caducado...), no en el codigo
            raise RuntimeError(f"subida {e.code}: {e.read().decode(errors='replace')[:200]}") from None
        nota = f"{nota}; {len(datos) // 1024} KB -> {len(cuerpo) // 1024} KB; {texto_util(t)} chars ({modo})"
        res = puerta({"modo": "pdf", "documento_id": p["documento_id"], "ruta": p["ruta"], "nota": nota})
    except HostSaturado as e:
        log("   se retiene y se devuelve al final:", e)
        RETENIDAS["pdfs"].add(p["documento_id"])
        return
    except Exception as e:
        res = puerta({"modo": "pdf", "documento_id": p["documento_id"], "error": str(e)[:300]})
    log("   ->", json.dumps(res, ensure_ascii=False)[:300])


def hacer_ficha(f: dict):
    """06/10: fichas de sedes que cortan a la IP de Supabase (Murcia). Es
    rastreo automatico: se respeta robots.txt y la pausa por servidor. Solo se
    baja el HTML; lo lee pf-catalogo-supra con su lector de siempre."""
    url = f["url"]
    log(f"ficha {url}")
    try:
        datos, cab, _ = _bajar_crudo(url, comprobar_robots=True, maximo=4 * 1024 * 1024)
        tipo = (cab.get("Content-Type") or "") if cab else ""
        if tipo and not re.search(r"html|xml", tipo, re.I):
            raise RuntimeError(f"no es una pagina: {tipo[:60]}")
        pagina = _decodificar(datos, cab)
        res = puerta({"modo": "ficha_html", "url": url, "html": pagina, "final_url": url})
    except HostSaturado as e:
        # la puerta la vuelve a dar a las 3 h; no hace falta soltarla
        log("   sede saturada, se deja:", e)
        return
    except Vetado as e:
        res = puerta({"modo": "ficha_html", "url": url, "error": "robots: " + str(e)[:250]})
    except Exception as e:
        res = puerta({"modo": "ficha_html", "url": url, "error": str(e)[:300]})
    log("   ->", json.dumps(res, ensure_ascii=False)[:200])


def contar():
    try:
        r = puerta({"modo": "contar"})
    except PuertaNoDisponible as e:
        # sin respuesta no se arranca: la siguiente ejecucion lo vuelve a mirar
        print(f"::warning::la puerta no responde, se deja para la proxima ejecucion ({str(e)[:200]})")
        r = {"hay": False}
    log("contar:", r)
    # Cada carril (textos / pdfs) solo arranca si hay trabajo de lo suyo.
    quiere_textos = int(os.environ.get("MAX_TEXTOS", "10")) > 0
    quiere_pdfs = int(os.environ.get("MAX_PDFS", "2")) > 0
    # Las fichas de sede (HTML ligero) van con el carril de textos.
    hay = bool((quiere_textos and (r.get("textos") or r.get("fichas_html")))
               or (quiere_pdfs and r.get("pdfs")))
    salida = os.environ.get("GITHUB_OUTPUT")
    if salida:
        with open(salida, "a") as fh:
            fh.write(f"hay={'true' if hay else 'false'}\n")


def trabajar():
    signal.signal(signal.SIGTERM, _cortar)
    signal.signal(signal.SIGINT, _cortar)
    ronda = 0
    motivo = "fin de la ejecucion"
    try:
        while queda() > 20 * 60:  # sin margen para un OCR largo no se toma nada mas
            ronda += 1
            try:
                # "admite": lo que sabe hacer esta version. La puerta no le da
                # tareas «solo comprimir» a un trabajador que no las conoce
                # (les pasaria el OCR, que es justo lo que hay que evitar), ni
                # reintentos por trozos a uno que no sabe trocear.
                r = puerta({"modo": "tareas",
                            "max_textos": int(os.environ.get("MAX_TEXTOS", "10")),
                            "max_pdfs": int(os.environ.get("MAX_PDFS", "2")),
                            # fichas de sede: solo el carril de textos
                            "max_fichas": int(os.environ.get("MAX_FICHAS", "40"))
                                          if int(os.environ.get("MAX_TEXTOS", "10")) > 0 else 0,
                            "admite": ["solo_comprimir", "trocear", "fichas", "sin_robots"]})
            except PuertaNoDisponible as e:
                # Lo ya hecho esta devuelto; lo que no se ha tomado sigue en la cola.
                print(f"::warning::la puerta no responde, se para aqui ({str(e)[:200]})")
                break
            textos, pdfs = r.get("textos") or [], r.get("pdfs") or []
            fichas = r.get("fichas_html") or []
            log(f"ronda {ronda}: {len(textos)} textos, {len(pdfs)} pdfs, {len(fichas)} fichas")
            if not textos and not pdfs and not fichas:
                break
            EN_MANO["textos"].update(t["id"] for t in textos)
            EN_MANO["pdfs"].update(p["documento_id"] for p in pdfs)
            # Ninguna tarea puede tumbar la ejecucion: cualquier error (un 401 de
            # la puerta al devolver el fallo, un fallo no previsto) se anota y se
            # sigue con la siguiente.
            for t in textos:
                try:
                    hacer_texto(t)
                except PuertaNoDisponible as e:
                    log("   no se ha podido devolver:", str(e)[:200])
                except Exception as e:
                    print(f"::warning::texto {t.get('id')}: {type(e).__name__}: {str(e)[:200]}", flush=True)
                EN_MANO["textos"].discard(t["id"])
            for f in fichas:
                if queda() < 15 * 60:
                    break  # las no bajadas vuelven solas a las 3 h
                try:
                    hacer_ficha(f)
                except PuertaNoDisponible as e:
                    log("   no se ha podido devolver:", str(e)[:200])
                except Exception as e:
                    print(f"::warning::ficha {f.get('url')}: {type(e).__name__}: {str(e)[:200]}", flush=True)
            for p in pdfs:
                try:
                    hacer_pdf(p)
                except PuertaNoDisponible as e:
                    log("   no se ha podido devolver:", str(e)[:200])
                except Exception as e:
                    print(f"::warning::pdf {p.get('documento_id')}: {type(e).__name__}: {str(e)[:200]}", flush=True)
                EN_MANO["pdfs"].discard(p["documento_id"])
    except SystemExit as e:
        motivo = str(e)
        print(f"::warning::{motivo}; se devuelve a la cola lo que quedaba en mano", flush=True)
        raise
    finally:
        soltar(motivo)
        log(f"fin: {ronda} rondas, {int(time.time() - INICIO)} s")


if __name__ == "__main__":
    if not CLAVE:
        sys.exit("falta TRABAJADOR_CLAVE")
    orden = sys.argv[1] if len(sys.argv) > 1 else "trabajar"
    {"contar": contar, "trabajar": trabajar}[orden]()
