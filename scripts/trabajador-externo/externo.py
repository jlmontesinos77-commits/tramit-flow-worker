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
import http.cookiejar
import faulthandler
import json
import os
import re
import shutil
import signal
import socket
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
    "https://iqskiegwxucfuimnnoiu.supabase.co/functions/v1/pf-trabajador-externo",
)
# 17/10: hojas y recompresion van por su propia puerta (misma clave).
PUERTA_HOJAS = os.environ.get(
    "TRAMITFLOW_PUERTA_HOJAS",
    "https://iqskiegwxucfuimnnoiu.supabase.co/functions/v1/pf-trabajador-hojas",
)
CLAVE = os.environ.get("TRABAJADOR_CLAVE", "")
UA_TOKEN = "TramitFlow"
UA = "Mozilla/5.0 (compatible; TramitFlow-externo/1.0; +https://kolven.es)"

MAX_BYTES = 300 * 1024 * 1024          # planes generales escaneados: el de Lugo pesa 198 MB
MAX_SUBIDA = 49 * 1024 * 1024          # copias con capa de texto: se comprimen si pasan de esto
# 17/10: el bucket 'normas' admite 200 MB (el limite global de Storage). Las copias que sube el PC de Jose de los hosts
# que solo le dejan entrar a el pueden llegar hasta ahi; se borran en cuanto se leen.
MAX_COPIA_LOCAL = 199 * 1024 * 1024
MIN_TEXTO = 500                         # por debajo, la puerta la cierra como fallida
PRESUPUESTO_S = int(os.environ.get("PRESUPUESTO_MIN", "150")) * 60
PAUSA_HOST_S = 4.0                      # cortesia con cada servidor (07/10: de 1,5 a 4 s)
# 07/10: espaciar. Una ejecucion ya no trabaja sin parar hasta agotar el
# presupuesto: hace como mucho MAX_RONDAS tandas, con una pausa entre una y
# otra. Junto con el tope de 2 documentos por servidor en cada toma (puerta),
# no se satura ni la base ni ningun portal.
MAX_RONDAS = int(os.environ.get("MAX_RONDAS", "4"))
PAUSA_RONDA_S = int(os.environ.get("PAUSA_RONDA_S", "120"))
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

# 06/10: SESION DE NAVEGACION. Hay portales oficiales que solo entregan el
# documento a quien llega con la cookie de sesion de haberlos visitado: el
# registro de planeamiento de la Junta de Andalucia (SITUA) contesta a
# descargaDocumentos.jsf?doc=N con su pagina HTML si no hay sesion, y con el PDF
# si la hay. Las descargas comparten un tarro de cookies durante la ejecucion
# (como un navegador) y, si un documento llega como pagina, se pide la sesion
# visitando su carpeta y la portada y se repite una vez (bajar_documento).
COOKIES = http.cookiejar.CookieJar()


def _abridores(ctxs) -> list:
    return [urllib.request.build_opener(urllib.request.HTTPSHandler(context=c),
                                        urllib.request.HTTPCookieProcessor(COOKIES)) for c in ctxs]


ABRIDORES = _abridores(CTX)

# 06/10: CADENA DE CERTIFICADOS INCOMPLETA. Hay servidores municipales que no
# mandan el certificado intermedio (ponferrada.org: 31 documentos fallaron con
# «unable to get local issuer certificate»). El navegador lo completa solo: lee
# en el certificado del servidor de donde bajar el intermedio (AIA, «CA
# Issuers») y lo baja. Aqui se hace lo mismo, una vez por host: se baja el
# intermedio (y el siguiente, si hace falta) y se anade a la verificacion. La
# verificacion NO se desactiva: el intermedio tiene que encadenar con una raiz
# de confianza del sistema o la conexion sigue fallando.
_ABRIDORES_HOST: dict[str, list] = {}
_AIA_PROBADO: set[str] = set()


def _aia_url(cert) -> str | None:
    from cryptography import x509
    from cryptography.x509.oid import AuthorityInformationAccessOID, ExtensionOID
    try:
        aia = cert.extensions.get_extension_for_oid(ExtensionOID.AUTHORITY_INFORMATION_ACCESS).value
    except x509.ExtensionNotFound:
        return None
    for d in aia:
        if d.access_method == AuthorityInformationAccessOID.CA_ISSUERS:
            v = d.access_location.value
            if v.lower().startswith(("http://", "https://")):
                return v
    return None


def completar_cadena(host: str, puerto: int = 443) -> bool:
    """Baja los intermedios que el servidor no manda y prepara abridores
    propios para ese host. True si se ha conseguido algun intermedio."""
    if host in _AIA_PROBADO:
        return host in _ABRIDORES_HOST
    _AIA_PROBADO.add(host)
    try:
        from cryptography import x509
        from cryptography.hazmat.primitives.serialization import Encoding
    except ImportError:
        log("   cadena incompleta en", host, "y falta python3-cryptography para completarla")
        return False
    try:
        actual = x509.load_pem_x509_certificate(ssl.get_server_certificate((host, puerto), timeout=30).encode())
    except Exception as e:
        log("   cadena incompleta en", host, "; no se pudo leer su certificado:", e)
        return False
    pems: list[str] = []
    for _ in range(3):
        if actual.issuer == actual.subject:
            break
        u = _aia_url(actual)
        if not u:
            break
        try:
            with urllib.request.urlopen(urllib.request.Request(u, headers={"User-Agent": UA}),
                                        timeout=30, context=CTX[0]) as r:
                cuerpo = r.read(512 * 1024)
            siguiente = (x509.load_pem_x509_certificate(cuerpo) if b"-----BEGIN" in cuerpo
                         else x509.load_der_x509_certificate(cuerpo))
        except Exception as e:
            log("   intermedio de", host, "en", u, "->", e)
            break
        pems.append(siguiente.public_bytes(Encoding.PEM).decode())
        actual = siguiente
    if not pems:
        return False
    ctxs = []
    for base in (_ctx_moderno(), _ctx_antiguo()):
        base.load_verify_locations(cadata="".join(pems))
        ctxs.append(base)
    _ABRIDORES_HOST[host] = _abridores(ctxs)
    log(f"   {host}: cadena completada con {len(pems)} intermedio(s) bajados del propio certificado")
    return True


def _es_cadena_incompleta(e: Exception) -> bool:
    t = str(e)
    return "CERTIFICATE_VERIFY_FAILED" in t and ("local issuer" in t or "issuer certificate" in t)


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


def puerta(cuerpo: dict, timeout: int = 120, destino: str | None = None) -> dict:
    datos = json.dumps(cuerpo).encode()
    ultimo = ""
    for intento, espera in enumerate((0, *ESPERAS_PUERTA)):
        if espera:
            log(f"   puerta: {ultimo[:160]} -> reintento en {espera} s")
            time.sleep(espera)
        req = urllib.request.Request(
            destino or PUERTA, data=datos, method="POST",
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
    intentos = list(_ABRIDORES_HOST.get(host) or ABRIDORES)
    completada = False
    while intentos:
        abridor = intentos.pop(0)
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "*/*",
                                                       "Accept-Language": "es-ES,es;q=0.9"})
            with abridor.open(req, timeout=90) as r:
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
            if not completada and _es_cadena_incompleta(e) and completar_cadena(host):
                completada = True
                intentos = list(_ABRIDORES_HOST[host])
                continue
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


_CON_SESION: dict[str, int] = {}     # aperturas de sesion por host en esta ejecucion
_SESION_OK: dict[str, bool] = {}       # la ultima apertura trajo el documento
MAX_APERTURAS_SESION = 6


def _rutas_de_sesion(url: str) -> tuple[str, list[str]]:
    u = urllib.parse.urlsplit(url)
    origen = f"{u.scheme}://{u.netloc}"
    trozos = [x for x in u.path.split("/") if x]
    rutas = ["/" + "/".join(trozos[:-1]) + "/" if len(trozos) > 1 else "/",
             "/" + trozos[0] + "/" if trozos else "/", "/"]
    return origen, list(dict.fromkeys(rutas))


def calentar_y_repetir(url: str, robots: bool, maximo: int):
    """Portales que solo sirven el documento a una sesion abierta en la
    aplicacion (SITUA de la Junta de Andalucia, visores JSF): visita la carpeta
    del documento, la primera carpeta del sitio y la portada, y DESPUES DE CADA
    UNA vuelve a pedir el documento. Se para en cuanto llega un PDF o un Word.

    06/10: antes se decidia por "ha llegado una cookie nueva", y eso fallaba
    justo en SITUA: el primer intento sin sesion ya rebota a una pagina de
    error que pone JSESSIONID, asi que la visita a /situadifusion/ (que abre la
    aplicacion y deja la sesion valida) no anadia cookie, no se repetia la
    descarga y el documento quedaba como "texto vacio". Lo que dice si la
    sesion vale es el documento, no el numero de cookies.
    07/10: la sesion CADUCA. Antes se abria una sola vez por host y ejecucion,
    y cuando SITUA la cerraba a mitad de tanda los 96 documentos siguientes
    salian como «texto vacio (157 chars, html)». Ahora se vuelve a abrir
    mientras la apertura anterior haya servido, hasta MAX_APERTURAS_SESION
    por host; si una apertura no trae el documento, no se insiste mas.
    Devuelve None si no hay manera."""
    origen, rutas = _rutas_de_sesion(url)
    n = _CON_SESION.get(origen, 0)
    if n >= MAX_APERTURAS_SESION or (n > 0 and not _SESION_OK.get(origen)):
        return None
    _CON_SESION[origen] = n + 1
    _SESION_OK[origen] = False
    for ruta in rutas:
        try:
            _bajar_crudo(origen + ruta, comprobar_robots=robots, maximo=4 * 1024 * 1024)
        except (Vetado, HostSaturado):
            raise
        except Exception as e:
            log("   sesion:", origen + ruta, "->", e)
        datos, cab, cod = _bajar_crudo(url, comprobar_robots=robots, maximo=maximo)
        if es_pdf(datos) or es_word(datos):
            log("   sesion valida tras visitar", origen + ruta)
            _SESION_OK[origen] = True
            return datos, cab, cod
    return None


def bajar_documento(url: str, robots: bool = True, maximo: int = MAX_BYTES):
    """Como _bajar_crudo, pero si lo que llega es una pagina casi vacia en vez
    del documento, abre sesion en el portal y repite."""
    datos, cab, cod = _bajar_crudo(url, comprobar_robots=robots, maximo=maximo)
    if es_pdf(datos) or es_word(datos):
        return datos, cab, cod
    tipo = (cab.get("Content-Type") or "").lower() if cab else ""
    if "html" in tipo and len(datos) < 300_000:
        texto, _ = html_a_texto(_decodificar(datos, cab))
        if texto_util(texto) < 1500:
            otra = calentar_y_repetir(url, robots, maximo)
            if otra:
                return otra
    return datos, cab, cod


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


# 06/10: ordenanzas publicadas en Word (Cadiz: .doc). Antes se leian como PDF
# y fallaban con «Invalid PDF structure».
def es_word(datos: bytes) -> str | None:
    if datos[:8] == b"\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1":
        return "doc"
    if datos[:2] == b"PK" and b"word/" in datos[:4096]:
        return "docx"
    return None


def texto_de_word(datos: bytes, tipo: str) -> tuple[str, str]:
    if tipo == "docx":
        import io
        import zipfile
        with zipfile.ZipFile(io.BytesIO(datos)) as z:
            xml = z.read("word/document.xml").decode("utf-8", "replace")
        xml = re.sub(r"</w:p>", "\n", xml)
        xml = re.sub(r"<w:tab/>", "\t", xml)
        t = html.unescape(re.sub(r"<[^>]+>", "", xml))
        return t, "docx"
    if not shutil.which("antiword"):
        raise RuntimeError("documento Word .doc y no esta instalado antiword")
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, "in.doc")
        with open(f, "wb") as fh:
            fh.write(datos)
        r = subprocess.run(["antiword", "-w", "0", f], capture_output=True, timeout=300)
        if r.returncode != 0:
            raise RuntimeError("antiword: " + r.stderr.decode(errors="replace")[:200])
        return r.stdout.decode("utf-8", "replace"), "doc"


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
        # 06/10: el PDF de un visor va en un iframe/embed/object, no en un enlace
        # (Gestiona preview-document: <iframe src="/preview/pdf/....pdf">).
        if tag in ("iframe", "embed", "object"):
            a = dict(attrs)
            src = a.get("src") or a.get("data")
            if src:
                self.enlaces.append((src, "documento incrustado pdf"))

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
    # 17/10: FUENTE SIN TABLA DE CARACTERES QUE SALE COMO CIFRAS Y SIGNOS (la
    # ordenanza del mercado de Motril: 42.000 caracteres de «47828586631:5681…» y
    # un 1 % de letras). Ahi no hay palabras que contar y se daba por legible. Un
    # texto de verdad, aunque sea una tabla de tarifas, no baja del 45 % de letras.
    sin_blancos = re.sub(r"\s", "", t)
    if len(sin_blancos) >= 2000:
        letras = len(re.findall(r"[A-Za-zÁÉÍÓÚÀÈÌÒÙÜÑÇáéíóúàèìòùüñç·]", sin_blancos))
        if letras / len(sin_blancos) < 0.45:
            return True
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


def _ocr_resistente(plano: str, salida: str, forzar: bool) -> tuple[int, str]:
    """_ocr_trozo, y si ocrmypdf revienta con el trozo entero (06/10: el PGOU
    de San Fernando, «ZeroDivisionError»), se repite pagina a pagina: la que
    falle se queda como estaba y el resto del documento sale con su texto."""
    try:
        return _ocr_trozo(plano, salida, forzar)
    except RuntimeError as e:
        n = len(_paginas(plano))
        if n <= 1:
            raise
        log(f"   ocr del trozo entero fallo ({e}); se repite pagina a pagina")
    d = os.path.dirname(salida) or "."
    hechos: list[str] = []
    rotas: list[int] = []
    codigos: set[int] = set()
    for i in range(1, n + 1):
        pag = os.path.join(d, f"pag-{i}.pdf")
        _qpdf_paginas([plano, str(i)], pag, f"separar la pagina {i}")
        ocr = os.path.join(d, f"pag-{i}-ocr.pdf")
        try:
            c, _ = _ocr_trozo(pag, ocr, forzar)
            codigos.add(c)
            os.remove(pag)
            hechos.append(ocr)
        except RuntimeError:
            rotas.append(i)
            hechos.append(pag)
    if len(rotas) == n:
        raise RuntimeError(f"ocrmypdf no puede con ninguna de las {n} paginas")
    args: list[str] = []
    for h in hechos:
        args += [h, "1-z"]
    _qpdf_paginas(args, salida, "unir las paginas")
    for h in hechos:
        os.remove(h)
    nota = (f"{len(rotas)} pagina(s) sin OCR porque ocrmypdf falla con ellas: "
            + ",".join(map(str, rotas[:20])) + ("…" if len(rotas) > 20 else "")) if rotas else ""
    return (0 if 0 in codigos else 6), nota


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
        codigo, nota_acotar = _ocr_resistente(plano, salida, forzar)
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
                c, na = _ocr_resistente(trozo, ocr, forzar)
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


def paginas_sin_texto(t: str) -> bool:
    """07/10: PORTADA CON TEXTO Y EL RESTO ESCANEADO. Muchas ordenanzas llevan
    la portada (o la diligencia) en texto y el articulado como imagen:
    pdftotext saca la portada, pasa de 2.000 caracteres y no se hacia OCR, asi
    que la norma salia «sin articulos suficientes». Si al menos un tercio de
    las paginas (y dos o mas) no traen texto, toca OCR; ocrmypdf --skip-text
    respeta las paginas que ya lo tienen."""
    pags = t.split("\f")
    if pags and not pags[-1].strip():
        pags = pags[:-1]
    if len(pags) < 2:
        return False
    # «sin texto»: menos de 80 caracteres utiles (un sello o una firma)
    vacias = sum(1 for x in pags if texto_util(x) < 80)
    return vacias >= 2 and vacias >= len(pags) / 3


def texto_de_pdf(datos: bytes) -> tuple[str, str]:
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, "doc.pdf")
        with open(f, "wb") as fh:
            fh.write(datos)
        t, modo = pdftotext(f)
        roto = texto_util(t) >= 2000 and ilegible(t)
        if texto_util(t) >= 2000 and not roto and not paginas_sin_texto(t):
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
        # Paginas con solo un sello o una linea de firma (la Diputacion, el
        # PDFCreator de Benalmadena: 61 caracteres por pagina y el resto
        # imagen): --skip-text las salta porque «ya tienen texto» y el OCR no
        # sacaba nada. Si la mayoria de paginas estan asi, se fuerza el OCR.
        forzar = paginas_sin_texto(t)
        log("   sin capa de texto" + (" (paginas con solo un sello), OCR forzado…" if forzar else ", OCR…"))
        dar_capa_texto(f, o, forzar=forzar)
        t2, modo2 = pdftotext(o)
        if texto_util(t2) > texto_util(t):
            return t2, modo2 + ("+ocr forzado" if forzar else "+ocr")
        # 17/10: UNA HOJA CON CABECERA EN TEXTO Y EL CUERPO ESCANEADO (las hojas de
        # beneficios fiscales de Cordoba: 300 caracteres de cabecera y la tabla como
        # imagen). --skip-text salta la pagina porque «ya tiene texto», el OCR no saca
        # nada y el documento salia «vacio» sin haberse leido la imagen. Si sigue
        # corto, se fuerza el OCR antes de darlo por vacio.
        if not forzar and texto_util(t) < 2000:
            log("   el OCR normal no saca nada, OCR forzado…")
            o2 = os.path.join(d, "ocr-forzado.pdf")
            dar_capa_texto(f, o2, forzar=True)
            t3, modo3 = pdftotext(o2)
            if texto_util(t3) > texto_util(t) and not ilegible(t3):
                return t3, modo3 + "+ocr forzado"
        return t, modo + ("+ocr" if not forzar else "+ocr forzado")


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
    datos, cab, _ = bajar_documento(url, robots=robots)
    if es_pdf(datos):
        return texto_de_pdf(datos)
    word = es_word(datos)
    if word:
        return texto_de_word(datos, word)

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
EN_MANO: dict[str, set] = {"textos": set(), "pdfs": set(), "vistas": set()}
RETENIDAS: dict[str, set] = {"textos": set(), "pdfs": set(), "vistas": set()}


def soltar(motivo: str):
    textos = sorted(EN_MANO["textos"] | RETENIDAS["textos"])
    pdfs = sorted(EN_MANO["pdfs"] | RETENIDAS["pdfs"])
    # las vistas viajan con los pdfs, con su prefijo
    pdfs += ["vista:" + x for x in sorted(EN_MANO["vistas"] | RETENIDAS["vistas"])]
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
        for k in ("textos", "pdfs", "vistas"):
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
        # 07/10: de un host que solo deja entrar al ordenador de Jose (la GVA) se
        # lee la copia que el lector local subio a Storage; la url oficial no cambia.
        fuente = t.get("copia") or url
        if fuente != url:
            log("   se lee la copia local:", fuente)
        texto, formato = resolver(fuente, via, robots=not a_mano)
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
        datos, _, _ = bajar_documento(p["descarga"], robots=not propio)
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


# 06/10: COPIA LIGERA DE LOS PLANOS PARA VERLOS EN PANTALLA. Los planos de los
# planes generales son escaneados de 5 a 50 MB; el visor tenia que bajar el PDF
# entero y pintar la imagen completa antes de ensenar nada. Aqui se saca una
# copia a 150 ppp (imagenes en color y gris a JPEG, las de un bit a 300 ppp),
# linealizada para que el visor pueda empezar a pintar antes de tenerla entera.
# El original no se toca: el boton «PDF» del visor sigue llevando a el.
VISTA_PPP = 150
VISTA_PPP_MONO = 300
VISTA_GANANCIA_MIN = 0.8   # si la copia no baja del 80 % del original, no compensa


def copia_ligera(entrada: str, d: str) -> str:
    salida = os.path.join(d, "vista-gs.pdf")
    r = subprocess.run(
        ["gs", "-q", "-dNOPAUSE", "-dBATCH", "-dSAFER", "-sDEVICE=pdfwrite",
         "-dCompatibilityLevel=1.5", "-dDetectDuplicateImages=true",
         "-dDownsampleColorImages=true", "-dColorImageDownsampleType=/Bicubic",
         f"-dColorImageResolution={VISTA_PPP}", "-dColorImageDownsampleThreshold=1.2",
         "-dAutoFilterColorImages=false", "-dColorImageFilter=/DCTEncode",
         "-dDownsampleGrayImages=true", "-dGrayImageDownsampleType=/Bicubic",
         f"-dGrayImageResolution={VISTA_PPP}", "-dGrayImageDownsampleThreshold=1.2",
         "-dAutoFilterGrayImages=false", "-dGrayImageFilter=/DCTEncode",
         "-dDownsampleMonoImages=true", "-dMonoImageDownsampleType=/Subsample",
         f"-dMonoImageResolution={VISTA_PPP_MONO}", "-dJPEGQ=75",
         "-sOutputFile=" + salida, entrada],
        capture_output=True, timeout=1200)
    if r.returncode != 0 or not os.path.exists(salida) or os.path.getsize(salida) < 1024:
        raise RuntimeError("ghostscript: " + (r.stderr or b"").decode(errors="replace")[-200:].strip())
    lineal = os.path.join(d, "vista.pdf")
    q = subprocess.run(["qpdf", "--linearize", salida, lineal], capture_output=True, timeout=600)
    # qpdf sale con 3 si solo hay avisos: el fichero vale
    if q.returncode in (0, 3) and os.path.exists(lineal) and os.path.getsize(lineal) > 1024:
        return lineal
    return salida


def hacer_vista(v: dict):
    log(f"vista {v['plano_id']}")
    try:
        datos, _, _ = bajar_documento(v["descarga"], robots=False)
        if not es_pdf(datos):
            raise RuntimeError("la descarga no es un PDF")
        with tempfile.TemporaryDirectory() as d:
            f = os.path.join(d, "in.pdf")
            with open(f, "wb") as fh:
                fh.write(datos)
            final = copia_ligera(f, d)
            tam = os.path.getsize(final)
            if tam >= len(datos) * VISTA_GANANCIA_MIN:
                res = puerta({"modo": "vista", "plano_id": v["plano_id"], "sin_mejora": True,
                              "nota": f"{len(datos) // 1024} KB -> {tam // 1024} KB: no compensa, se ve el original"})
                log("   ->", json.dumps(res, ensure_ascii=False)[:200])
                return
            with open(final, "rb") as fh:
                cuerpo = fh.read()
        req = urllib.request.Request(v["subida"], data=cuerpo, method="PUT",
                                     headers={"Content-Type": "application/pdf", "x-upsert": "true",
                                              "cache-control": "max-age=31536000"})
        try:
            with urllib.request.urlopen(req, timeout=600, context=CTX[0]) as r:
                r.read()
        except urllib.error.HTTPError as e:
            raise RuntimeError(f"subida {e.code}: {e.read().decode(errors='replace')[:200]}") from None
        res = puerta({"modo": "vista", "plano_id": v["plano_id"], "ruta": v["ruta"],
                      "nota": f"{len(datos) // 1024} KB -> {len(cuerpo) // 1024} KB ({VISTA_PPP} ppp)"})
    except HostSaturado as e:
        log("   se retiene y se devuelve al final:", e)
        RETENIDAS["vistas"].add(v["plano_id"])
        return
    except Exception as e:
        res = puerta({"modo": "vista", "plano_id": v["plano_id"], "error": str(e)[:300]})
    log("   ->", json.dumps(res, ensure_ascii=False)[:200])


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


# ---------------------------------------------------------------- REGISTROS
# 06/10: registros autonomicos de planeamiento que cortan a las IP de Supabase
# (el de la GVA deja colgado el saludo TLS). Carril "registros": toma turnos de
# municipio en la puerta, lee el indice y devuelve inventario y documentos con
# "registro_guardar". Es rastreo automatico: robots.txt se respeta (el de
# mediambient.gva.es permite /auto/urbanismo/ a un agente generico). Lo que hay
# que bajar lo decide la base (solo para municipios dados de alta) y entra en
# la cola de textos de siempre.

GVA = "https://mediambient.gva.es/auto/urbanismo/reg-planeamiento"
GVA_PROV = {"03": "2%20ALICANTE", "12": "3%20CASTELL%D3N", "46": "4%20VALENCIA"}
GVA_TOPE_LISTADOS = 120
PAUSA_LISTADO = 0.4
PAUSA_MUNICIPIO = 3
_PROV_CACHE: dict[str, list[str]] = {}


def _sin_tildes(t: str) -> str:
    import unicodedata
    return "".join(c for c in unicodedata.normalize("NFD", t) if unicodedata.category(c) != "Mn").lower()


def clase_registro(ruta: str, nombre: str) -> str:
    """La misma regla que pf-registro-autonomico: planos y fichas antes que normas."""
    t = _sin_tildes(ruta + " / " + nombre)
    n = _sin_tildes(nombre)
    if re.search(r"\bplanos?\b", n) or (re.search(r"\bplanos?\b", t)
                                         and not re.search(r"\bnormas?\b|ordenanza|catalogo|memoria", n)):
        return "plano"
    if re.search(r"\bfichas?\b", t):
        return "ficha_ambito"
    if "catalogo" in t:
        return "catalogo_proteccion"
    if re.search(r"\bnormas?\b|ordenanzas?|normativa", t):
        return "planeamiento"
    return "documento_auxiliar"


def listar_gva(url: str) -> list[str]:
    time.sleep(PAUSA_LISTADO)
    datos, cab, _ = _bajar_crudo(url + "/", comprobar_robots=True, maximo=4 * 1024 * 1024)
    texto = datos.decode("latin-1", errors="replace")
    out, vistos = [], set()
    for parte in texto.split('href="')[1:]:
        h = parte.split('"', 1)[0]
        if not h or h.startswith(("http", "?", "/")) or h in vistos:
            continue
        vistos.add(h)
        out.append(h)
    return out


def des_gva(s: str) -> str:
    """Los nombres van en LATIN-1 escapado en la URL."""
    crudo = urllib.parse.unquote_to_bytes(s)
    try:
        t = crudo.decode("utf-8")
    except UnicodeDecodeError:
        t = crudo.decode("latin-1")
    return t[:-1] if t.endswith("/") else t


def leer_gva(ine: str) -> tuple[list, list]:
    prov = GVA_PROV.get(ine[:2])
    if not prov:
        raise RuntimeError("la provincia no esta en el registro de la GVA")
    raiz = GVA + "/" + prov
    if prov not in _PROV_CACHE:
        _PROV_CACHE[prov] = listar_gva(raiz)
    carpeta = next((c for c in _PROV_CACHE[prov] if c.startswith(ine + "%20") or c.startswith(ine + " ")), None)
    if not carpeta:
        return [], []
    mu = raiz + "/" + carpeta.rstrip("/")
    listados, parcial = 1, False
    figuras, docs = [], []
    for n1 in listar_gva(mu):
        if not n1.endswith("/"):
            continue
        listados += 1
        tipo = des_gva(n1)
        ruta_n1 = mu + "/" + n1[:-1]
        general = bool(re.match(r"^1\b", tipo)) or "GENERAL" in tipo.upper()
        for exp in listar_gva(ruta_n1):
            if not exp.endswith("/"):
                continue
            nombre = des_gva(exp)
            m = re.match(r"^(\d{5}-\d{3,4})\s+(.*)$", nombre)
            a = re.search(r"((?:19|20)\d{2})[ -]\d{3,4}\s*$", nombre) or re.search(r"\b((?:19|20)\d{2})\b", nombre)
            fid = tipo + " / " + nombre
            ruta_exp = ruta_n1 + "/" + exp[:-1]
            figuras.append({"figura_id": fid, "figura": (m.group(2) if m else nombre).strip(), "fecha": None,
                            "estado": "", "adaptacion": "", "url": ruta_exp + "/",
                            "datos": {"tipo": tipo, "codigo": m.group(1) if m else None,
                                      "anio": a.group(1) if a else None}})
            if not general:
                continue
            if listados >= GVA_TOPE_LISTADOS:
                parcial = True
                continue
            listados += 1
            for carp in listar_gva(ruta_exp):
                if not carp.endswith("/"):
                    continue
                nc = des_gva(carp)
                if not re.search(r"norma|ordenanza|catalogo", _sin_tildes(nc)):
                    continue
                if listados >= GVA_TOPE_LISTADOS:
                    parcial = True
                    break
                listados += 1
                ruta_carp = ruta_exp + "/" + carp[:-1]
                for f in listar_gva(ruta_carp):
                    if not f.lower().endswith(".pdf"):
                        continue
                    nf = des_gva(f)
                    docs.append({"figura_id": fid, "doc_id": fid + " / " + nc + " / " + nf, "expediente": nombre,
                                 "ruta": fid + " / " + nc, "nombre": nf, "url": ruta_carp + "/" + f,
                                 "clase": clase_registro(nc, nf),
                                 # la base solo lo baja si el municipio esta dado de alta
                                 "bajar": True})
    if parcial and figuras:
        figuras[0]["datos"]["parcial"] = f"tope de {GVA_TOPE_LISTADOS} listados: documentos incompletos"
    return figuras, docs


LECTORES_REGISTRO = {"gva": leer_gva}


# CARRIL DE REGISTROS EN EL ORDENADOR DE JOSE (07/10). La pasada de las 15:53
# leyo dos municipios y se quedo parada una hora sin escribir nada, hasta que
# el Programador de tareas la mato (0xC000013A) y se salto la siguiente. Leida
# a mano desde otra maquina, Alzira (el tercero) sale en 2,5 minutos: no es el
# municipio, es una peticion que se queda colgada. Tres cosas:
#  - un tope de tiempo para la lectura y otro para las copias, por debajo de la
#    hora que deja la tarea, para que siempre acabe sola y deje sitio a la
#    siguiente (lo que queda en curso lo devuelve la base a los 30 minutos);
#  - timeout por defecto en todos los sockets, tambien los que no lo ponen;
#  - si aun asi algo se cuelga, cada 10 minutos se escribe en el registro donde
#    esta parado cada hilo, para saber que peticion es.
REGISTROS_MIN = int(os.environ.get("REGISTROS_MIN", "35"))
# 25/10: las copias van PRIMERO y por tiempo, no por numero. Antes la pasada
# cogia 20 documentos fijos y solo despues de leer los registros; con la tarea
# cada 15 minutos, 12 minutos de copias dejan margen y nunca se pisan.
COPIAS_MIN = int(os.environ.get("COPIAS_MIN", "12"))
COPIAS_TANDA = int(os.environ.get("COPIAS_TANDA", "10"))
# Una descarga que no acaba en 2 minutos vuelve a la cola para otra pasada; no
# bloquea al resto (antes eran 5 minutos por documento colgado).
NAVEGADOR_ESPERA_S = int(os.environ.get("NAVEGADOR_ESPERA_S", "120"))
# Perfil propio y persistente del Chrome del lector: guarda las cookies que dan
# los cortafuegos (y el «no soy un robot» si alguna vez hay que pasarlo a mano)
# de una pasada a otra. No es el perfil diario de Jose: ese esta en uso mientras
# su Chrome esta abierto y Chrome no deja abrirlo dos veces.
NAVEGADOR_PERFIL = os.environ.get("NAVEGADOR_PERFIL", r"C:\TramitFlow\chrome-perfil")
# Donde el PC archiva las paginas que se suben desde el panel (Aportar a mano).
SEDES_DIR = os.environ.get("SEDES_DIR", "")


class _Navegador:
    """19/10: HOSTS QUE SOLO DEJAN ENTRAR A UN NAVEGADOR DE VERDAD (granada.org).
    Su cortafuegos mira la huella de la conexion, no las cabeceras: da 403 a
    GitHub, al lector del PC con cabeceras de Chrome e incluso a Chrome sin
    ventana. Con el Chrome de Jose con ventana (Playwright, channel="chrome") si
    entra. La ventana se abre fuera de la pantalla y se cierra al acabar las
    copias. Solo en el ordenador de Jose y solo cuando la descarga normal da 403.

    25/10: el documento se pide DESDE LA PAGINA (fetch con las cookies de la
    sesion, por la red del propio Chrome), no como descarga. La descarga de
    Chrome fallaba con «Download.save_as: canceled» y se quedaba esperando 5
    minutos cuando el PDF se abria en el visor en vez de descargarse. Si el
    fetch no vale, se prueba la descarga como antes. Y el perfil es persistente
    (NAVEGADOR_PERFIL): lo que el cortafuegos concede una vez sirve para las
    siguientes pasadas."""

    def __init__(self):
        self.pw = self.ctx = self.pg = None
        self.portadas: set[str] = set()

    def disponible(self) -> bool:
        if os.environ.get("REGISTROS_LOCAL") != "1" or os.environ.get("COPIAS_NAVEGADOR", "1") != "1":
            return False
        try:
            import playwright.sync_api  # noqa: F401
            return True
        except Exception:
            return False

    def _abrir(self):
        if self.pw is not None:
            return
        from playwright.sync_api import sync_playwright
        self.pw = sync_playwright().start()
        args = ["--window-position=-32000,-32000", "--window-size=900,700"]
        try:
            os.makedirs(NAVEGADOR_PERFIL, exist_ok=True)
            self.ctx = self.pw.chromium.launch_persistent_context(
                NAVEGADOR_PERFIL, channel="chrome", headless=False, accept_downloads=True, args=args)
        except Exception as e:
            log("   perfil persistente no disponible (" + str(e)[:120] + "): sin perfil")
            b = self.pw.chromium.launch(channel="chrome", headless=False, args=args)
            self.ctx = b.new_context(accept_downloads=True)
        self.pg = self.ctx.pages[0] if self.ctx.pages else self.ctx.new_page()

    def _portada(self, url: str):
        p = urllib.parse.urlsplit(url)
        base = f"{p.scheme}://{p.netloc}/"
        if base not in self.portadas:
            # Entrar por la portada: el cortafuegos da la cookie de sesion ahi.
            self.pg.goto(base, wait_until="domcontentloaded", timeout=60000)
            self.portadas.add(base)

    def bajar(self, url: str, maximo: int) -> bytes:
        self._abrir()
        self._portada(url)
        try:
            r = self.pg.evaluate(
                """async ([u, maximo, espera]) => {
                    const c = new AbortController();
                    const t = setTimeout(() => c.abort(), espera);
                    try {
                      const r = await fetch(u, { credentials: 'include', signal: c.signal });
                      if (!r.ok) return { estado: r.status };
                      const b = new Uint8Array(await r.arrayBuffer());
                      if (b.length > maximo) return { grande: b.length };
                      let s = '';
                      for (let i = 0; i < b.length; i += 0x8000) s += String.fromCharCode.apply(null, b.subarray(i, i + 0x8000));
                      return { b64: btoa(s) };
                    } catch (e) { return { error: String(e) }; } finally { clearTimeout(t); }
                }""", [url, maximo, NAVEGADOR_ESPERA_S * 1000])
        except Exception as e:
            r = {"error": str(e)[:200]}
        if r.get("b64") is not None:
            import base64
            return base64.b64decode(r["b64"])
        if r.get("grande"):
            raise RuntimeError(f"fichero mayor de {maximo // 1048576} MB")
        if r.get("estado"):
            raise RuntimeError(f"no se ha podido bajar: HTTP {r['estado']} (tambien con el navegador)")
        log("   el navegador no pudo pedirlo desde la pagina (" + str(r.get("error"))[:120] + "): se descarga")
        with self.pg.expect_download(timeout=NAVEGADOR_ESPERA_S * 1000) as d:
            self.pg.evaluate("u => { const a = document.createElement('a'); a.href = u; a.download = 'doc';"
                             " document.body.appendChild(a); a.click(); a.remove(); }", url)
        dl = d.value
        with tempfile.TemporaryDirectory() as dd:
            ruta = os.path.join(dd, "doc")
            dl.save_as(ruta)
            if os.path.getsize(ruta) > maximo:
                raise RuntimeError(f"fichero mayor de {maximo // 1048576} MB")
            with open(ruta, "rb") as fh:
                return fh.read()

    def cerrar(self):
        try:
            if self.ctx:
                self.ctx.close()
            if self.pw:
                self.pw.stop()
        except Exception:
            pass
        self.pw = self.ctx = self.pg = None
        self.portadas.clear()


NAVEGADOR = _Navegador()


def _pdf_de_ficha(url: str, datos: bytes) -> str | None:
    """24/10: la direccion de la cola es a veces la FICHA HTML del documento, no
    el documento (Huelva: /portal/documentos/<nombre>, con el PDF colgando de
    /sites/default/files/...). Se busca el PDF que enlaza la ficha: si solo hay
    uno, ese; si hay varios, el que mas palabras comparte con la direccion de la
    ficha, siempre que gane con claridad. Si no, None (y la fila se cierra con
    su motivo, que es lo que hacia antes)."""
    texto = datos.decode("utf-8", errors="replace")
    vistos: list[str] = []
    for e in re.findall(r"""href\s*=\s*["']([^"']+?\.pdf(?:\?[^"']*)?)["']""", texto, re.I):
        u = urllib.parse.urljoin(url, html.unescape(e))
        if u.startswith(("http://", "https://")) and u not in vistos:
            vistos.append(u)
    if len(vistos) == 1:
        return vistos[0]
    if not vistos:
        return None
    palabras = lambda s: set(re.findall(r"[a-z0-9]{4,}", urllib.parse.unquote(s).lower()))
    clave = palabras(urllib.parse.urlsplit(url).path)
    puntos = sorted(((len(clave & palabras(urllib.parse.urlsplit(v).path)), v) for v in vistos), reverse=True)
    if puntos[0][0] >= 2 and puntos[0][0] > puntos[1][0]:
        return puntos[0][1]
    return None


def _bajar_una(url: str, robots: bool) -> bytes:
    """Una direccion, con todo lo que sabe el PC: si da 403 se repite con el
    Chrome; si es http:// y no conecta, se prueba https:// (y si ahi da 403,
    tambien con el Chrome)."""
    try:
        datos, _, _ = bajar_documento(url, robots=robots, maximo=MAX_COPIA_LOCAL)
        return datos
    except (HostSaturado, Vetado):
        raise
    except Exception as e:
        err = str(e)
    # 24/10: direccion http:// que no conecta (El Puerto de Santa Maria: 38 PDF
    # con enlaces viejos en http que hoy solo sirve por https): se repite en
    # https. 25/10: SOLO si no conecta; un 403 en http no es «no conecta» (los
    # 15 de transparencia.granada.org se quedaban sin pasar por el Chrome).
    if url.startswith("http://") and "no se ha podido bajar" in err and "HTTP " not in err:
        log("   http no conecta: se repite en https")
        url = "https://" + url[len("http://"):]
        try:
            datos, _, _ = bajar_documento(url, robots=robots, maximo=MAX_COPIA_LOCAL)
            return datos
        except (HostSaturado, Vetado):
            raise
        except Exception as e2:
            err = str(e2)
    if "HTTP 403" in err and NAVEGADOR.disponible():
        log("   403: se baja con el navegador")
        return NAVEGADOR.bajar(url, MAX_COPIA_LOCAL)
    raise RuntimeError(err)


def _bajar_copia(url: str, robots: bool = True) -> bytes:
    """Baja un documento para la copia local.
    - 403 de un cortafuegos que solo deja pasar a un navegador: con el Chrome de Jose.
    - http:// que no conecta: se repite en https.
    - 24/10: si llega la ficha HTML del documento, se baja el PDF que enlaza
      (25/10: tambien con el Chrome si ese PDF da 403).
    - robots=False en lo aportado a mano por una persona."""
    datos = _bajar_una(url, robots)
    if es_pdf(datos) or es_word(datos):
        return datos
    pdf = _pdf_de_ficha(url, datos)
    if not pdf:
        raise RuntimeError("lo que hay en esa direccion no es un PDF (ni una ficha que enlace un solo PDF)")
    log("   es la ficha del documento: se baja el PDF que enlaza", pdf)
    datos = _bajar_una(pdf, robots)
    if not (es_pdf(datos) or es_word(datos)):
        raise RuntimeError("la ficha enlaza " + pdf + ", pero lo que hay ahi no es un PDF")
    return datos


def _copiar(c: dict) -> None:
    url = c["url"]
    log("   copia", url)
    cuerpo = {"modo": "copia_hecha", "url": url}
    try:
        datos = _bajar_copia(url, robots=not c.get("a_mano"))
        req = urllib.request.Request(c["subida"], data=datos, method="PUT",
                                     headers={"Content-Type": "application/pdf", "x-upsert": "true"})
        ultimo = None
        for intento in range(3):  # el bucket a veces contesta 429 (too_many_connections)
            try:
                with urllib.request.urlopen(req, timeout=600, context=CTX[0]) as resp:
                    resp.read()
                ultimo = None
                break
            except urllib.error.HTTPError as e:
                ultimo = RuntimeError(f"subida {e.code}: {e.read().decode(errors='replace')[:200]}")
                if e.code != 429:
                    break
                time.sleep(10 * (intento + 1))
        if ultimo:
            raise ultimo
        cuerpo.update(ruta=c["ruta"], bytes=len(datos))
    except HostSaturado as e:
        log("   servidor saturado, se deja para la proxima:", e)
        return
    except Exception as e:
        cuerpo["error"] = f"{type(e).__name__}: {str(e)[:250]}"
        log("   no se ha podido:", cuerpo["error"])
    try:
        log("   ->", json.dumps(puerta(cuerpo), ensure_ascii=False)[:200])
    except Exception as e:
        log("   no se ha podido devolver:", str(e)[:200])


def hacer_copias(hasta: float):
    """Ordenador de Jose (REGISTROS_LOCAL=1): baja los documentos de la cola de
    los hosts que solo le dejan entrar a el y los sube a Storage, para que el
    trabajador de GitHub los lea de la copia. Lo que pasa de 199 MB no cabe en el
    bucket: se cierra con su motivo.
    25/10: por tandas de COPIAS_TANDA hasta que no quede nada o se acabe el
    tiempo (antes, 20 fijos por pasada)."""
    total = 0
    vistos: set[str] = set()
    try:
        while time.time() < hasta:
            try:
                r = puerta({"modo": "copias_pendientes", "limite": COPIAS_TANDA})
            except PuertaNoDisponible as e:
                print(f"::warning::la puerta no responde ({str(e)[:200]})")
                return
            copias = [c for c in (r.get("copias") or []) if c["url"] not in vistos]
            if not copias:
                break
            log(f"copias: tanda de {len(copias)} documentos")
            for c in copias:
                if time.time() > hasta:
                    log("   tope de tiempo de las copias: el resto, en la proxima pasada")
                    break
                vistos.add(c["url"])
                _copiar(c)
                total += 1
                time.sleep(PAUSA_MUNICIPIO)
    finally:
        NAVEGADOR.cerrar()
        log(f"copias: {total} documentos en esta pasada")


def archivar_aportes():
    """25/10: las paginas subidas desde el panel (Aportar a mano) se guardan en
    OneDrive: Desarrollo IT\\Normas\\Gestiona u Otras sedes."""
    if not SEDES_DIR or not os.path.isdir(SEDES_DIR):
        return
    try:
        r = puerta({"modo": "aportes_archivar", "limite": 20})
    except Exception as e:  # una puerta anterior no conoce el modo: no para la pasada
        log("   paginas aportadas: la puerta no contesta (" + str(e)[:120] + ")")
        return
    for a in r.get("aportes") or []:
        cuerpo = {"modo": "aporte_archivado", "id": a["id"]}
        try:
            carpeta = os.path.join(SEDES_DIR, re.sub(r'[\\/:*?"<>|]+', " ", a.get("carpeta") or "Otras sedes"))
            os.makedirs(carpeta, exist_ok=True)
            nombre = re.sub(r'[\\/:*?"<>|]+', " ", a.get("fichero") or f"pagina-{a['id']}.html").strip()
            destino = os.path.join(carpeta, nombre)
            if os.path.exists(destino):
                base, ext = os.path.splitext(destino)
                destino = f"{base} ({a['id']}){ext}"
            with urllib.request.urlopen(a["descarga"], timeout=120, context=CTX[0]) as resp:
                datos = resp.read()
            with open(destino, "wb") as fh:
                fh.write(datos)
            cuerpo["ruta"] = destino
            log("   pagina archivada:", destino)
        except Exception as e:
            cuerpo["error"] = f"{type(e).__name__}: {str(e)[:200]}"
        try:
            puerta(cuerpo)
        except Exception:
            pass


def hacer_registros():
    # 25/10: en el ordenador de Jose, primero las copias (lo que mas espera) y
    # las paginas aportadas; despues los registros autonomicos.
    if os.environ.get("REGISTROS_LOCAL") == "1":
        archivar_aportes()
        hacer_copias(hasta=time.time() + COPIAS_MIN * 60)
    try:
        # REGISTROS_LOCAL=1: este trabajador corre en el ordenador de Jose y toma
        # los registros que cortan tambien a GitHub (la GVA, 07/10).
        r = puerta({"modo": "registro_tomar", "limite": int(os.environ.get("MAX_REGISTROS", "10")),
                    "local": os.environ.get("REGISTROS_LOCAL") == "1"})
    except PuertaNoDisponible as e:
        print(f"::warning::la puerta no responde ({str(e)[:200]})")
        return
    turnos = r.get("turnos") or []
    log(f"registros: {len(turnos)} municipios")
    hasta = time.time() + REGISTROS_MIN * 60
    for i, t in enumerate(turnos):
        reg, ine = t.get("registro"), t.get("municipio_ine")
        if time.time() > hasta:
            log(f"   tope de {REGISTROS_MIN} min de lectura: {len(turnos) - i} municipios para la proxima pasada")
            break
        log(f"   {reg} {ine}: leyendo")
        lector = LECTORES_REGISTRO.get(reg)
        cuerpo = {"modo": "registro_guardar", "registro": reg, "municipio_ine": ine}
        try:
            if not lector:
                raise RuntimeError(f"este trabajador no sabe leer el registro {reg}")
            figuras, docs = lector(ine)
            cuerpo.update(figuras=figuras, docs=docs)
            log(f"   {reg} {ine}: {len(figuras)} figuras, {len(docs)} documentos")
        except (Vetado, HostSaturado) as e:
            cuerpo["error"] = f"{type(e).__name__}: {str(e)[:250]}"
        except Exception as e:
            cuerpo["error"] = f"{type(e).__name__}: {str(e)[:250]}"
        try:
            res = puerta(cuerpo)
            log("   ->", json.dumps(res, ensure_ascii=False)[:200])
        except PuertaNoDisponible as e:
            log("   no se ha podido devolver:", str(e)[:200])
        if i < len(turnos) - 1:
            time.sleep(PAUSA_MUNICIPIO)


# --------------------------------------------------------------------------
# 17/10: CARRIL DE HOJAS. Las hojas rasterizadas de las normas en PDF (lo que
# enseña el visor para ver tablas y dibujos tal como se publicaron) las hacia la
# edge function pf-hoja-pdf, de 12 en 12 o de 24 en 24 paginas porque el worker
# de Supabase no da para mas, y cada llamada volvia a bajar el PDF ENTERO del
# bucket: un PDF de 472 paginas se bajaba 40 veces. Era la mayor parte del
# Cached Egress del proyecto. Aqui el PDF se baja UNA vez y salen todas sus
# hojas.
#
# Las hojas salen con pdftoppm a la misma resolucion que las de pf-hoja-pdf
# (escala 1,35 = 97,2 ppp) y pasan por optipng, SIN PERDIDA: si la hoja es gris
# se guarda en gris, si tiene pocos colores, con paleta. El pixel es el mismo.
#
# Y lo ya guardado: el mismo carril recomprime los PNG del bucket (hojas,
# figuras, tablas...) que hizo el codificador antiguo (RGBA sin filtro). Solo se
# sube la version nueva si pesa menos; la ruta no cambia, asi que nada de lo que
# la apunta se entera.
# --------------------------------------------------------------------------
HOJA_PPP = 97.2                       # = escala 1,35 de pf-hoja-pdf
HOJAS_TROZO = 40                      # hojas por entrega a la puerta (el avance queda apuntado)
HOJAS_MIN = int(os.environ.get("HOJAS_MIN", "120"))
MAX_HOJAS_DOCS = int(os.environ.get("MAX_HOJAS", "0"))
MAX_RECOMPRIMIR = int(os.environ.get("MAX_RECOMPRIMIR", "0"))
HILOS_PNG = max(1, (os.cpu_count() or 2))
GANANCIA_MIN = 0.97                   # recomprimir: si no baja al menos un 3 %, no se sube


def _optipng(ruta: str) -> None:
    # -o2: medido con una hoja real del codificador antiguo, 292 KB -> 136 KB
    # en 0,7 s (-o1 se quedaba en 182 KB; -o3 tarda el doble y no gana nada).
    # -strip all quita metadatos que nadie usa. Reduce sola a gris o a paleta
    # cuando se puede, sin perdida.
    subprocess.run(["optipng", "-quiet", "-o2", "-strip", "all", ruta],
                   check=True, timeout=300)


def _png_medidas(ruta: str) -> tuple[int, int]:
    with open(ruta, "rb") as fh:
        cab = fh.read(24)
    return int.from_bytes(cab[16:20], "big"), int.from_bytes(cab[20:24], "big")


def _subir_png(url_subida: str, datos: bytes) -> None:
    req = urllib.request.Request(url_subida, data=datos, method="PUT",
                                 headers={"Content-Type": "image/png", "x-upsert": "true"})
    for espera in (0, 5, 20):
        if espera:
            time.sleep(espera)
        try:
            with urllib.request.urlopen(req, timeout=120, context=CTX[0]) as r:
                r.read()
            return
        except urllib.error.HTTPError as e:
            if e.code < 500:
                raise RuntimeError(f"subida {e.code}: {e.read().decode(errors='replace')[:200]}") from None
        except (urllib.error.URLError, ConnectionError, TimeoutError):
            pass
    raise RuntimeError("subida: el Storage no responde")


def _paginas_pdf(ruta: str) -> int:
    r = subprocess.run(["pdfinfo", ruta], capture_output=True, timeout=120)
    m = re.search(rb"^Pages:\s+(\d+)", r.stdout, re.M)
    if not m:
        raise RuntimeError("pdfinfo no da el numero de paginas")
    return int(m.group(1))


def ph(cuerpo: dict, timeout: int = 120) -> dict:
    return puerta(cuerpo, timeout, destino=PUERTA_HOJAS)


def hacer_hoja_doc(t: dict, hasta: float) -> None:
    iid = t["instrumento_id"]
    log(f"hojas {iid} desde la {t.get('desde', 1)}")
    from concurrent.futures import ThreadPoolExecutor
    try:
        propio = "iqskiegwxucfuimnnoiu.supabase.co/" in t["descarga"]
        datos, _, _ = bajar_documento(t["descarga"], robots=not propio)
        if not es_pdf(datos):
            raise RuntimeError("la descarga no es un PDF")
        with tempfile.TemporaryDirectory() as d:
            pdf = os.path.join(d, "in.pdf")
            with open(pdf, "wb") as fh:
                fh.write(datos)
            del datos
            total = _paginas_pdf(pdf)
            p = max(1, int(t.get("desde") or 1))
            while p <= total:
                if time.time() > hasta:
                    log(f"   tope de tiempo en la hoja {p} de {total}: sigue en la proxima pasada")
                    ph({"modo": "hojas_hecho", "instrumento_id": iid, "documento_id": t["documento_id"],
                            "total": total, "paginas": [], "soltar": True})
                    return
                fin = min(p + HOJAS_TROZO - 1, total)
                sal = os.path.join(d, f"t{p}")
                os.makedirs(sal, exist_ok=True)
                subprocess.run(["pdftoppm", "-png", "-r", str(HOJA_PPP), "-f", str(p), "-l", str(fin),
                                pdf, os.path.join(sal, "h")], check=True, timeout=1800,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                # pdftoppm numera con ceros segun el total: se lee el numero del nombre
                hechas = {}
                for nombre in os.listdir(sal):
                    m = re.search(r"-(\d+)\.png$", nombre)
                    if m:
                        hechas[int(m.group(1))] = os.path.join(sal, nombre)
                with ThreadPoolExecutor(HILOS_PNG) as ex:
                    list(ex.map(_optipng, hechas.values()))
                r = ph({"modo": "hojas_subidas", "instrumento_id": iid, "paginas": sorted(hechas)})
                subidas = r.get("subidas") or {}
                filas = []

                def subir(pag: int):
                    ruta = hechas[pag]
                    with open(ruta, "rb") as fh:
                        _subir_png(subidas[str(pag)]["url"], fh.read())
                    w, h = _png_medidas(ruta)
                    return {"pagina": pag, "ruta": subidas[str(pag)]["ruta"], "ancho": w, "alto": h,
                            "bytes": os.path.getsize(ruta)}
                with ThreadPoolExecutor(4) as ex:
                    filas = list(ex.map(subir, sorted(hechas)))
                res = ph({"modo": "hojas_hecho", "instrumento_id": iid, "documento_id": t["documento_id"],
                              "total": total, "paginas": filas})
                kb = sum(f["bytes"] for f in filas) // max(1, len(filas)) // 1024
                log(f"   hojas {p}-{fin} de {total} ({kb} KB por hoja) ->",
                    json.dumps(res, ensure_ascii=False)[:160])
                shutil.rmtree(sal, ignore_errors=True)
                p = fin + 1
    except HostSaturado as e:
        log("   servidor saturado, se suelta:", e)
        ph({"modo": "hojas_hecho", "instrumento_id": iid, "documento_id": t["documento_id"],
                "paginas": [], "soltar": True})
    except Exception as e:
        res = ph({"modo": "hojas_hecho", "instrumento_id": iid, "documento_id": t["documento_id"],
                      "paginas": [], "error": f"{type(e).__name__}: {str(e)[:250]}"})
        log("   error ->", json.dumps(res, ensure_ascii=False)[:200])


def hacer_recompresion(hasta: float) -> None:
    from concurrent.futures import ThreadPoolExecutor
    total_antes = total_despues = n = 0
    while time.time() < hasta:
        try:
            r = ph({"modo": "recomprimir_tomar", "limite": MAX_RECOMPRIMIR})
        except PuertaNoDisponible as e:
            print(f"::warning::la puerta no responde ({str(e)[:200]})")
            return
        objs = r.get("objetos") or []
        if not objs:
            break
        resultados = []

        def uno(o: dict) -> dict:
            out = {"ruta": o["ruta"]}
            try:
                datos, _, _ = bajar_documento(o["descarga"], robots=False, maximo=60 * 1024 * 1024)
                if datos[:8] != b"\x89PNG\r\n\x1a\n":
                    raise RuntimeError("no es un PNG")
                with tempfile.TemporaryDirectory() as d:
                    f = os.path.join(d, "x.png")
                    with open(f, "wb") as fh:
                        fh.write(datos)
                    _optipng(f)
                    nuevo = os.path.getsize(f)
                    out["antes"] = len(datos)
                    if nuevo <= len(datos) * GANANCIA_MIN:
                        with open(f, "rb") as fh:
                            _subir_png(o["subida"], fh.read())
                        out["despues"] = nuevo
                    else:
                        out["despues"] = len(datos)   # no compensa: se queda como estaba
            except Exception as e:
                out["error"] = f"{type(e).__name__}: {str(e)[:200]}"
            return out
        with ThreadPoolExecutor(HILOS_PNG * 2) as ex:
            resultados = list(ex.map(uno, objs))
        try:
            res = ph({"modo": "recomprimir_hecho", "objetos": resultados})
        except PuertaNoDisponible as e:
            log("   no se ha podido devolver:", str(e)[:200])
            return
        a = sum(x.get("antes", 0) for x in resultados)
        b = sum(x.get("despues", 0) for x in resultados)
        total_antes += a
        total_despues += b
        n += len(resultados)
        log(f"recomprimir: {len(resultados)} PNG, {a // 1048576} MB -> {b // 1048576} MB ->",
            json.dumps(res, ensure_ascii=False)[:160])
    if n:
        log(f"recomprimir total: {n} PNG, {total_antes // 1048576} MB -> {total_despues // 1048576} MB")


def hacer_hojas() -> None:
    hasta = INICIO + HOJAS_MIN * 60
    if MAX_HOJAS_DOCS > 0:
        while time.time() < hasta:
            try:
                r = ph({"modo": "hojas_tomar", "limite": MAX_HOJAS_DOCS})
            except PuertaNoDisponible as e:
                print(f"::warning::la puerta no responde ({str(e)[:200]})")
                break
            docs = r.get("documentos") or []
            log(f"hojas: {len(docs)} documentos")
            if not docs:
                break
            for t in docs:
                if time.time() > hasta:
                    ph({"modo": "hojas_hecho", "instrumento_id": t["instrumento_id"],
                            "documento_id": t["documento_id"], "paginas": [], "soltar": True})
                    continue
                try:
                    hacer_hoja_doc(t, hasta)
                except PuertaNoDisponible as e:
                    log("   no se ha podido devolver:", str(e)[:200])
    # Con el tiempo que quede, lo ya guardado.
    if MAX_RECOMPRIMIR > 0 and time.time() < hasta:
        hacer_recompresion(hasta)


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
    quiere_vistas = int(os.environ.get("MAX_VISTAS", "0")) > 0
    quiere_registros = int(os.environ.get("MAX_REGISTROS", "0")) > 0
    quiere_hojas = MAX_HOJAS_DOCS > 0 or MAX_RECOMPRIMIR > 0
    if quiere_hojas:
        try:
            rh = ph({"modo": "contar"})
        except Exception as e:
            print(f"::warning::la puerta de hojas no responde ({str(e)[:200]})")
            rh = {}
        log("contar hojas:", rh)
        r["hojas"] = (MAX_HOJAS_DOCS > 0 and rh.get("hojas")) or (MAX_RECOMPRIMIR > 0 and rh.get("recomprimir"))
    # Las fichas de sede (HTML ligero) van con el carril de textos.
    hay = bool((quiere_textos and (r.get("textos") or r.get("fichas_html")))
               or (quiere_pdfs and r.get("pdfs"))
               or (quiere_vistas and r.get("vistas"))
               or (quiere_registros and r.get("registros"))
               or (quiere_hojas and r.get("hojas")))
    salida = os.environ.get("GITHUB_OUTPUT")
    if salida:
        with open(salida, "a") as fh:
            fh.write(f"hay={'true' if hay else 'false'}\n")


def trabajar():
    signal.signal(signal.SIGTERM, _cortar)
    signal.signal(signal.SIGINT, _cortar)
    if MAX_HOJAS_DOCS > 0 or MAX_RECOMPRIMIR > 0:
        # carril de hojas: rasterizado y recompresion, sin las otras colas
        socket.setdefaulttimeout(120)
        hacer_hojas()
        return
    if int(os.environ.get("MAX_REGISTROS", "0")) > 0:
        # carril de registros: solo lectura de indices, sin colas de textos ni PDFs
        socket.setdefaulttimeout(90)
        faulthandler.dump_traceback_later(600, repeat=True, file=sys.stdout)
        try:
            hacer_registros()
        finally:
            faulthandler.cancel_dump_traceback_later()
        return
    ronda = 0
    motivo = "fin de la ejecucion"
    try:
        while queda() > 20 * 60 and ronda < MAX_RONDAS:  # sin margen para un OCR largo no se toma nada mas
            if ronda > 0:
                time.sleep(PAUSA_RONDA_S)  # 07/10: tandas espaciadas
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
                            "max_vistas": int(os.environ.get("MAX_VISTAS", "0")),
                            "admite": ["solo_comprimir", "trocear", "fichas", "sin_robots", "vistas"]})
            except PuertaNoDisponible as e:
                # Lo ya hecho esta devuelto; lo que no se ha tomado sigue en la cola.
                print(f"::warning::la puerta no responde, se para aqui ({str(e)[:200]})")
                break
            textos, pdfs = r.get("textos") or [], r.get("pdfs") or []
            fichas = r.get("fichas_html") or []
            vistas = r.get("vistas") or []
            log(f"ronda {ronda}: {len(textos)} textos, {len(pdfs)} pdfs, {len(fichas)} fichas, {len(vistas)} vistas")
            if not textos and not pdfs and not fichas and not vistas:
                break
            EN_MANO["vistas"].update(v["plano_id"] for v in vistas)
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
            for v in vistas:
                if queda() < 5 * 60:
                    break  # las no hechas se sueltan al final
                try:
                    hacer_vista(v)
                except PuertaNoDisponible as e:
                    log("   no se ha podido devolver:", str(e)[:200])
                except Exception as e:
                    print(f"::warning::vista {v.get('plano_id')}: {type(e).__name__}: {str(e)[:200]}", flush=True)
                EN_MANO["vistas"].discard(v["plano_id"])
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
    {"contar": contar, "trabajar": trabajar, "registros": hacer_registros}[orden]()
