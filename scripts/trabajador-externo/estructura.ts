// TramitFlow - trabajador externo: PAGINADO y BLOQUES de las normas en PDF grandes.
//
// POR QUE EXISTE
//
// pf-paginar-norma (en que pagina esta cada articulo) y pf-estructurar-norma
// (titulos, tablas, figuras y formulas de cada pagina) corren en el edge de
// Supabase: 150 s por llamada y poca memoria, y en cada llamada vuelven a bajar
// y a abrir el PDF entero. Con los PDF de cientos de paginas se mueren antes de
// guardar nada: no avanzan y a los tres intentos salen como fallo (17-10-2026:
// 92 sin paginar, mediana 377 paginas; 268 normas sin bloques, mediana 40).
//
// Aqui va EL MISMO CALCULO (copiado tal cual de pf-estructurar-norma v15 y de
// pf-paginar-norma v2), sin reloj de 150 s, abriendo el PDF una sola vez. Lo
// unico que cambia es por donde se lee y se escribe: por la puerta
// pf-trabajador-hojas, con la clave del trabajador. Nunca con la clave de
// servicio.
//
//   deno run -A estructura.ts contar     -> hay=true|false en GITHUB_OUTPUT
//   deno run -A estructura.ts trabajar   -> paginado y luego bloques
//
// Si se cambia el calculo en el edge, hay que traerlo aqui (y al reves).

import { getDocumentProxy } from "npm:unpdf@0.12.1";
import { PDFiumLibrary } from "npm:@hyzyla/pdfium@2.1.5";

const ESCALA = 2;
const TINTA = 200;
const RAYA_TROZO = 20;      // px: un trozo suelto de raya, antes de pegarlo
const RAYA_MIN = 50;       // px: lo que ya cuenta como raya, despues de pegarla
const JUNTA = 4;
const MIN_FIG = 70;
const SOBRA_MAX = 0.015;


type Item = {
  s: string; x0: number; x1: number; yb: number; yt: number;
  alto: number; negrita: boolean; recta: boolean;
};
type Raya = { a: number; d0: number; d1: number };
type Caja = { x0: number; y0: number; x1: number; y1: number };
type Celda = { t: string; x0: number; x1: number; cx: number };
type Hueca = { t: string; cs: number } | null;
type Tabla = {
  reg: Caja; cols: number[][]; filas: Hueca[][]; usados: Item[];
  cabecera: number; rotulo: string | null; lateral: string[];
};

const lum = (b: Uint8Array, p: number) => 0.299 * b[p + 2] + 0.587 * b[p + 1] + 0.114 * b[p];

// ------------------------------------------------------------------ PNG ----
const CRC = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; }
  return t;
})();
function crc32(b: Uint8Array): number {
  let c = 0xFFFFFFFF;
  for (let i = 0; i < b.length; i++) c = CRC[(c ^ b[i]) & 0xFF] ^ (c >>> 8);
  return (c ^ 0xFFFFFFFF) >>> 0;
}
function trozo(tipo: string, d: Uint8Array): Uint8Array {
  const out = new Uint8Array(12 + d.length); const dv = new DataView(out.buffer);
  dv.setUint32(0, d.length); out.set(new TextEncoder().encode(tipo), 4); out.set(d, 8);
  dv.setUint32(8 + d.length, crc32(out.subarray(4, 8 + d.length)));
  return out;
}
async function aPng(bgra: Uint8Array, W: number, x: number, y: number, w: number, h: number): Promise<Uint8Array> {
  const linea = w * 4 + 1;
  const bruto = new Uint8Array(h * linea);
  for (let j = 0; j < h; j++) {
    let s = ((y + j) * W + x) * 4, d = j * linea + 1;
    for (let i = 0; i < w; i++) {
      bruto[d] = bgra[s + 2]; bruto[d + 1] = bgra[s + 1]; bruto[d + 2] = bgra[s]; bruto[d + 3] = 255;
      s += 4; d += 4;
    }
  }
  const z = new Uint8Array(await new Response(new Blob([bruto]).stream().pipeThrough(new CompressionStream("deflate"))).arrayBuffer());
  const ihdr = new Uint8Array(13); const dv = new DataView(ihdr.buffer);
  dv.setUint32(0, w); dv.setUint32(4, h); ihdr[8] = 8; ihdr[9] = 6;
  const ps = [new Uint8Array([137,80,78,71,13,10,26,10]), trozo("IHDR", ihdr), trozo("IDAT", z), trozo("IEND", new Uint8Array(0))];
  const out = new Uint8Array(ps.reduce((n, p) => n + p.length, 0));
  let o = 0; for (const p of ps) { out.set(p, o); o += p.length; }
  return out;
}

// ----------------------------------------------------------------- RAYAS ---
// Se recogen los trozos cortos y se pegan DESPUES: el borde inferior de la
// Tabla 3.4 del SE-AE viene en ocho trozos, uno por columna, y varios miden
// menos de lo que se pediria a una raya. Filtrando antes de pegar, la tabla se
// queda sin fondo y se corta en la cabecera.
const GRUESO = 5;   // px: por encima de esto ya no es una raya, es tinta
function finaH(d: Uint8Array, W: number, H: number, y: number, x0: number, x1: number): boolean {
  // se mira arriba y abajo en tres puntos: una raya tiene blanco a los lados
  for (const f of [y - GRUESO, y + GRUESO]) {
    if (f < 0 || f >= H) continue;
    let osc = 0;
    for (let k = 1; k <= 3; k++) {
      const x = Math.round(x0 + (x1 - x0) * k / 4);
      if (x >= 0 && x < W && lum(d, (f * W + x) * 4) < TINTA) osc++;
    }
    if (osc >= 3) return false;
  }
  return true;
}
function rayasH(d: Uint8Array, W: number, H: number): Raya[] {
  const out: Raya[] = [];
  for (let y = 0; y < H; y++) {
    let ini = -1;
    for (let x = 0; x <= W; x++) {
      const osc = x < W && lum(d, (y * W + x) * 4) < TINTA;
      if (osc && ini < 0) ini = x;
      else if (!osc && ini >= 0) {
        if (x - ini >= RAYA_TROZO && finaH(d, W, H, y, ini, x)) out.push({ a: y, d0: ini, d1: x });
        ini = -1;
      }
    }
  }
  return fundirRayas(out).filter((r) => r.d1 - r.d0 >= RAYA_MIN);
}
function finaV(d: Uint8Array, W: number, H: number, x: number, y0: number, y1: number): boolean {
  for (const c of [x - GRUESO, x + GRUESO]) {
    if (c < 0 || c >= W) continue;
    let osc = 0;
    for (let k = 1; k <= 3; k++) {
      const y = Math.round(y0 + (y1 - y0) * k / 4);
      if (y >= 0 && y < H && lum(d, (y * W + c) * 4) < TINTA) osc++;
    }
    if (osc >= 3) return false;
  }
  return true;
}
function rayasV(d: Uint8Array, W: number, H: number): Raya[] {
  const out: Raya[] = [];
  for (let x = 0; x < W; x++) {
    let ini = -1;
    for (let y = 0; y <= H; y++) {
      const osc = y < H && lum(d, (y * W + x) * 4) < TINTA;
      if (osc && ini < 0) ini = y;
      else if (!osc && ini >= 0) {
        if (y - ini >= RAYA_TROZO && finaV(d, W, H, x, ini, y)) out.push({ a: x, d0: ini, d1: y });
        ini = -1;
      }
    }
  }
  return fundirRayas(out).filter((r) => r.d1 - r.d0 >= 16);
}
function fundirRayas(rs: Raya[]): Raya[] {
  const o = [...rs].sort((p, q) => p.a - q.a || p.d0 - q.d0);
  const out: Raya[] = [];
  for (const r of o) {
    const u = out[out.length - 1];
    if (u && r.a - u.a <= JUNTA && r.d0 <= u.d1 + 3 * JUNTA && r.d1 >= u.d0 - 3 * JUNTA) {
      u.d0 = Math.min(u.d0, r.d0); u.d1 = Math.max(u.d1, r.d1);
    } else out.push({ ...r });
  }
  return out;
}

// -------------------------------------------------------------- 1. PALABRA -
// La fuente Symbol no guarda letras: guarda posiciones. Word exporta con ella
// las griegas, los sumatorios y los "menor o igual", y llegan como caracteres
// de uso privado (U+F000-U+F8FF) que no son nada. La codificacion de Adobe es
// fija, asi que se descifra.
const SIMBOLO: Record<number, string> = {
  34:"∀",36:"∃",39:"∋",42:"∗",45:"−",64:"≅",
  65:"Α",66:"Β",67:"Χ",68:"Δ",69:"Ε",70:"Φ",71:"Γ",
  72:"Η",73:"Ι",74:"ϑ",75:"Κ",76:"Λ",77:"Μ",78:"Ν",
  79:"Ο",80:"Π",81:"Θ",82:"Ρ",83:"Σ",84:"Τ",85:"Υ",
  86:"ς",87:"Ω",88:"Ξ",89:"Ψ",90:"Ζ",
  92:"∴",94:"⊥",96:"‾",
  97:"α",98:"β",99:"χ",100:"δ",101:"ε",102:"φ",103:"γ",
  104:"η",105:"ι",106:"ϕ",107:"κ",108:"λ",109:"μ",110:"ν",
  111:"ο",112:"π",113:"θ",114:"ρ",115:"σ",116:"τ",117:"υ",
  118:"ϖ",119:"ω",120:"ξ",121:"ψ",122:"ζ",126:"∼",
  163:"≤",165:"∞",171:"↔",172:"←",173:"↑",174:"→",175:"↓",
  176:"°",177:"±",178:"″",179:"≥",180:"×",181:"∝",182:"∂",
  183:"•",184:"÷",185:"≠",186:"≡",187:"≈",188:"…",
  191:"↵",196:"⊗",197:"⊕",198:"∅",199:"∩",200:"∪",201:"⊃",
  202:"⊇",203:"⊄",204:"⊂",205:"⊆",206:"∈",207:"∉",
  208:"∠",209:"∇",210:"®",211:"©",212:"™",213:"∏",214:"√",
  215:"⋅",216:"¬",217:"∧",218:"∨",219:"⇔",220:"⇐",221:"⇑",
  222:"⇒",223:"⇓",224:"◊",225:"〈",229:"∑",
  230:"(",231:"",232:"",233:"[",234:"",235:"",236:"{",237:"",238:"",239:"",
  241:"〉",242:"∫",243:"∫",244:"",245:"",
  246:")",247:"",248:"",249:"]",250:"",251:"",252:"}",253:"",254:"",
};
function descifrar(s: string, fuente: string): string {
  if (!/symbol/i.test(fuente)) return s;
  let out = "";
  for (const c of s) {
    const k = c.codePointAt(0)!;
    out += (k >= 0xF000 && k <= 0xF8FF) ? (SIMBOLO[k & 0xFF] ?? "") : c;
  }
  return out;
}

const SUP: Record<string, string> = {"0":"⁰","1":"¹","2":"²","3":"³","4":"⁴","5":"⁵","6":"⁶","7":"⁷","8":"⁸","9":"⁹","+":"⁺","-":"⁻","(":"⁽",")":"⁾","n":"ⁿ"};
const SUB: Record<string, string> = {"0":"₀","1":"₁","2":"₂","3":"₃","4":"₄","5":"₅","6":"₆","7":"₇","8":"₈","9":"₉","+":"₊","-":"₋","(":"₍",")":"₎","a":"ₐ","e":"ₑ","h":"ₕ","i":"ᵢ","k":"ₖ","l":"ₗ","m":"ₘ","n":"ₙ","o":"ₒ","p":"ₚ","r":"ᵣ","s":"ₛ","t":"ₜ","u":"ᵤ","v":"ᵥ","x":"ₓ"};
const volar = (s: string, m: Record<string, string>) =>
  [...s].map((c) => m[c] ?? c).join("");

// Un superindice o un subindice NO es una palabra suelta: es parte de la de al
// lado. Y tiene que caber DENTRO de su caja: si basta con rozarla, el volado
// del renglon de abajo tambien roza y sale "su2 cerramiento".
function fundirIndices(its: Item[]): Item[] {
  const ws = [...its].sort((a, b) => a.x0 - b.x0 || a.yt - b.yt);
  const muerto = new Set<Item>();
  for (const w of ws) {
    if (muerto.has(w) || w.s.length > 3) continue;
    let mejor: Item | null = null, dmin = 9e9;
    for (const z of ws) {
      if (z === w || muerto.has(z) || z.alto <= w.alto * 1.15) continue;
      const dx = w.x0 - z.x1;
      if (dx < -1.5 || dx > 3.5) continue;
      const hz = z.yb - z.yt;
      if (w.yt < z.yt - 0.30 * hz || w.yb > z.yb + 0.30 * hz) continue;
      if (dx < dmin) { dmin = dx; mejor = z; }
    }
    if (!mejor) continue;
    const arriba = (w.yt + w.yb) / 2 < (mejor.yt + mejor.yb) / 2;
    mejor.s += volar(w.s, arriba ? SUP : SUB);
    mejor.x1 = Math.max(mejor.x1, w.x1);
    muerto.add(w);
  }
  return ws.filter((w) => !muerto.has(w));
}

// El rotulo lateral de una tabla va girado 90 grados: llega letra a letra y de
// abajo arriba, y ademas cada trocito viene del reves dentro de si mismo.
function separarGiradas(its: Item[]): { rectas: Item[]; giradas: (Caja & { texto: string })[] } {
  const rectas = its.filter((i) => i.recta);
  const gir = its.filter((i) => !i.recta).sort((a, b) => Math.round(a.x0 / 8) - Math.round(b.x0 / 8) || b.yt - a.yt);
  const grupos: Item[][] = [];
  for (const w of gir) {
    const u = grupos[grupos.length - 1];
    const v = u ? u[u.length - 1] : null;
    if (v && Math.abs(v.x0 - w.x0) <= 8 && v.yt - w.yb <= 12) u!.push(w);
    else grupos.push([w]);
  }
  const giradas: (Caja & { texto: string })[] = [];
  for (const g of grupos) {
    let t = "";
    for (let k = 0; k < g.length; k++) {
      if (k && g[k - 1].yt - g[k].yb >= 4) t += " ";
      t += g[k].s.length > 1 ? [...g[k].s].reverse().join("") : g[k].s;
    }
    t = t.trim();
    if (t.length < 3) continue;
    giradas.push({
      texto: t,
      x0: Math.min(...g.map((z) => z.x0)), x1: Math.max(...g.map((z) => z.x1)),
      y0: Math.min(...g.map((z) => z.yt)), y1: Math.max(...g.map((z) => z.yb)),
    });
  }
  return { rectas, giradas };
}

// -------------------------------------------------------------- 2. RENGLON -
function renglones(items: Item[]): Item[][] {
  const o = [...items].sort((a, b) => (a.yt - b.yt) || (a.x0 - b.x0));
  const out: Item[][] = [];
  for (const it of o) {
    const u = out[out.length - 1];
    if (u && Math.abs(u[0].yt - it.yt) <= Math.max(2, 0.45 * it.alto)) u.push(it);
    else out.push([it]);
  }
  for (const r of out) r.sort((a, b) => a.x0 - b.x0);
  return out;
}
const PEGA_IZQ = new Set([")", "]", ",", ".", ";", ":", "%", "º", "°"]);
const PEGA_DER = new Set(["(", "[", "¿", "¡"]);
function unir(ts: string[]): string {
  let out = "";
  for (const t of ts) {
    if (!out) out = t;
    else if (PEGA_IZQ.has(t[0]) || PEGA_DER.has(out[out.length - 1])) out += t;
    else out += " " + t;
  }
  return out.replace(/\s+/g, " ").trim();
}
const texto = (r: Item[]) => unir(r.map((w) => w.s));

// ---------------------------------------------------------------- 3. MARCO -
// Lo que define al encabezado no es cuanto se repite sino DONDE esta. El DB-SI
// cambia el encabezado en cada anejo: el de "Anejo C" sale en 16 paginas de 92
// y con un umbral del 30% se colaba en el texto. En la franja de cabecera o de
// pie, con repetirse tres veces basta; y un folio suelto no necesita ni eso.
const norma = (s: string) => s.replace(/\d+/g, "#").replace(/\s+/g, " ").trim().toLowerCase();
const FOLIO = /^(#|página\s*#|pag\.?\s*#|#\s*de\s*#|#\s*\/\s*#)$/;
const enMargen = (r: Item[], H: number) =>
  r[0].yt < 0.08 * H || Math.max(...r.map((z) => z.yb)) > 0.92 * H;

function marcoDelDocumento(paginas: Map<number, Item[][]>, H: number, N: number): Set<string> {
  const c = new Map<string, { n: number; margen: boolean }>();
  for (const rens of paginas.values()) {
    for (const r of rens) {
      const k = Math.round(r[0].yt / H * 40) + "|" + norma(texto(r));
      const v = c.get(k) ?? { n: 0, margen: enMargen(r, H) };
      v.n++; v.margen = v.margen || enMargen(r, H); c.set(k, v);
    }
  }
  const out = new Set<string>();
  for (const [k, v] of c) {
    const t = k.split("|").slice(1).join("|");
    if (v.margen && (v.n >= 3 || FOLIO.test(t))) out.add(k);
    else if (v.n >= Math.max(3, 0.30 * N)) out.add(k);
  }
  return out;
}
const esMarco = (r: Item[], H: number, marco: Set<string>) =>
  (enMargen(r, H) && FOLIO.test(norma(texto(r)))) ||
  marco.has(Math.round(r[0].yt / H * 40) + "|" + norma(texto(r)));

// --------------------------------------------------------------- LA CELDA --
// El hueco que separa dos celdas depende del TAMANO DE LETRA DEL RENGLON, no
// del cuerpo del documento: las tablas del DB-HE van en 7 puntos y sus columnas
// se separan 8. Con el umbral del cuerpo, la fila entera se lee como una celda.
function hueco(r: Item[], cuerpo: number): number {
  const t = r.map((w) => w.alto).sort((a, b) => a - b);
  const m = t.length ? t[t.length >> 1] : cuerpo;
  return Math.max(3, 0.9 * m);
}
const _cache = new WeakMap<Item[], Map<number, Celda[]>>();
function celdas(r: Item[], u: number): Celda[] {
  let m = _cache.get(r);
  if (!m) { m = new Map(); _cache.set(r, m); }
  const k = Math.round(u * 10);
  const v = m.get(k);
  if (v) return v;
  const c = _celdas(r, u);
  m.set(k, c);
  return c;
}
function _celdas(r: Item[], u: number): Celda[] {
  const g: Item[][] = [[r[0]]];
  for (const w of r.slice(1)) {
    const k = g[g.length - 1];
    if (w.x0 - k[k.length - 1].x1 > u) g.push([w]); else k.push(w);
  }
  return g.map((k) => ({
    t: unir(k.map((z) => z.s)), x0: k[0].x0, x1: k[k.length - 1].x1,
    cx: (k[0].x0 + k[k.length - 1].x1) / 2,
  }));
}

// Las columnas las dicta el CUERPO de la tabla, y se buscan por el BLANCO.
// No vale agrupar celdas que se solapen: basta con que una fila lleve el
// ordinal pegado al texto ("IV Zona urbana...") y otra lo lleve suelto ("I" y
// aparte el texto) para que dos columnas se fundan y la tabla se descuadre.
// Un pasillo es blanco limpio, o blanco que cruza alguna fila pero con celda
// PEGADA a los dos lados: eso distingue el hueco entre columnas del blanco que
// deja una fila corta al terminar su texto.
// Y las rayas verticales que el PDF dibuja MANDAN: son la reticula declarada.
function columnas(filas: Celda[][], cuerpo: number, dibujadas: number[] = []): number[][] {
  if (!filas.length) return [];
  const m = Math.max(...filas.map((f) => f.length));
  const votan = filas.filter((f) => f.length >= Math.max(2, m * 0.6));
  const cels = votan.flat();
  if (!cels.length) return [];
  const x0 = Math.min(...cels.map((c) => c.x0)) - 1;
  const x1 = Math.max(...cels.map((c) => c.x1)) + 1;
  const n = Math.round(x1 - x0) + 1;
  const cruza = new Int32Array(n);
  for (const c of cels) {
    const a = Math.max(0, Math.floor(c.x0 - x0)), b = Math.min(n - 1, Math.floor(c.x1 - x0));
    for (let i = a; i <= b; i++) cruza[i]++;
  }
  const tope = 0.45 * votan.length, cerca = 3 * cuerpo;
  const fin = cels.map((c) => c.x1).sort((a, b) => a - b);
  const ini = cels.map((c) => c.x0).sort((a, b) => a - b);
  const pegadaIzq = (x: number) => { let k = -1; for (let i = 0; i < fin.length; i++) { if (fin[i] <= x) k = i; else break; } return k >= 0 && x - fin[k] <= cerca; };
  const pegadaDer = (x: number) => { for (let i = 0; i < ini.length; i++) if (ini[i] >= x) return ini[i] - x <= cerca; return false; };
  const ok: boolean[] = [];
  for (let i = 0; i < n; i++)
    ok.push(cruza[i] <= tope && (cruza[i] === 0 || (pegadaIzq(x0 + i) && pegadaDer(x0 + i))));
  const cortes: number[] = dibujadas.filter((x) => x > x0 && x < x1);
  let g: number[] = [];
  for (let i = 0; i < n; i++) {
    if (ok[i]) { g.push(i); continue; }
    if (g.length >= 2) cortes.push(x0 + (g[0] + g[g.length - 1]) / 2);
    g = [];
  }
  if (g.length >= 2) cortes.push(x0 + (g[0] + g[g.length - 1]) / 2);
  const bordes = [x0, ...[...new Set(cortes.map((c) => Math.round(c * 10) / 10))].sort((a, b) => a - b), x1];
  const cols: number[][] = [];
  for (let k = 0; k < bordes.length - 1; k++) {
    const a = bordes[k], b = bordes[k + 1];
    const met = cels.filter((c) => (c.x0 + c.x1) / 2 >= a && (c.x0 + c.x1) / 2 <= b);
    if (!met.length) continue;
    cols.push([Math.max(a, Math.min(...met.map((c) => c.x0))), Math.min(b, Math.max(...met.map((c) => c.x1)))]);
  }
  return cols;
}

// Cada celda, en la columna que pisa. Y si una celda de cabecera va centrada
// sobre varias columnas libres, se estira hasta cubrirlas: es lo que hace que
// "Elementos verticales" ocupe tres columnas y no una. Solo pueden estirarse
// las filas con dos o mas celdas: si no, un texto largo se come la columna del
// ordinal de al lado.
function colocar(f: Celda[], cols: number[][], cuerpo: number): Hueca[] {
  const n = cols.length;
  const ocupa: number[][] = [];
  for (const c of f) {
    const ov: number[] = [];
    for (let i = 0; i < n; i++) {
      const sol = Math.min(cols[i][1], c.x1) - Math.max(cols[i][0], c.x0);
      if (sol > 0.3 * Math.min(cols[i][1] - cols[i][0], c.x1 - c.x0 + 0.5)) ov.push(i);
    }
    if (!ov.length) {
      let mejor = 0, d = 9e9;
      for (let i = 0; i < n; i++) { const z = Math.abs((cols[i][0] + cols[i][1]) / 2 - c.cx); if (z < d) { d = z; mejor = i; } }
      ov.push(mejor);
    }
    ocupa.push([Math.min(...ov), Math.max(...ov)]);
  }
  for (let k = 1; k < ocupa.length; k++) {
    if (ocupa[k][0] <= ocupa[k - 1][1]) ocupa[k][0] = ocupa[k - 1][1] + 1;
    if (ocupa[k][1] < ocupa[k][0]) ocupa[k][1] = ocupa[k][0];
  }
  const libre = new Array(n).fill(true);
  for (const [a, b] of ocupa) for (let i = a; i <= Math.min(b, n - 1); i++) libre[i] = false;
  if (f.length >= 2) {
    for (let k = 0; k < f.length; k++) {
      const c = f[k];
      const anclIzq = Math.abs(c.x0 - cols[Math.min(ocupa[k][0], n - 1)][0]) <= cuerpo;
      const anclDer = Math.abs(c.x1 - cols[Math.min(ocupa[k][1], n - 1)][1]) <= cuerpo;
      for (const lado of [-1, 1]) {
        if (lado < 0 && anclIzq) continue;
        if (lado > 0 && anclDer) continue;
        for (;;) {
          const i = lado < 0 ? ocupa[k][0] - 1 : ocupa[k][1] + 1;
          if (i < 0 || i >= n || !libre[i]) break;
          if (lado < 0 && k > 0 && i <= ocupa[k - 1][1]) break;
          if (lado > 0 && k + 1 < f.length && i >= ocupa[k + 1][0]) break;
          const a = Math.min(ocupa[k][0], i), b = Math.max(ocupa[k][1], i);
          const sc = (cols[a][0] + cols[b][1]) / 2;
          const centrada = Math.abs(c.cx - sc) <= Math.max(cuerpo, 0.10 * (cols[b][1] - cols[a][0]));
          const izqda = Math.abs(c.x0 - cols[a][0]) <= cuerpo;
          if (!centrada && !izqda) break;
          ocupa[k] = [a, b]; libre[i] = false;
        }
      }
    }
  }
  const fila: Hueca[] = new Array(n).fill(null);
  for (let k = 0; k < f.length; k++) {
    let a = Math.min(ocupa[k][0], n - 1); const b = Math.min(Math.max(ocupa[k][1], a), n - 1);
    if (!fila[a]) fila[a] = { t: f[k].t, cs: b - a + 1 };
    else fila[a] = { t: unir([fila[a]!.t, f[k].t]), cs: Math.max(fila[a]!.cs, b - a + 1) };
  }
  return fila;
}

// ---------------------------------------------------------------- LAS FILAS
// Si la tabla lleva rayas entre sus filas, LAS FILAS SON LAS RAYAS. Es lo que
// tenia delante y no miraba: en la Tabla 2.2 del DB-HS cada fila va recuadrada,
// y aun asi yo adivinaba las bandas por el texto, de modo que una celda escrita
// en dos renglones ("I2+I3+D1+" y "D5") se convertia en dos filas.
// La tinta manda si de verdad declara las filas: si ninguna banda se come mas
// de un tercio de la tabla. Una sola raya bajo la cabecera no declara las
// filas, separa la cabecera.
function filasPorRayas(reg: Caja, hs: Raya[], dentro: Item[][], cols: number[][], cuerpo: number):
    { rej: Hueca[][]; cab: number } | null {
  const sep = [...new Set(hs
    .filter((h) => h.a > reg.y0 + 1 && h.a < reg.y1 - 1 &&
      Math.min(h.d1, reg.x1) - Math.max(h.d0, reg.x0) >= 0.6 * (reg.x1 - reg.x0))
    .map((h) => Math.round(h.a * 10) / 10))].sort((a, b) => a - b);
  if (sep.length < 2) return null;
  const lim = [reg.y0 - 1, ...sep, reg.y1 + 1];
  let mayor = 0;
  for (let k = 0; k < lim.length - 1; k++) mayor = Math.max(mayor, lim[k + 1] - lim[k]);
  if (mayor > 0.4 * (reg.y1 - reg.y0)) return null;

  const grupos: Item[][][] = lim.slice(0, -1).map(() => []);
  for (const r of dentro) {
    const cy = (r[0].yt + Math.max(...r.map((z) => z.yb))) / 2;
    let k = 0; while (k + 1 < lim.length - 1 && cy >= lim[k + 1]) k++;
    grupos[k].push(r);
  }
  const rej: Hueca[][] = []; let cab = 0, vistos = false;
  for (let k = 0; k < grupos.length; k++) {
    const g = grupos[k];
    if (!g.length) continue;
    const fila: Hueca[] = new Array(cols.length).fill(null);
    for (const r of [...g].sort((a, b) => a[0].yt - b[0].yt)) {
      const puesta = colocar(celdas(r, hueco(r, cuerpo)), cols, cuerpo);
      for (let i = 0; i < cols.length; i++) {
        const c = puesta[i]; if (!c) continue;
        if (!fila[i]) fila[i] = { t: c.t, cs: c.cs };
        else fila[i] = { t: unir([fila[i]!.t, c.t]), cs: Math.max(fila[i]!.cs, c.cs) };
      }
    }
    rej.push(fila);
    if (!vistos && lim[k + 1] <= sep[0] + 0.5) cab++; else vistos = true;
  }
  return { rej, cab };
}

// Una FILA de tabla no es un renglon, es una BANDA. Cada fila de la tabla 2.1
// del DB-SI arrastra hasta cuatro renglones de texto largo. El renglon suelto
// se va con la banda de al lado, a su columna, en su sitio, y ENCADENADO: si el
// renglon de encima ya escribia en esa columna es su continuacion, aunque la
// banda de abajo le pille mas cerca.
function bandas(rej: Hueca[][], tops: number[], bots: number[]): { rej: Hueca[][]; idx: number[] } {
  const llenas = rej.map((f) => f.map((c, i) => (c ? i : -1)).filter((i) => i >= 0));
  const esb = rej.map((f, k) => !(llenas[k].length === 1 && f[llenas[k][0]]!.cs === 1));
  const band: number[] = []; for (let k = 0; k < rej.length; k++) if (esb[k]) band.push(k);
  if (!band.length) return { rej, idx: rej.map((_, i) => i) };
  const sep = (b: number, k: number) => (tops[k] >= tops[b] ? tops[k] - bots[b] : tops[b] - bots[k]);
  const de = new Map<number, number>();
  for (let k = 0; k < rej.length; k++) {
    if (esb[k]) { de.set(k, k); continue; }
    const c = llenas[k][0];
    const prev = k - 1;
    if (prev >= 0 && llenas[prev].includes(c) && de.has(prev)) de.set(k, de.get(prev)!);
    else {
      let mejor = band[0], d = 9e9;
      for (const b of band) { const z = sep(b, k); if (z < d) { d = z; mejor = b; } }
      de.set(k, mejor);
    }
  }
  const trozos = new Map<string, { y: number; t: string }[]>();
  for (let k = 0; k < rej.length; k++) {
    const j = de.get(k)!;
    for (const i of llenas[k]) {
      const key = j + ":" + i;
      if (!trozos.has(key)) trozos.set(key, []);
      trozos.get(key)!.push({ y: tops[k], t: rej[k][i]!.t });
      if (!rej[j][i]) rej[j][i] = { t: "", cs: rej[k][i]!.cs };
    }
  }
  for (const [key, ps] of trozos) {
    const [j, i] = key.split(":").map(Number);
    ps.sort((a, b) => a.y - b.y);
    rej[j][i]!.t = unir(ps.map((p) => p.t));
  }
  return { rej: band.map((k) => rej[k]), idx: band };
}

const ROTULO = /^\s*(Tabla|TABLA|Cuadro|CUADRO|Figura|FIGURA)\s*[\dA-Za-z]/;
const PIE_FIG = /^\s*(Fig\.|Figura|FIGURA|Imagen|Foto)\s*[\dA-Z]/;
// En el CTE un epigrafe es "3.1.2". En una ordenanza, en una ley y en casi
// todo lo demas es "Articulo 12.". Sin esto, una norma municipal entera se
// queda sin articulado: ni un titulo, ni una referencia, y sus bloques
// colgando de ningun articulo.
const TITULO = /^\s*(\d{1,3}(\.\d{1,3}){0,3}\.?\s|Artículo|ARTÍCULO|Articulo|Art\.|Anejo|ANEJO|Anexo|ANEXO|Apéndice|Capítulo|CAPÍTULO|Título|TÍTULO|Sección|SECCIÓN|Disposición|DISPOSICIÓN|Preámbulo)\b/;
// Un renglon con puntos suspensivos hasta el numero de pagina es una linea
// del indice, no un epigrafe. El indice de una ordenanza tiene sesenta.
const INDICE = /\.{4,}|(\s\.){4,}/;
const ABRE = /^\s*(\(\s*[\da-zñ]{1,4}\s*\)|\d+(\.\d+)*\s|[a-zñ]\)|[ivxlcdm]{1,4}\)|[A-Z]\)|[−–—\-•]\s)/;
const CIERRA = /[:;,.]\s*$/;
const NUMERO_EC = /\((\d+\.\d+[a-z]?)\)/;

const PALABRA_TIT = /^\s*(Artículo|ARTÍCULO|Articulo|Art\.|Anejo|ANEJO|Anexo|ANEXO|Capítulo|CAPÍTULO|Título|TÍTULO|Sección|SECCIÓN|Disposición|DISPOSICIÓN|Preámbulo)\b/;

function esTitulo(r: Item[], cuerpo: number): boolean {
  const t = texto(r).trim();
  if (!t || t.length > 95) return false;
  if (ROTULO.test(t) || INDICE.test(t)) return false;
  // "Articulo 12." se anuncia con la palabra: no hace falta que ademas vaya en
  // negrita ni mas grande, porque en media normativa municipal no lo va.
  if (PALABRA_TIT.test(t)) return true;
  // Un renglon numerado NO es un titulo por estar numerado: el CTE numera sus
  // parrafos -1, 2, 3- con la letra del cuerpo. Un titulo lo es por la LETRA:
  // negrita cuando se puede saber, y por el tamano siempre.
  const neg = r.filter((w) => w.negrita).length >= Math.max(1, r.length >> 1);
  const grande = r[0].alto > cuerpo * 1.04;
  if (TITULO.test(t) && (neg || grande)) return true;
  if (r[0].alto > cuerpo * 1.25) return true;
  if (neg && r[0].alto > cuerpo * 1.12) return true;
  return false;
}

// Entre dos rayas lejanas: hay tabla o hay prosa. La Tabla 3.4 del SE-AE solo
// lleva tres rayas y sus cinco filas quedan a 113 puntos. Dos rayas asi de
// lejos son la misma tabla solo si lo de en medio esta en columnas. Prosa es la
// linea que va de margen a margen: mirar solo el margen derecho no basta,
// porque el texto de una celda ancha tambien llega alli.
function puente(ya: number, yb: number, rens: Item[][], cuerpo: number): boolean {
  if (yb - ya > 26 * cuerpo) return false;
  const medio = rens.filter((r) => r[0].yt > ya + 2 && r[0].yt < yb - 2);
  if (!medio.length) return true;
  const der = Math.max(0, ...rens.map((r) => Math.max(...r.map((z) => z.x1))));
  const izq = Math.min(1e9, ...rens.map((r) => r[0].x0));
  let col = 0;
  for (const r of medio) {
    const t = texto(r);
    if (esTitulo(r, cuerpo) || ROTULO.test(t)) return false;
    const n = celdas(r, hueco(r, cuerpo)).length;
    if (n >= 2) col++;
    else if (Math.max(...r.map((z) => z.x1)) >= der - 1.5 * cuerpo && r[0].x0 <= izq + 3 * cuerpo) return false;
  }
  return col >= 2;
}

// ------------------------------------------------------------- LAS REGIONES
function regionesPorRayas(hs: Raya[], rens: Item[][], cuerpo: number): Caja[] {
  const out: Caja[] = []; let g: Raya[] = [];
  const cerrar = () => {
    if (g.length >= 2) {
      const x0 = Math.min(...g.map((r) => r.d0)), x1 = Math.max(...g.map((r) => r.d1));
      if (x1 - x0 >= 80 && g[g.length - 1].a - g[0].a >= 8)
        out.push({ x0, y0: g[0].a, x1, y1: g[g.length - 1].a });
    }
    g = [];
  };
  for (const r of [...hs].sort((a, b) => a.a - b.a)) {
    if (g.length) {
      // El solape se mide contra TODO lo agrupado, no contra la ultima raya:
      // dentro de la Tabla C.1 del SE-AE las rayas son de media anchura -unas
      // de la columna izquierda, otras de la derecha- y de dos en dos la tabla
      // se partia por la mitad.
      const u = { a: g[g.length - 1].a, d0: Math.min(...g.map((z) => z.d0)), d1: Math.max(...g.map((z) => z.d1)) };
      const sol = (Math.min(u.d1, r.d1) - Math.max(u.d0, r.d0)) /
                  Math.max(1, Math.min(u.d1 - u.d0, r.d1 - r.d0));
      if (sol >= 0.5 && (r.a - u.a <= 9 * cuerpo || puente(u.a, r.a, rens, cuerpo))) { g.push(r); continue; }
    }
    cerrar(); g = [r];
  }
  cerrar();
  return out;
}

// La tabla que no tiene NADA: ni rayas ni recuadros, solo alineacion. Asi esta
// la tabla 1.4.2.2 del RITE en el BOE, y asi estara cualquier ordenanza pasada
// de Word a PDF sin bordes. Tres o mas renglones seguidos partidos por huecos
// que caen en el mismo sitio; con menos de tres no se afirma nada.
function regionesPorAlineacion(rens: Item[][], cuerpo: number, ya: Caja[], izq: number, der: number): Caja[] {
  const orden = [...rens].sort((a, b) => a[0].yt - b[0].yt);
  const dentroYa = (r: Item[]) => ya.some((g) => r[0].yt >= g.y0 - 3 && r[0].yt <= g.y1 + 3);
  const out: Caja[] = [];
  let i = 0;
  while (i < orden.length) {
    const r = orden[i];
    const f = celdas(r, hueco(r, cuerpo));
    if (f.length < 2 || dentroYa(r) || esTitulo(r, cuerpo) || ROTULO.test(texto(r))) { i++; continue; }
    const cent = f.map((c) => c.cx); const grupo = [r]; let j = i + 1;
    const tol = Math.max(10, cuerpo);
    while (j < orden.length) {
      const q = orden[j];
      if (q[0].yt - Math.max(...grupo[grupo.length - 1].map((z) => z.yb)) > 1.2 * cuerpo) break;
      if (dentroYa(q) || esTitulo(q, cuerpo) || ROTULO.test(texto(q))) break;
      const g = celdas(q, hueco(q, cuerpo));
      if (g.length < 2) break;
      const casan = g.filter((c) => Math.min(...cent.map((x) => Math.abs(c.cx - x))) <= tol).length;
      if (casan < 2 || casan < 0.5 * g.length) break;
      for (const c of g) if (Math.min(...cent.map((x) => Math.abs(c.cx - x))) > tol) cent.push(c.cx);
      grupo.push(q); j++;
    }
    if (grupo.length >= 3) {
      // Prosa justificada disfrazada: estira los espacios hasta que parecen
      // huecos de columna. La delata que casi todas sus lineas llegan clavadas
      // al margen derecho, cosa que una fila de datos no hace.
      const llega = grupo.filter((q) => Math.max(...q.map((z) => z.x1)) >= der - 1.5 * cuerpo).length;
      const cols = columnas(grupo.map((q) => celdas(q, hueco(q, cuerpo))), cuerpo);
      const pasillo = cols.some((_, k) => k < cols.length - 1 && cols[k][1] < cols[k + 1][0] - 0.5 * cuerpo);
      if (llega <= 0.5 * grupo.length && cols.length >= 2 && pasillo) {
        out.push({
          x0: Math.min(...grupo.map((q) => q[0].x0)) - 2,
          y0: Math.min(...grupo.map((q) => q[0].yt)) - 2,
          x1: Math.max(...grupo.map((q) => Math.max(...q.map((z) => z.x1)))) + 2,
          y1: Math.max(...grupo.map((q) => Math.max(...q.map((z) => z.yb)))) + 2,
        });
        i = j; continue;
      }
    }
    i++;
  }
  return out;
}

function juntarRegiones(a: Caja[], b: Caja[]): Caja[] {
  const out = a.map((r) => ({ ...r }));
  for (const r of b) {
    let met = false;
    for (const o of out) {
      if (Math.min(o.x1, r.x1) - Math.max(o.x0, r.x0) > 0 && Math.min(o.y1, r.y1) - Math.max(o.y0, r.y0) > 0) {
        o.x0 = Math.min(o.x0, r.x0); o.y0 = Math.min(o.y0, r.y0);
        o.x1 = Math.max(o.x1, r.x1); o.y1 = Math.max(o.y1, r.y1); met = true; break;
      }
    }
    if (!met) out.push({ ...r });
  }
  return out;
}

// Dos regiones que se pisan, o que solo estan separadas por filas, son UNA.
function fundirRegiones(regs: Caja[], rens: Item[][], cuerpo: number): Caja[] {
  const out = regs.map((r) => ({ ...r })).sort((a, b) => a.y0 - b.y0);
  for (let vuelta = 0; vuelta < 6; vuelta++) {
    let cambio = false;
    for (let i = 0; i < out.length && !cambio; i++)
      for (let j = i + 1; j < out.length; j++) {
        const a = out[i], b = out[j];
        const anchoc = Math.min(a.x1, b.x1) - Math.max(a.x0, b.x0);
        if (anchoc < 0.5 * Math.min(a.x1 - a.x0, b.x1 - b.x0)) continue;
        const h = b.y0 - a.y1;
        if (h > 26 * cuerpo) continue;
        if (h > 0 && !puente(a.y1, b.y0, rens, cuerpo)) continue;
        out[i] = { x0: Math.min(a.x0, b.x0), y0: Math.min(a.y0, b.y0), x1: Math.max(a.x1, b.x1), y1: Math.max(a.y1, b.y1) };
        out.splice(j, 1); cambio = true; break;
      }
    if (!cambio) break;
  }
  return out;
}

const dentroDe = (it: Item, r: Caja) => {
  const cx = (it.x0 + it.x1) / 2, cy = (it.yb + it.yt) / 2;
  return cx >= r.x0 - 4 && cx <= r.x1 + 4 && cy >= r.y0 - 4 && cy <= r.y1 + 4;
};
function encaja(f: Celda[], cent: number[], tol: number): boolean {
  if (f.length < 2) return false;
  const n = f.filter((c) => Math.min(...cent.map((x) => Math.abs(c.cx - x))) <= tol).length;
  return n >= 2 && n >= 0.5 * f.length;
}

// ------------------------------------------------------------- MONTAR TABLA
function armarTabla(reg0: Caja, rens: Item[][], cuerpo: number, hs: Raya[], vs: Raya[]): Tabla | null {
  const reg: Caja = { ...reg0 };
  let dentro = rens.filter((r) => {
    const cx = (r[0].x0 + Math.max(...r.map((z) => z.x1))) / 2;
    if (ROTULO.test(texto(r))) return false;   // el rotulo es de la tabla, no una fila
    return r[0].yt >= reg.y0 - 3 && r[0].yt <= reg.y1 + 3 && cx >= reg.x0 - 5 && cx <= reg.x1 + 5;
  });
  if (dentro.length < 2) return null;
  let filas = dentro.map((r) => celdas(r, hueco(r, cuerpo)));
  if (Math.max(...filas.map((f) => f.length)) < 2) return null;

  // Para saber si una fila de abajo sigue la tabla no vale mirar UNA fila de la
  // cabecera: la plantilla es la reticula de todo el bloque.
  const vdib = vs.filter((v) => v.a > reg.x0 + 1 && v.a < reg.x1 - 1).map((v) => v.a);
  const cols0 = columnas(filas, cuerpo, vdib);
  if (cols0.length < 2) return null;
  const cent = cols0.map(([a, b]) => (a + b) / 2);
  const tol = Math.max(12, cuerpo * 1.2);

  // La tabla sigue aunque se acaben las rayas. Lo que la corta es un titulo, un
  // rotulo o PROSA; los renglones sangrados de en medio son la continuacion de
  // una celda larga, y en la tabla 2.1 del DB-SI cada fila arrastra hasta tres.
  const izqP = Math.min(1e9, ...rens.map((r) => r[0].x0));
  const derP = Math.max(0, ...rens.map((r) => Math.max(...r.map((z) => z.x1))));
  const cola = rens.filter((r) => r[0].yt > reg.y1 + 3).sort((a, b) => a[0].yt - b[0].yt);
  let ult = Math.max(...dentro[dentro.length - 1].map((z) => z.yb));
  let pend: { r: Item[]; f: Celda[] }[] = [], fallos = 0;
  for (const r of cola) {
    if (r[0].yt - ult > 4.5 * cuerpo) break;
    const f = celdas(r, hueco(r, cuerpo));
    if (encaja(f, cent, tol)) {
      for (const p of pend) { dentro.push(p.r); filas.push(p.f); reg.y1 = Math.max(reg.y1, Math.max(...p.r.map((z) => z.yb))); }
      pend = []; fallos = 0;
      dentro.push(r); filas.push(f); reg.y1 = Math.max(reg.y1, Math.max(...r.map((z) => z.yb)));
    } else {
      const t = texto(r);
      if (esTitulo(r, cuerpo) || ROTULO.test(t) || PIE_FIG.test(t)) break;
      if (Math.max(...r.map((z) => z.x1)) >= derP - 1.5 * cuerpo && r[0].x0 <= izqP + 3 * cuerpo) break;
      if (++fallos > 6) break;
      pend.push({ r, f });
    }
    ult = Math.max(...r.map((z) => z.yb));
  }
  dentro = dentro.sort((a, b) => a[0].yt - b[0].yt);
  filas = dentro.map((r) => celdas(r, hueco(r, cuerpo)));

  const cols = columnas(filas, cuerpo, vs.filter((v) => v.a > reg.x0 + 1 && v.a < reg.x1 - 1 &&
    Math.min(v.d1, reg.y1) - Math.max(v.d0, reg.y0) >= 0.6 * (reg.y1 - reg.y0)).map((v) => v.a));
  if (cols.length < 2) return null;

  let rej: Hueca[][]; let cab = 1;
  const porRayas = filasPorRayas(reg, hs, dentro, cols, cuerpo);
  if (porRayas) { rej = porRayas.rej; cab = porRayas.cab; }
  else {
    const puestas = filas.map((f) => colocar(f, cols, cuerpo));
    const b = bandas(puestas, dentro.map((r) => r[0].yt), dentro.map((r) => Math.max(...r.map((z) => z.yb))));
    rej = b.rej;
    const raya = hs.filter((h) => h.a > reg.y0 + 1 && h.a < reg.y1 - 1 &&
      Math.min(h.d1, reg.x1) - Math.max(h.d0, reg.x0) >= 0.6 * (reg.x1 - reg.x0)).map((h) => h.a);
    cab = raya.length
      ? b.idx.filter((k) => Math.max(...dentro[k].map((z) => z.yb)) <= Math.min(...raya)).length
      : 1;
  }
  cab = Math.min(cab, 6, Math.max(1, Math.floor(rej.length / 3)));
  if (!rej.length) return null;

  // Un parrafo con una caja alrededor no es una tabla: Word usa tablas sin
  // bordes para maquetar, y en esas "filas" solo hay una celda con un parrafo
  // entero dentro.
  let solas = 0;
  for (const f of rej) {
    const ll = f.filter((c) => c);
    if (ll.length === 1 && ll[0]!.t.length > 60) solas++;
  }
  if (solas >= 0.5 * rej.length) return null;

  return { reg, cols, filas: rej, usados: dentro.flat(), cabecera: Math.max(0, Math.min(cab, rej.length - 1)),
           rotulo: null, lateral: [] };
}

const mismasColumnas = (a: Tabla, b: Tabla, cuerpo: number) => {
  const ca = a.cols.map(([x, y]) => (x + y) / 2), cb = b.cols.map(([x, y]) => (x + y) / 2);
  if (ca.length < 2 || cb.length < 2) return false;
  const tol = Math.max(12, cuerpo * 1.5);
  return cb.filter((c) => Math.min(...ca.map((z) => Math.abs(c - z))) <= tol).length >= 0.6 * cb.length;
};

// Una tabla crece hacia abajo mientras haya filas, y al crecer puede alcanzar a
// la region de mas abajo. Entonces son la misma: se funden las regiones y se
// vuelve a montar, en vez de coser dos tablas ya hechas.
function armarTablas(regs: Caja[], rens: Item[][], cuerpo: number, hs: Raya[], vs: Raya[],
                     dibujo: (r: Caja) => boolean, blandas: Caja[]): { tablas: Tabla[]; figuras: Caja[] } {
  const tablas: Tabla[] = [], figuras: Caja[] = [];
  const gastados = new Set<Item>();
  const clave = (r: Caja) => [r.x0, r.y0, r.x1, r.y1].map((v) => Math.round(v)).join(",");
  const blandaSet = new Set(blandas.map(clave));
  for (const reg of [...regs].sort((a, b) => a.y0 - b.y0)) {
    const blanda = blandaSet.has(clave(reg));
    if (!blanda && dibujo(reg)) { figuras.push({ ...reg }); continue; }
    const t = armarTabla(reg, rens, cuerpo, hs, vs);
    if (!t) continue;                       // si no cuaja, se deja estar
    const nuevos = t.usados.filter((it) => !gastados.has(it));
    if (nuevos.length < 0.4 * t.usados.length) continue;
    for (const it of t.usados) gastados.add(it);
    tablas.push(t);
  }
  for (let vuelta = 0; vuelta < 3; vuelta++) {
    let fundida = false;
    for (let i = 0; i < tablas.length && !fundida; i++)
      for (let j = i + 1; j < tablas.length; j++) {
        const a = tablas[i].reg, b = tablas[j].reg;
        const anchoc = Math.min(a.x1, b.x1) - Math.max(a.x0, b.x0);
        if (anchoc < 0.5 * Math.min(a.x1 - a.x0, b.x1 - b.x0)) continue;
        const h = Math.max(a.y0, b.y0) - Math.min(a.y1, b.y1);
        if (h > 26 * cuerpo) continue;
        if (h > 0 && !puente(Math.min(a.y1, b.y1), Math.max(a.y0, b.y0), rens, cuerpo)) continue;
        if (!mismasColumnas(tablas[i], tablas[j], cuerpo)) continue;
        const reg = { x0: Math.min(a.x0, b.x0), y0: Math.min(a.y0, b.y0), x1: Math.max(a.x1, b.x1), y1: Math.max(a.y1, b.y1) };
        const nueva = armarTabla(reg, rens, cuerpo, hs, vs);
        if (!nueva) continue;
        nueva.rotulo = tablas[i].rotulo ?? tablas[j].rotulo;
        tablas[i] = nueva; tablas.splice(j, 1); fundida = true; break;
      }
    if (!fundida) break;
  }
  return { tablas, figuras };
}

// Una tabla que se acaba en el pie y otra que empieza en la cabeza de la pagina
// siguiente, con las mismas columnas, son LA MISMA TABLA. La Tabla 2.1 del
// DB-SI ocupa pagina y media y en la segunda no se repite la cabecera: quien
// lee la continuacion no sabe que esas tres columnas son riesgo bajo, medio y
// alto. Se le presta la cabecera de la primera.
function enlazar(ant: Tabla | null, act: Tabla | null, H: number, cuerpo: number): boolean {
  if (!ant || !act) return false;
  if (ant.reg.y1 < 0.84 * H || act.reg.y0 > 0.22 * H) return false;
  if (!mismasColumnas(ant, act, cuerpo)) return false;
  const cab = ant.filas.slice(0, ant.cabecera);
  if (cab.length) {
    act.filas = cab.map((f) => f.map((c) => (c ? { ...c } : null))).concat(act.filas);
    act.cabecera = cab.length;
  }
  act.rotulo = (act.rotulo ?? ant.rotulo ?? "") + " (continuación)";
  if (!act.lateral.length) act.lateral = [...ant.lateral];
  return true;
}

// ------------------------------------------------------------- LAS FORMULAS
// Word exporta las ecuaciones en piezas: el numerador por un lado, el
// denominador por otro, los corchetes grandes en glifos aparte. Leidas como
// parrafos salen cosas como "]" o "1 0,055(3 +psi)", que no dicen nada y ademas
// mienten. Se juntan las piezas vecinas y se guarda el TROZO DE PAGINA: una
// formula se ve, no se cuenta.
const MATE = new Set([..."∑∏√∫≤≥≠±×÷≈≡∂∇∞αβγδεζηθλμνξπρστφχψωΔΣΩΦ"]);
const huerfano = (r: Item[]) => { const t = texto(r).trim(); return t.length > 0 && t.length <= 3 && !ABRE.test(t); };
function esMate(r: Item[], cuerpo: number): boolean {
  const t = texto(r).trim();
  if (!t) return false;
  if (CIERRA.test(t) && t.length > 12) return false;
  if (esTitulo(r, cuerpo)) return false;
  if ([...t].some((c) => MATE.has(c))) return true;
  if (t.includes("=") && t.length < 70) return true;
  if (t.length <= 10 && !CIERRA.test(t)) return true;
  return false;
}
function formulas(rens: Item[][], cuerpo: number): { lineas: Item[][]; reg: Caja; pie: string | null }[] {
  const orden = [...rens].sort((a, b) => a[0].yt - b[0].yt);
  const out: { lineas: Item[][]; reg: Caja; pie: string | null }[] = [];
  const sigue = (r: Item[]) => {
    const t = texto(r).trim();
    return esMate(r, cuerpo) || huerfano(r) || (t.length < 45 && !CIERRA.test(t) && !ABRE.test(t));
  };
  let i = 0;
  while (i < orden.length) {
    if (!(esMate(orden[i], cuerpo) || huerfano(orden[i]))) { i++; continue; }
    let j = i;
    while (j + 1 < orden.length &&
           orden[j + 1][0].yt - Math.max(...orden[j].map((z) => z.yb)) <= 0.9 * cuerpo &&
           sigue(orden[j + 1])) j++;
    while (i > 0 && orden[i][0].yt - Math.max(...orden[i - 1].map((z) => z.yb)) <= 0.9 * cuerpo &&
           sigue(orden[i - 1]) && !out.some((b) => b.lineas.includes(orden[i - 1]))) i--;
    const grupo = orden.slice(i, j + 1);
    const corto = grupo.some((r) => huerfano(r) || texto(r).trim().length <= 10);
    const simbolo = grupo.some((r) => { const t = texto(r); return [...t].some((c) => MATE.has(c)) || t.includes("=") || NUMERO_EC.test(t); });
    if (grupo.length >= 2 && corto && simbolo) {
      const m = NUMERO_EC.exec(grupo.map((r) => texto(r)).join(" "));
      out.push({
        lineas: grupo,
        reg: {
          x0: Math.min(...grupo.map((r) => r[0].x0)) - 4,
          y0: Math.min(...grupo.map((r) => r[0].yt)) - 3,
          x1: Math.max(...grupo.map((r) => Math.max(...r.map((z) => z.x1)))) + 4,
          y1: Math.max(...grupo.map((r) => Math.max(...r.map((z) => z.yb)))) + 3,
        },
        pie: m ? "Fórmula (" + m[1] + ")" : null,
      });
    }
    i = j + 1;
  }
  return out;
}

// Los rotulos de un grafico son parte del grafico: los ejes, la leyenda y la
// escala. Si no se los queda la figura, salen sueltos por el documento como
// parrafos de dos letras.
function engordarFiguras(figs: Caja[], rens: Item[][], cuerpo: number): Caja[] {
  const out = figs.map((f) => ({ ...f }));
  for (let vuelta = 0; vuelta < 6; vuelta++) {
    let cambio = false;
    for (const f of out) {
      for (const r of rens) {
        const t = texto(r).trim();
        if (!t) continue;
        const tk = t.split(/\s+/);
        const cifras = tk.filter((z) => /^[-+]?\d+[.,]?\d*$/.test(z)).length;
        if (t.length > 60 && cifras < 0.6 * tk.length) continue;
        if (PIE_FIG.test(t) || ROTULO.test(t) || esTitulo(r, cuerpo)) continue;
        const rx1 = Math.max(...r.map((z) => z.x1)), ryb = Math.max(...r.map((z) => z.yb));
        const ancho = Math.max(1, rx1 - r[0].x0);
        if (Math.min(f.x1, rx1) - Math.max(f.x0, r[0].x0) < 0.6 * ancho) continue;
        const dv = Math.max(f.y0 - ryb, r[0].yt - f.y1);
        if (dv > 1.6 * cuerpo) continue;
        const n = { x0: Math.min(f.x0, r[0].x0), y0: Math.min(f.y0, r[0].yt), x1: Math.max(f.x1, rx1), y1: Math.max(f.y1, ryb) };
        if (n.x0 !== f.x0 || n.y0 !== f.y0 || n.x1 !== f.x1 || n.y1 !== f.y1) {
          f.x0 = n.x0; f.y0 = n.y0; f.x1 = n.x1; f.y1 = n.y1; cambio = true;
        }
      }
    }
    if (!cambio) break;
  }
  return out;
}

// Una pagina no tiene dieciocho figuras.
//
// manchas() encuentra cada borron de tinta por separado, y en una norma
// escaneada eso son veinte trozos del mismo dibujo. Subir un PNG por cada uno
// costaba veinte segundos por pagina -el motor tarda ciento cincuenta
// milisegundos- y ademas partia la figura en cachos para quien la lee.
// Lo que va junto, va junto; y si la pagina es casi toda dibujo, la figura es
// la pagina.
function juntarFiguras(figs: Caja[], W: number, H: number, cuerpo: number): Caja[] {
  const out = figs.map((f) => ({ ...f }));
  const G = 2 * cuerpo;
  for (let vuelta = 0; vuelta < 8; vuelta++) {
    let cambio = false;
    for (let i = 0; i < out.length && !cambio; i++)
      for (let j = i + 1; j < out.length; j++) {
        const a = out[i], b = out[j];
        if (a.x0 > b.x1 + G || b.x0 > a.x1 + G || a.y0 > b.y1 + G || b.y0 > a.y1 + G) continue;
        out[i] = { x0: Math.min(a.x0, b.x0), y0: Math.min(a.y0, b.y0),
                   x1: Math.max(a.x1, b.x1), y1: Math.max(a.y1, b.y1) };
        out.splice(j, 1); cambio = true; break;
      }
    if (!cambio) break;
  }
  // Y si lo que queda ocupa casi toda la hoja, NO es una figura: es la hoja.
  // Las normas escaneadas son una imagen por pagina, y recortarla y subirla era
  // volver a guardar el documento entero -seis megas por pagina- para enseñar
  // lo mismo que ya enseña el recorte de hoja. De ahi los veinte segundos por
  // pagina: no se estaba pensando, se estaba subiendo.
  const grandes = out.filter((f) => (f.x1 - f.x0) * (f.y1 - f.y0) > 0.45 * W * H);
  const resto = out.filter((f) => (f.x1 - f.x0) * (f.y1 - f.y0) <= 0.45 * W * H);
  if (grandes.length) return [];
  if (resto.length <= 6) return resto;
  return resto.sort((a, b) => (b.x1 - b.x0) * (b.y1 - b.y0) - (a.x1 - a.x0) * (a.y1 - a.y0)).slice(0, 6);
}

// --------------------------------------------------------------- PARRAFOS --
// El corte lo manda la SANGRIA de la SEGUNDA linea, no el margen derecho: la
// primera linea lleva la numeracion o la llamada volada. El margen solo corta
// si la linea anterior se queda muy corta.
type Parrafo = { y: number; txt: string; x0: number; x1: number; yb: number; sangria: number | null };
function coser(rens: Item[][], cuerpo: number, margenes: Map<Item[], [number, number]>):
    { y: number; clase: string; txt: string }[] {
  const out: { y: number; clase: string; txt: string }[] = [];
  let ab: Parrafo | null = null;
  const cerrar = () => { if (ab) { out.push({ y: ab.y, clase: "parrafo", txt: ab.txt }); ab = null; } };
  for (const r of rens) {
    const t = texto(r).trim();
    if (!t) continue;
    if (esTitulo(r, cuerpo)) { cerrar(); out.push({ y: r[0].yt, clase: "titulo", txt: t }); continue; }
    const x1 = Math.max(...r.map((z) => z.x1)), yb = Math.max(...r.map((z) => z.yb));
    let corta = true;
    if (ab) {
      const [izq, der] = margenes.get(r) ?? [r[0].x0, ab.x1];
      const corto = ab.x1 < der - Math.max(cuerpo * 1.5, 0.12 * (der - izq));
      const sangria = ab.sangria !== null && Math.abs(r[0].x0 - ab.sangria) > 2;
      corta = corto || sangria || ABRE.test(t) || (r[0].yt - ab.yb > cuerpo * 1.1);
    }
    if (corta) { cerrar(); ab = { y: r[0].yt, txt: t, x0: r[0].x0, x1, yb, sangria: null }; }
    else if (ab) {
      ab.txt = /[-­]$/.test(ab.txt) && /^[a-zà-ÿ]/.test(t)
        ? ab.txt.replace(/[-­]$/, "") + t : unir([ab.txt, t]);
      ab.x1 = x1; ab.yb = yb;
      if (ab.sangria === null) ab.sangria = r[0].x0;
    }
  }
  cerrar();
  return out;
}
function margenesLocales(rens: Item[][], cuerpo: number): Map<Item[], [number, number]> {
  const m = new Map<Item[], [number, number]>();
  for (const r of rens) {
    const y = r[0].yt;
    const cerca = rens.filter((q) => Math.abs(q[0].yt - y) <= 5 * cuerpo);
    const g = cerca.length ? cerca : [r];
    m.set(r, [Math.min(...g.map((q) => q[0].x0)), Math.max(...g.map((q) => Math.max(...q.map((z) => z.x1))))]);
  }
  return m;
}

// ------------------------------------------------------- TINTA QUE SOBRA ---
// Lo que separa una tabla de un dibujo: se tapan las rayas y las cajas de texto
// y se cuenta lo que queda. Tabla 3.1 del SE-AE: 0,03%. Dibujo del viento: 10%.
function tintaQueSobra(d: Uint8Array, W: number, H: number, reg: Caja, hs: Raya[], vs: Raya[], items: Item[]): number {
  const x0 = Math.max(0, Math.floor(reg.x0)), x1 = Math.min(W, Math.ceil(reg.x1));
  const y0 = Math.max(0, Math.floor(reg.y0)), y1 = Math.min(H, Math.ceil(reg.y1));
  const w = x1 - x0, h = y1 - y0;
  if (w <= 0 || h <= 0) return 1;
  const tapa = new Uint8Array(w * h);
  const pinta = (a0: number, b0: number, a1: number, b1: number) => {
    for (let y = Math.max(y0, Math.floor(b0)); y < Math.min(y1, Math.ceil(b1)); y++)
      for (let x = Math.max(x0, Math.floor(a0)); x < Math.min(x1, Math.ceil(a1)); x++)
        tapa[(y - y0) * w + (x - x0)] = 1;
  };
  for (const r of hs) if (r.a >= y0 - 4 && r.a <= y1 + 4) pinta(r.d0 - 3, r.a - 3, r.d1 + 3, r.a + 4);
  for (const r of vs) if (r.a >= x0 - 4 && r.a <= x1 + 4) pinta(r.a - 3, r.d0 - 3, r.a + 4, r.d1 + 3);
  for (const it of items) pinta(it.x0 - 2, it.yt - 2, it.x1 + 2, it.yb + 2);
  let sobra = 0;
  for (let y = y0; y < y1; y++)
    for (let x = x0; x < x1; x++)
      if (!tapa[(y - y0) * w + (x - x0)] && lum(d, (y * W + x) * 4) < TINTA) sobra++;
  return sobra / (w * h);
}

// Un dibujo no tiene por que llevar rayas: la Fig. 3.1 del SE-AE son 396 curvas
// y hasta sus rotulos son trazos, no texto. Se buscan manchas de tinta.
function manchas(d: Uint8Array, W: number, H: number, tapar: Caja[]): Caja[] {
  const C = 8, cx = Math.ceil(W / C), cy = Math.ceil(H / C);
  const t = new Uint8Array(cx * cy);
  for (let y = 0; y < H; y++) { const f = Math.floor(y / C) * cx;
    for (let x = 0; x < W; x++) if (lum(d, (y * W + x) * 4) < 232) t[f + Math.floor(x / C)] = 1; }
  for (const c of tapar)
    for (let j = Math.max(0, Math.floor(c.y0 / C)); j <= Math.min(cy - 1, Math.floor(c.y1 / C)); j++)
      for (let i = Math.max(0, Math.floor(c.x0 / C)); i <= Math.min(cx - 1, Math.floor(c.x1 / C)); i++) t[j * cx + i] = 0;
  const visto = new Uint8Array(cx * cy); const out: Caja[] = []; const pila: number[] = [];
  for (let k = 0; k < t.length; k++) {
    if (!t[k] || visto[k]) continue;
    pila.length = 0; pila.push(k); visto[k] = 1;
    let i0 = cx, i1 = 0, j0 = cy, j1 = 0;
    while (pila.length) {
      const p = pila.pop()!; const i = p % cx, j = (p - i) / cx;
      if (i < i0) i0 = i; if (i > i1) i1 = i; if (j < j0) j0 = j; if (j > j1) j1 = j;
      for (let dj = -1; dj <= 1; dj++) for (let di = -1; di <= 1; di++) {
        const a = i + di, b = j + dj;
        if (a < 0 || b < 0 || a >= cx || b >= cy) continue;
        const q = b * cx + a; if (t[q] && !visto[q]) { visto[q] = 1; pila.push(q); }
      }
    }
    const caja = { x0: i0 * C, y0: j0 * C, x1: (i1 + 1) * C, y1: (j1 + 1) * C };
    if (caja.x1 - caja.x0 >= MIN_FIG && caja.y1 - caja.y0 >= MIN_FIG) out.push(caja);
  }
  return out;
}

const NUM = /^(\d{1,3}(?:\.\d{1,3}){0,3})\.?\s+(.{2,140})$/;
const ART = /^(?:artículo|articulo|art\.)\s*(\d+[a-z]?(?:\.\d+)*)\.?[\s–—-]*(.{0,140})$/i;
const CAP = /^(capítulo|título|sección|anexo|anejo|disposición\s+\w+)\s+([\dIVXLC]+[a-z]?)\.?[\s–—-]*(.{0,140})$/i;
const ANEJO = /^(anejo|anexo)\s+([A-Z0-9]+(?:\.[0-9]+)*)\.?\s*(.{0,120})$/i;
const llano = (s: string) => s.normalize("NFD").replace(/[̀-ͯ]/g, "").toLowerCase().replace(/[^a-z0-9]/g, "");


// ============================================================ TRABAJADOR ===

const PUERTA = Deno.env.get("TRAMITFLOW_PUERTA_HOJAS") ??
  "https://iqskiegwxucfuimnnoiu.supabase.co/functions/v1/pf-trabajador-hojas";
const CLAVE = Deno.env.get("TRABAJADOR_CLAVE") ?? "";
const UA = "Mozilla/5.0 (compatible; TramitFlow-externo/1.0; +https://kolven.es)";
const INICIO = Date.now();
const HASTA = INICIO + Number(Deno.env.get("ESTRUCTURA_MIN") ?? "150") * 60000;
const MAX_PAG = Number(Deno.env.get("MAX_PAGINADO") ?? "3");
const MAX_BLQ = Number(Deno.env.get("MAX_BLOQUES") ?? "2");
const PDF_MAX_EXT = 300 * 1024 * 1024;
const TROZO = 40;          // paginas que se leen juntas para el marco y el cuerpo del documento
const AGUJA = 70;          // pf-paginar-norma: letras del trozo con el que se busca
const AGUJA_MIN = 28;
const SALTO_CABECERA = 30;

const log = (...a: unknown[]) =>
  console.log("[" + Math.round((Date.now() - INICIO) / 1000) + " s]", ...a);

class PuertaNoDisponible extends Error {}

async function puerta(cuerpo: Record<string, unknown>): Promise<Record<string, unknown>> {
  let ultimo = "";
  for (const espera of [0, 20, 60, 120]) {
    if (espera) { log("   puerta:", ultimo.slice(0, 160), "-> reintento en", espera, "s"); await new Promise((r) => setTimeout(r, espera * 1000)); }
    try {
      const r = await fetch(PUERTA, {
        method: "POST",
        headers: { "Content-Type": "application/json", "x-trabajador-clave": CLAVE },
        body: JSON.stringify(cuerpo),
        signal: AbortSignal.timeout(180000),
      });
      const txt = await r.text();
      if (r.ok) return JSON.parse(txt || "{}");
      ultimo = "puerta " + r.status + ": " + txt.slice(0, 400);
      if (r.status < 500) throw new Error(ultimo);   // 400/401: repetir no lo arregla
    } catch (e) {
      if ((e as Error).message.startsWith("puerta 4")) throw e;
      ultimo = ultimo || "puerta sin respuesta: " + (e as Error).message;
    }
  }
  throw new PuertaNoDisponible(ultimo);
}

async function bajar(url: string): Promise<Uint8Array> {
  let ultimo = "";
  for (const espera of [0, 15, 60]) {
    if (espera) await new Promise((r) => setTimeout(r, espera * 1000));
    try {
      const r = await fetch(url, { headers: { "User-Agent": UA }, signal: AbortSignal.timeout(300000) });
      if (!r.ok) {
        ultimo = "descarga HTTP " + r.status;
        if (r.status < 500 && r.status !== 429) break;
        continue;
      }
      const bytes = new Uint8Array(await r.arrayBuffer());
      if (bytes.length > PDF_MAX_EXT) throw new Error("PDF de " + Math.round(bytes.length / 1048576) + " MB");
      if (!(bytes[0] === 0x25 && bytes[1] === 0x50 && bytes[2] === 0x44 && bytes[3] === 0x46))
        throw new Error("la descarga no es un PDF");
      return bytes;
    } catch (e) {
      ultimo = (e as Error).message;
      if (/no es un PDF|MB$/.test(ultimo)) break;
    }
  }
  throw new Error(ultimo || "descarga sin respuesta");
}

// ------------------------------------------------------------- PAGINADO -----
// Identico a pf-paginar-norma: tira de letras y numeros por pagina, aguja metida
// en el cuerpo del articulo, busqueda monotona y final por el ultimo trozo.
function tira(s: string): string {
  return s.normalize("NFD").replace(/[̀-ͯ]/g, "").toLowerCase().replace(/[^a-z0-9]/g, "");
}

type ArtPag = { id: string; referencia: string | null; texto: string | null };

async function paginarDoc(d: { instrumento_id: string; descarga: string; articulos: ArtPag[] }) {
  const iid = d.instrumento_id;
  const t0 = Date.now();
  let pdf: Awaited<ReturnType<typeof getDocumentProxy>> | null = null;
  try {
    const articulos = d.articulos ?? [];
    if (articulos.length === 0) {
      log("paginado", iid, "sin articulado con texto");
      await puerta({ modo: "pag_hecho", instrumento_id: iid, filas: [] });
      return;
    }
    const bytes = await bajar(d.descarga);
    pdf = await getDocumentProxy(bytes);
    const total = pdf.numPages;
    const paginas: string[] = [];
    for (let p = 1; p <= total; p++) {
      try {
        const tc = await (await pdf.getPage(p)).getTextContent();
        paginas.push(tira((tc.items as Array<Record<string, unknown>>)
          .map((it) => (typeof it.str === "string" ? it.str : "")).join("")));
      } catch {
        paginas.push("");
      }
    }
    const aguja = (texto: string): string => {
      const t = tira(texto);
      if (t.length < AGUJA_MIN) return "";
      const desde = t.length > SALTO_CABECERA + AGUJA_MIN ? SALTO_CABECERA : 0;
      return t.slice(desde, desde + AGUJA);
    };
    const agujaFinal = (texto: string): string => {
      const t = tira(texto);
      if (t.length < AGUJA_MIN) return "";
      return t.slice(Math.max(0, t.length - AGUJA));
    };
    const buscar = (needle: string, desde: number): number => {
      if (!needle) return -1;
      for (let q = desde; q < paginas.length; q++) if (paginas[q].includes(needle)) return q;
      for (let q = 0; q < desde; q++) if (paginas[q].includes(needle)) return q;
      return -1;
    };
    const salida: { id: string; ini: number; fin: number }[] = [];
    let cursor = 0, sinCasar = 0;
    for (const a of articulos) {
      const ini = buscar(aguja(a.texto ?? ""), cursor);
      if (ini < 0) { sinCasar++; continue; }
      const finBusc = buscar(agujaFinal(a.texto ?? ""), ini);
      const fin = finBusc >= ini ? finBusc : ini;
      cursor = ini;
      salida.push({ id: a.id, ini: ini + 1, fin: fin + 1 });
    }
    const res = await puerta({ modo: "pag_hecho", instrumento_id: iid, filas: salida });
    log("paginado", iid, total, "paginas,", articulos.length, "articulos,", salida.length, "paginados,",
        sinCasar, "sin casar,", Math.round((Date.now() - t0) / 1000), "s ->", JSON.stringify(res).slice(0, 120));
  } catch (e) {
    if (e instanceof PuertaNoDisponible) throw e;
    const msg = (e as Error).message.slice(0, 250);
    log("paginado", iid, "error:", msg);
    await puerta({ modo: "pag_hecho", instrumento_id: iid, filas: [], error: msg });
  } finally {
    try { await pdf?.destroy(); } catch { /* da igual */ }
  }
}

// -------------------------------------------------------------- BLOQUES -----
type ArtBlq = { id: string; referencia: string | null; pagina_ini: number | null; pagina_fin: number | null };

async function bloquesDoc(d: { instrumento_id: string; descarga: string; desde: number; articulos: ArtBlq[] }) {
  const iid = d.instrumento_id;
  const t0 = Date.now();
  let lib: { destroy: () => void } | null = null;
  let pdf: Awaited<ReturnType<typeof getDocumentProxy>> | null = null;
  try {
    const arts = d.articulos ?? [];
    const porRef = new Map<string, string>();
    for (const a of arts) if (a.referencia) porRef.set(llano(a.referencia), a.id);
    const porPagina = (p: number): string | null => {
      let mejor: string | null = null, ancho = Infinity;
      for (const a of arts) {
        if (a.pagina_ini == null || (a.referencia ?? "") === "Texto completo") continue;
        const fin = a.pagina_fin ?? a.pagina_ini;
        if (a.pagina_ini > p || fin < p) continue;
        if (fin - a.pagina_ini < ancho) { ancho = fin - a.pagina_ini; mejor = a.id; }
      }
      return mejor;
    };

    const bytes = await bajar(d.descarga);
    pdf = await getDocumentProxy(bytes.slice());
    lib = await PDFiumLibrary.init() as unknown as { destroy: () => void };
    // deno-lint-ignore no-explicit-any
    const pdfium = await (lib as any).loadDocument(bytes);
    const total = pdf.numPages;

    let refActual: string | null = null;
    let anterior: Tabla | null = null;
    let nTablas = 0, nIlegibles = 0, nFiguras = 0, nFormulas = 0, nParrafos = 0, nTitulos = 0, nContinuadas = 0;
    let desde = Math.max(1, Number(d.desde ?? 1));
    log("bloques", iid, "desde la", desde, "de", total);

    while (desde <= total) {
      if (Date.now() > HASTA) {
        log("   tope de tiempo en la pagina", desde, "de", total, ": sigue en la proxima pasada");
        await puerta({ modo: "blq_hecho", instrumento_id: iid, soltar: true });
        return;
      }
      const hasta = Math.min(desde + TROZO - 1, total);

      // PRIMERA PASADA, solo texto (como en el edge): el marco y el cuerpo son del DOCUMENTO.
      const leerPagina = async (p: number) => {
        const page = await pdf!.getPage(p);
        const vp = page.getViewport({ scale: 1 });
        const tc = await page.getTextContent();
        // deno-lint-ignore no-explicit-any
        const co = (page as any).commonObjs;
        const nombreFuente = (id: string): string => {
          try { const f = co?.get?.(id); return String(f?.name ?? f?.loadedName ?? id); }
          catch { return id; }
        };
        const brutos: Item[] = (tc.items as Array<Record<string, unknown>>)
          .filter((it) => typeof it.str === "string" && (it.str as string).trim() !== "")
          .map((it) => {
            const t = it.transform as number[];
            const alto = Math.abs(Number(it.height ?? 0)) || Math.abs(t[3]) || 10;
            const anc = Number(it.width ?? 0);
            const fn = nombreFuente(String(it.fontName ?? ""));
            const recta = Math.abs(t[1]) < 0.15 && Math.abs(t[2]) < 0.15;
            return {
              s: descifrar((it.str as string).trim(), fn),
              x0: t[4] * ESCALA, x1: (t[4] + anc) * ESCALA,
              yb: (vp.height - t[5]) * ESCALA, yt: (vp.height - t[5] - alto) * ESCALA,
              alto: alto * ESCALA, negrita: /bold|negri|black|semib/i.test(fn), recta,
            };
          })
          .filter((it) => it.s !== "");
        const { rectas, giradas } = separarGiradas(brutos);
        return { vp, rectas: fundirIndices(rectas), giradas };
      };

      const cache = new Map<number, { vp: { width: number; height: number }; rectas: Item[]; giradas: (Caja & { texto: string })[] }>();
      const lineas = new Map<number, Item[][]>();
      const cuentaAlto = new Map<number, number>();
      for (let p = desde; p <= hasta; p++) {
        const dd = await leerPagina(p);
        cache.set(p, dd);
        lineas.set(p, renglones(dd.rectas));
        for (const it of dd.rectas) {
          const a = Math.round(it.alto * 2) / 2;
          cuentaAlto.set(a, (cuentaAlto.get(a) ?? 0) + it.s.length);
        }
      }
      let CUERPO = 10 * ESCALA, mejorN = 0;
      for (const [a, n] of cuentaAlto) if (n > mejorN) { mejorN = n; CUERPO = a; }
      const H0 = (cache.get(desde)?.vp.height ?? 842) * ESCALA;
      const MARCO = marcoDelDocumento(lineas, H0, hasta - desde + 1);

      for (let p = desde; p <= hasta; p++) {
        const cab = cache.get(p)!;
        const H = Math.round(cab.vp.height * ESCALA);
        // deno-lint-ignore no-explicit-any
        const img = await (pdfium as any).getPage(p - 1).render({ scale: ESCALA, render: "bitmap" });
        const datos = img.data as Uint8Array;
        const Wr = img.width as number, Hr = img.height as number;

        const rens = (lineas.get(p) ?? []).filter((r) => !esMarco(r, H, MARCO));
        const hs = rayasH(datos, Wr, Hr), vs = rayasV(datos, Wr, Hr);
        const izq = Math.min(1e9, ...rens.map((rr) => rr[0].x0));
        const der = Math.max(0, ...rens.map((rr) => Math.max(...rr.map((z) => z.x1))));

        let regs = regionesPorRayas(hs, rens, CUERPO);
        const ali = regionesPorAlineacion(rens, CUERPO, regs, izq, der);
        regs = fundirRegiones(juntarRegiones(regs, ali), rens, CUERPO);

        const esDibujo = (reg: Caja) =>
          tintaQueSobra(datos, Wr, Hr, reg, hs, vs, rens.flat().filter((it) => dentroDe(it, reg))) > SOBRA_MAX;
        const { tablas, figuras: figReg } = armarTablas(regs, rens, CUERPO, hs, vs, esDibujo, ali);

        const usados = new Set<Item>();
        for (const t of tablas) for (const it of t.usados) usados.add(it);

        for (const t of tablas) {
          const arr = rens.filter((rr) => ROTULO.test(texto(rr)) && t.reg.y0 - Math.max(...rr.map((z) => z.yb)) > 0 && t.reg.y0 - Math.max(...rr.map((z) => z.yb)) < 34 * ESCALA);
          const aba = rens.filter((rr) => ROTULO.test(texto(rr)) && rr[0].yt - t.reg.y1 > 0 && rr[0].yt - t.reg.y1 < 34 * ESCALA);
          const cand = arr.length ? arr[arr.length - 1] : (aba.length ? aba[0] : null);
          if (cand && !t.rotulo) { t.rotulo = texto(cand); for (const z of cand) usados.add(z); }
        }
        for (const g of cab.giradas) {
          for (const t of tablas) {
            if (Math.min(g.x1, t.reg.x1) - Math.max(g.x0, t.reg.x0) > 0 &&
                Math.min(g.y1, t.reg.y1) - Math.max(g.y0, t.reg.y0) > 0) { t.lateral.push(g.texto); break; }
          }
        }

        if (tablas.length) {
          const primera = [...tablas].sort((a, c) => a.reg.y0 - c.reg.y0)[0];
          if (enlazar(anterior, primera, H, CUERPO)) nContinuadas++;
        }

        const libres = rens.filter((rr) => !rr.some((it) => usados.has(it)));
        const fors = formulas(libres, CUERPO).filter((f) =>
          !figReg.some((dg) => Math.min(f.reg.x1, dg.x1) - Math.max(f.reg.x0, dg.x0) > 0 &&
                               Math.min(f.reg.y1, dg.y1) - Math.max(f.reg.y0, dg.y0) > 0));
        for (const f of fors) for (const rr of f.lineas) for (const it of rr) usados.add(it);

        const tapar: Caja[] = [...tablas.map((t) => t.reg), ...figReg, ...fors.map((f) => f.reg)];
        const sueltas = manchas(datos, Wr, Hr, tapar).filter((f) => {
          const cerca = rens.flat().filter((it) => dentroDe(it, f));
          const area = (f.x1 - f.x0) * (f.y1 - f.y0);
          const areaTxt = cerca.reduce((n, it) => n + (it.x1 - it.x0) * (it.yb - it.yt), 0);
          return area > 0 && areaTxt / area <= 0.35;
        });
        const figuras = juntarFiguras(engordarFiguras([...figReg, ...sueltas], rens, CUERPO), Wr, Hr, CUERPO);
        for (const f of figuras) for (const it of rens.flat()) if (dentroDe(it, f)) usados.add(it);

        const piezas: { y: number; fila: Record<string, unknown> }[] = [];
        let nEnPagina = 0;
        // El recorte se sube con una direccion firmada que da la puerta (solo carpetas de este instrumento).
        const subir = async (carpeta: string, c: Caja): Promise<{ ruta: string | null; url: string | null }> => {
          const x = Math.max(0, Math.round(c.x0) - 6), y = Math.max(0, Math.round(c.y0) - 6);
          const w = Math.min(Wr - x, Math.round(c.x1 - c.x0) + 12), hh = Math.min(Hr - y, Math.round(c.y1 - c.y0) + 12);
          if (w <= 20 || hh <= 20) return { ruta: null, url: null };
          nEnPagina++;
          const ruta = iid + "/" + carpeta + "/" + String(p).padStart(4, "0") + "-" + nEnPagina + ".png";
          const png = await aPng(datos, Wr, x, y, w, hh);
          try {
            const s = await puerta({ modo: "blq_subida", instrumento_id: iid, ruta });
            const r = await fetch(String(s.url), {
              method: "PUT", headers: { "Content-Type": "image/png", "x-upsert": "true" }, body: new Blob([png as BlobPart]),
              signal: AbortSignal.timeout(120000),
            });
            await r.body?.cancel();
            return { ruta, url: r.ok ? String(s.publica) : null };
          } catch (e) {
            if (e instanceof PuertaNoDisponible) throw e;
            return { ruta, url: null };
          }
        };
        const pieDe = (caja: Caja): string | null => {
          for (const rr of rens) {
            if (rr.some((it) => usados.has(it))) continue;
            if (rr[0].yt > caja.y1 && rr[0].yt < caja.y1 + 30 * ESCALA) {
              const t = texto(rr).trim();
              if (PIE_FIG.test(t) || ROTULO.test(t)) { for (const z of rr) usados.add(z); return t.slice(0, 300); }
            }
          }
          return null;
        };

        let tablasPag = 0;
        for (const t of tablas) {
          const utiles = t.filas.map((f) => f.map((c) => (c ? c.t : ""))).filter((f) => f.some((c) => c !== ""));
          const legible = utiles.length >= 2 && utiles[0].length >= 2;
          const { ruta, url } = legible ? { ruta: null, url: null } : await subir("tablas", t.reg);
          if (legible) { nTablas++; tablasPag++; } else nIlegibles++;
          const pie = [t.rotulo, ...(t.lateral.length ? ["↺ " + t.lateral.join(" / ")] : [])]
            .filter(Boolean).join(" · ") || null;
          piezas.push({ y: t.reg.y0, fila: {
            clase: "tabla", pagina: p, celdas: legible ? utiles : null,
            filas_cabecera: Math.max(1, t.cabecera), ruta, url, pie, texto: null,
            estado: legible ? "leida" : "no_legible",
          } });
        }
        for (const f of fors) {
          const { ruta, url } = await subir("formulas", f.reg);
          nFormulas++;
          piezas.push({ y: f.reg.y0, fila: { clase: "figura", pagina: p, celdas: null, ruta, url, pie: f.pie, texto: null, estado: "leida" } });
        }
        for (const f of figuras) {
          const pie = pieDe(f);
          const { ruta, url } = await subir("figuras", f);
          nFiguras++;
          piezas.push({ y: f.y0, fila: { clase: "figura", pagina: p, celdas: null, ruta, url, pie, texto: null, estado: "leida" } });
        }

        const sobra = rens.filter((rr) => !rr.some((it) => usados.has(it)));
        const cosido = coser(sobra, CUERPO, margenesLocales(sobra, CUERPO));
        const nTit = cosido.filter((z) => z.clase === "titulo").length;
        const esIndice = nTit >= 6 && nTit >= 0.5 * cosido.length;
        for (const z0 of cosido) {
          const z = esIndice && z0.clase === "titulo" ? { ...z0, clase: "parrafo" } : z0;
          if (z.clase === "titulo") {
            const mart = ART.exec(z.txt), mcap = CAP.exec(z.txt);
            const m = NUM.exec(z.txt), ma = ANEJO.exec(z.txt);
            let ref: string | null = null, tit = z.txt, niv = 1;
            if (mart) { ref = "Artículo " + mart[1]; tit = (mart[2] || "").trim(); niv = 3; }
            else if (mcap) { ref = mcap[1] + " " + mcap[2]; tit = (mcap[3] || "").trim(); niv = 1; }
            else if (ma) { ref = ma[1] + " " + ma[2]; tit = (ma[3] || "").trim(); }
            else if (m) { ref = m[1]; tit = m[2].trim(); niv = m[1].split(".").length; }
            nTitulos++;
            piezas.push({ y: z.y, fila: {
              clase: "titulo", pagina: p, texto: tit || z.txt, referencia: ref,
              nivel: niv, celdas: null, estado: "leida",
            } });
          } else {
            nParrafos++;
            piezas.push({ y: z.y, fila: { clase: "parrafo", pagina: p, texto: z.txt, celdas: null, estado: "leida" } });
          }
        }

        piezas.sort((a, c) => a.y - c.y);
        let ref: string | null = refActual;
        const filas = piezas.map((z, i) => {
          const propia = z.fila.referencia as string | undefined;
          if (propia) ref = propia;
          const art = (ref ? porRef.get(llano(ref)) : null) ?? porPagina(p);
          return { ...z.fila, articulo_id: art, orden: p * 1000 + i };
        });
        refActual = ref;
        // Lo hecho se guarda pagina a pagina: si el runner muere, se sigue desde aqui.
        await puerta({ modo: "blq_pagina", instrumento_id: iid, pagina: p, filas, tablas: tablasPag });

        anterior = tablas.length ? [...tablas].sort((a, c) => a.reg.y1 - c.reg.y1)[tablas.length - 1] : null;
      }
      log("   paginas", desde + "-" + hasta, "de", total);
      desde = hasta + 1;
    }
    const res = await puerta({ modo: "blq_hecho", instrumento_id: iid, total });
    log("bloques", iid, "hecho:", total, "paginas,", nTitulos, "titulos,", nParrafos, "parrafos,", nTablas, "tablas,",
        nIlegibles, "no legibles,", nFiguras, "figuras,", nFormulas, "formulas,", nContinuadas, "continuadas,",
        Math.round((Date.now() - t0) / 1000), "s ->", JSON.stringify(res).slice(0, 100));
  } catch (e) {
    if (e instanceof PuertaNoDisponible) throw e;
    const msg = (e as Error).message.slice(0, 250);
    log("bloques", iid, "error:", msg);
    await puerta({ modo: "blq_hecho", instrumento_id: iid, error: msg });
  } finally {
    try { lib?.destroy(); } catch { /* da igual */ }
    try { await pdf?.destroy(); } catch { /* da igual */ }
  }
}

// -------------------------------------------------------------- ORDENES -----
async function contar() {
  let hay = false;
  try {
    const r = await puerta({ modo: "contar" });
    log("contar:", JSON.stringify(r));
    hay = (MAX_PAG > 0 && Number(r.paginado ?? 0) > 0) || (MAX_BLQ > 0 && Number(r.bloques ?? 0) > 0);
  } catch (e) {
    console.log("::warning::la puerta no responde, se deja para la proxima ejecucion (" + (e as Error).message.slice(0, 200) + ")");
  }
  const salida = Deno.env.get("GITHUB_OUTPUT");
  if (salida) await Deno.writeTextFile(salida, "hay=" + (hay ? "true" : "false") + "\n", { append: true });
}

async function trabajar() {
  // Primero el paginado: los bloques cuelgan del articulo por la pagina.
  while (MAX_PAG > 0 && Date.now() < HASTA - 10 * 60000) {
    const r = await puerta({ modo: "pag_tomar", limite: MAX_PAG });
    const docs = (r.documentos ?? []) as { instrumento_id: string; descarga: string; articulos: ArtPag[] }[];
    log("paginado:", docs.length, "documentos");
    if (!docs.length) break;
    for (const d of docs) await paginarDoc(d);
  }
  while (MAX_BLQ > 0 && Date.now() < HASTA - 10 * 60000) {
    const r = await puerta({ modo: "blq_tomar", limite: MAX_BLQ });
    const docs = (r.documentos ?? []) as { instrumento_id: string; descarga: string; desde: number; articulos: ArtBlq[] }[];
    log("bloques:", docs.length, "documentos");
    if (!docs.length) break;
    for (const d of docs) {
      if (Date.now() > HASTA) { await puerta({ modo: "blq_hecho", instrumento_id: d.instrumento_id, soltar: true }); continue; }
      await bloquesDoc(d);
    }
  }
  log("fin");
}

if (import.meta.main) {
  if (!CLAVE) { console.error("falta TRABAJADOR_CLAVE"); Deno.exit(1); }
  const orden = Deno.args[0] ?? "trabajar";
  if (orden === "contar") await contar();
  else if (orden === "trabajar") await trabajar();
  else { console.error("orden desconocida: " + orden); Deno.exit(2); }
}
