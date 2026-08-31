#!/usr/bin/env python3
"""
Watchlist Double Bill — v3

Cruza los watchlists publicos de dos perfiles de Letterboxd y devuelve
las coincidencias ordenadas por el rating promedio de la plataforma.

Novedades v3:
  - modos San Valentin (romance) y Halloween (horror o thriller)
  - los generos salen del mismo HTML que ya se pide por el rating: 0 requests extra

Novedades v2:
  - cada perfil puede sumar sus peliculas ya vistas al cruce ("repetir")
  - resultados en tandas de 10
  - cache en disco de los ratings (las corridas siguientes son casi instantaneas)

Uso:
    python3 watchlist_match.py
    -> abre http://localhost:8000

Sin dependencias: solo libreria estandar de Python 3.8+
"""

import json
import os
import re
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from concurrent.futures import ThreadPoolExecutor
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

PORT = int(os.environ.get("PORT", 8000))
HOST = os.environ.get("HOST", "127.0.0.1")   # en produccion: 0.0.0.0
BASE = "https://letterboxd.com"
UA = "watchlist-double-bill/0.3 (personal MVP; contacto: tu-email@ejemplo.com)"
CACHE_VERSION = 3       # subir esto invalida el cache cuando cambia la forma del dato
MAX_PAGES = 120         # techo de seguridad
FETCH_WORKERS = 3       # peticiones simultaneas a Letterboxd. Bajo a proposito:
                        # el paralelismo sostenido es lo que delata a un bot.
PAGE_SIZE = 10          # resultados por tanda
MAX_RANK = 1000         # techo duro de peliculas a rankear en una corrida

CACHE_PATH = os.environ.get(
    "CACHE_PATH",
    os.path.join(os.path.dirname(os.path.abspath(__file__)), ".film_cache.json"))

# Cache pre-cocinado que viaja con el repo. Se genera en local con --warm y se
# lee al arrancar. Es lo que evita que el servidor tenga que redescubrir el
# top 500 desde cero cada vez que se reinicia.
SEED_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                         "film_cache_seed.json")

# Limite por visitante. Sin esto, una sola persona puede lanzar cientos de
# peticiones a Letterboxd desde el servidor. Solo aplica a los endpoints caros.
RATE_WINDOW = 600       # segundos
RATE_MAX = 60           # peticiones por ventana y por IP. Cada accion cuenta:
                        # cruzar, rankear, y cada clic de "mas recomendaciones".

# Listas publicas de donde salen las recomendaciones.
# "urls" puede tener varias: se concatenan en orden y se quitan repetidas.
# En produccion NO se descargan: se leen de la semilla. Los links solo se usan
# al correr --warm.
LISTS = {
    # Solo para las tarjetas de San Valentin y Halloween.
    "top500": {
        "urls": ["https://letterboxd.com/dave/list/letterboxd-top-500-films-history-collected/"],
        "pages": 7,
    },
    # Descubrimiento: el top all-time y las underseen en una sola bolsa.
    # slugs_de_lista ya quita repetidas y ordena por rating, asi que las tres
    # recomendaciones salen por merito y no por cuota de cada lista.
    "alltime": {
        "urls": [
            "https://letterboxd.com/dave/list/letterboxd-top-500-films-history-collected/",
            "https://letterboxd.com/official/list/top-100-underseen-films/",
        ],
        "pages": 7,
    },
    # Premiadas: Palma de Oro + BAFTA mejor pelicula + Oscar mejor pelicula.
    "winners": {
        "urls": [
            "https://letterboxd.com/cannestracker/list/palme-dor-winners/",
            "https://letterboxd.com/bafta/list/all-bafta-best-film-award-winners/",
            "https://letterboxd.com/oscars/list/oscar-winning-films-best-picture/",
        ],
        "pages": 2,
    },
    # Peliculas modernas mejor puntuadas en IMDb, lista propia.
    # 10 paginas = hasta 1000 titulos. Si la lista es mas corta, para sola.
    "modern": {
        "urls": ["https://letterboxd.com/alvarovadilloz/list/imdb-top-modern-films/"],
        "pages": 10,
    },
}
SCAN_CHUNK = 25         # cuantas fichas abrimos por tanda antes de volver a evaluar
MAX_SCAN = 250          # techo de fichas a revisar antes de rendirse

# Solo el comando --warm puede salir a buscar listas. En produccion se leen
# de la semilla y punto: asi el trafico a Letterboxd por este concepto es cero.
MODO_WARM = False

# Que genero define cada modo. Igual que en la UI, pero el servidor no confia en
# lo que le mande el cliente.
MODE_GENRES = {
    "valentine": {"romance"},
    "halloween": {"horror"},
}

_cache_lock = threading.Lock()
_film_cache = {}

# Estas dos viven solo en memoria: el estado de "vista" cambia y es por persona.
_watch_lock = threading.Lock()
_watch_cache = {}       # "usuario/slug" -> True | False
_list_lock = threading.Lock()
_list_pages = {}        # (url, numero de pagina) -> lista de slugs

_rate_lock = threading.Lock()
_rate = {}              # ip -> lista de timestamps

# Cuantas peticiones salen de verdad hacia Letterboxd. Sirve para dejar de
# estimar: se ve en /api/stats.
_net_lock = threading.Lock()
_net = {"paginas": 0, "vistas": 0, "inicio": time.time()}


def contar(tipo):
    with _net_lock:
        _net[tipo] = _net.get(tipo, 0) + 1


def stats_red():
    with _net_lock:
        d = dict(_net)
    horas = max((time.time() - d.pop("inicio")) / 3600, 0.001)
    total = sum(d.values())
    d["total"] = total
    d["por_hora"] = round(total / horas, 1)
    d["horas_encendido"] = round(horas, 2)
    return d


def rate_ok(ip):
    """False si esa IP ya paso su cuota en la ventana actual."""
    ahora = time.time()
    with _rate_lock:
        marcas = [t for t in _rate.get(ip, []) if ahora - t < RATE_WINDOW]
        if len(marcas) >= RATE_MAX:
            _rate[ip] = marcas
            return False
        marcas.append(ahora)
        _rate[ip] = marcas
        if len(_rate) > 5000:               # poda simple, que no crezca sin fin
            viejas = [k for k, v in _rate.items()
                      if not v or ahora - v[-1] > RATE_WINDOW]
            for k in viejas:
                _rate.pop(k, None)
    return True


def load_cache():
    """Carga el cache solo si es de esta version. Un cache v2 no trae generos."""
    global _film_cache
    try:
        with open(CACHE_PATH, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return
    if not isinstance(data, dict):
        return
    if data.get("version") != CACHE_VERSION:
        print("Cache de una version anterior: se descarta y se vuelve a construir.")
        return
    films = data.get("films")
    if isinstance(films, dict):
        _film_cache = films
        print(f"Cache: {len(_film_cache)} peliculas conocidas.")


def save_cache():
    try:
        with _cache_lock:
            snapshot = dict(_film_cache)
        tmp = CACHE_PATH + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump({"version": CACHE_VERSION, "films": snapshot}, f)
        os.replace(tmp, CACHE_PATH)
    except OSError:
        pass  # el cache es un lujo, no una dependencia


def load_seed():
    """
    Carga el cache pre-cocinado que viaja con el repo: fichas de peliculas y
    contenido de las listas. Es de solo lectura; lo que se descubra despues
    vive en memoria. Sin esto, cada reinicio del servidor empieza de cero.
    """
    try:
        with open(SEED_PATH, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return

    if data.get("version") != CACHE_VERSION:
        print("Semilla de una version anterior: se ignora.")
        return

    films = data.get("films") or {}
    with _cache_lock:
        for k, v in films.items():
            _film_cache.setdefault(k, v)

    listas = data.get("lists") or {}
    n = 0
    with _list_lock:
        for k, slugs in listas.items():
            url, _, page = k.rpartition("|")
            if url and page.isdigit():
                _list_pages.setdefault((url, int(page)), slugs)
                n += 1

    print(f"Semilla: {len(films)} peliculas y {n} paginas de listas.")


def warm():
    """
    Descarga las fichas de todas las peliculas de todas las listas y las deja
    en la semilla. Se corre en local y despues se sube el archivo al repo:

        python watchlist_match.py --warm
    """
    global MODO_WARM
    MODO_WARM = True          # unico momento en que se permite bajar listas

    todos = []
    paginas = {}

    for key, conf in LISTS.items():
        antes = len(todos)
        for url in conf["urls"]:
            for page in range(1, conf["pages"] + 1):
                slugs = list_page(url, page)
                if not slugs:
                    break
                paginas[f"{url}|{page}"] = slugs
                todos.extend(slugs)
        print(f"lista '{key}': {len(todos) - antes} entradas "
              f"({len(conf['urls'])} fuente(s))")

    todos = list(dict.fromkeys(todos))
    print(f"\n{len(todos)} peliculas unicas. Descargando fichas...")

    with ThreadPoolExecutor(max_workers=FETCH_WORKERS) as pool:
        for i, _ in enumerate(pool.map(fetch_film, todos), 1):
            if i % 25 == 0 or i == len(todos):
                print(f"  {i}/{len(todos)}")

    with _cache_lock:
        snapshot = dict(_film_cache)
    con_genero = sum(1 for f in snapshot.values() if f.get("genres"))

    with open(SEED_PATH, "w", encoding="utf-8") as f:
        json.dump({"version": CACHE_VERSION, "films": snapshot, "lists": paginas},
                  f, ensure_ascii=False)

    kb = os.path.getsize(SEED_PATH) / 1024
    print(f"\nGuardadas {len(snapshot)} peliculas ({con_genero} con genero) "
          f"y {len(paginas)} paginas de listas en {SEED_PATH} ({kb:.0f} KB).")
    print("Ahora sube ese archivo al repo y vuelve a desplegar.")


# ─────────────────────────────────────────────────────────────
# HTTP
# ─────────────────────────────────────────────────────────────

def get(url, timeout=20):
    contar("paginas")          # todo lo que sale a Letterboxd pasa por aqui
    req = urllib.request.Request(url, headers={
        "User-Agent": UA,
        "Accept": "text/html,application/xhtml+xml",
        "Accept-Language": "en",
    })
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read().decode("utf-8", errors="replace")


# ─────────────────────────────────────────────────────────────
# Perfil, watchlist y vistas
# ─────────────────────────────────────────────────────────────

def parse_username(raw):
    """Acepta 'alvarovadilloz', '@alvarovadilloz' o cualquier URL del perfil."""
    s = (raw or "").strip()
    if not s:
        return None
    s = re.sub(r"^@", "", s)
    m = re.search(r"letterboxd\.com/([^/?#\s]+)", s, re.I)
    if m:
        s = m.group(1)
    s = s.strip("/").split("/")[0].split("?")[0]
    if not s or s.lower() in {"film", "films", "lists", "actor", "director", "search"}:
        return None
    if not re.fullmatch(r"[A-Za-z0-9_-]+", s):
        return None
    return s.lower()


# Letterboxd ha cambiado estos atributos varias veces; probamos en orden.
SLUG_PATTERNS = [
    re.compile(r'data-film-slug="([^"]+)"'),
    re.compile(r'data-item-slug="([^"]+)"'),
    re.compile(r'data-target-link="/film/([^/"]+)/'),
    re.compile(r'data-film-link="/film/([^/"]+)/'),
]
HREF_FALLBACK = re.compile(r'href="/film/([^/"?#]+)/?"')


def extract_slugs(html):
    """Slugs de peliculas en orden de aparicion, sin duplicados."""
    for pat in SLUG_PATTERNS:
        found = pat.findall(html)
        if found:
            return list(dict.fromkeys(found))
    return list(dict.fromkeys(HREF_FALLBACK.findall(html)))


def fetch_section(username, section, paginate=True):
    """
    section: 'watchlist' (por ver) o 'films' (ya vistas).

    paginate=True  -> recorre todas las paginas (watchlist: 28 por pagina).
    paginate=False -> solo la primera. Letterboxd devuelve 403 en /films/page/2/
                      y siguientes, asi que pedirlas es un viaje perdido.

    Devuelve lista de slugs. Lanza ValueError con mensaje legible.
    """
    label = "watchlist" if section == "watchlist" else "peliculas vistas"
    try:
        first = get(f"{BASE}/{username}/{section}/")
    except urllib.error.HTTPError as e:
        if e.code == 404:
            raise ValueError(f"No existe el perfil '{username}' en Letterboxd.")
        raise ValueError(f"Letterboxd respondio {e.code} para '{username}'.")
    except urllib.error.URLError as e:
        raise ValueError(f"No se pudo conectar con Letterboxd: {e.reason}")

    if re.search(r"(watchlist|profile) is (private|not visible)|hidden their watchlist",
                 first, re.I):
        raise ValueError(f"El {label} de '{username}' es privado.")

    slugs = extract_slugs(first)
    if not slugs or not paginate:
        return slugs

    page_size = len(slugs)
    seen = set(slugs)
    page = 2
    while page <= MAX_PAGES:
        if len(slugs) % page_size != 0:
            break  # la ultima pagina vino corta
        try:
            html = get(f"{BASE}/{username}/{section}/page/{page}/")
        except (urllib.error.HTTPError, urllib.error.URLError):
            break
        found = extract_slugs(html)
        new = [s for s in found if s not in seen]
        if not new:
            break
        slugs.extend(new)
        seen.update(new)
        page += 1

    return slugs


def leer_vistas(username):
    """
    Peliculas que el usuario registro como vistas, uniendo dos fuentes:

      /films/  -> 72 titulos, sin orden de fecha
      /diary/  -> 50 visionados mas recientes

    Se solapan bastante pero no del todo: medido en tres perfiles, el diario
    aportaba entre 7 y 37 titulos que /films/ no traia. De ambas solo se puede
    leer la primera pagina; el resto lo bloquea Letterboxd.
    """
    vistas = fetch_section(username, "films", paginate=False)
    conocidas = set(vistas)
    try:
        diario = fetch_section(username, "diary", paginate=False)
    except Exception:
        diario = []          # fuente secundaria: si falla, seguimos con /films/
    for s in diario:
        if s not in conocidas:
            vistas.append(s)
            conocidas.add(s)
    return vistas


def build_pool(username, include_seen):
    """
    Devuelve (pool, stats).
      pool  : dict slug -> 'seen' | 'watchlist'
      stats : conteos para mostrar en la UI
    Si el mismo slug aparece en ambos lados, gana 'seen'.

    El watchlist se lee completo. Las vistas son parciales por diseno del
    sitio: solo la primera pagina de cada fuente.
    """
    watchlist = fetch_section(username, "watchlist")
    pool = {s: "watchlist" for s in watchlist}
    seen = []
    if include_seen:
        seen = leer_vistas(username)
        for s in seen:
            pool[s] = "seen"
    return pool, {
        "user": username,
        "watchlist": len(watchlist),
        "seen": len(seen),
        "pool": len(pool),
        "include_seen": bool(include_seen),
        "url": f"{BASE}/{username}/",
    }


# ─────────────────────────────────────────────────────────────
# Datos de cada pelicula
# ─────────────────────────────────────────────────────────────

OG_TITLE = re.compile(r'<meta property="og:title" content="([^"]+)"')
OG_IMAGE = re.compile(r'<meta property="og:image" content="([^"]+)"')
LD_RATING = re.compile(r'"aggregateRating".*?"ratingValue"\s*:\s*([\d.]+)', re.S)
LD_COUNT = re.compile(r'"aggregateRating".*?"ratingCount"\s*:\s*(\d+)', re.S)
CSI_AVG = re.compile(r"Weighted average of\s*([\d.]+)\s*based on\s*([\d,]+)", re.I)

# Generos. Preferimos el bloque #tab-genres para no confundirnos con links de
# navegacion en otras partes de la pagina. Si no esta, barremos toda la pagina.
GENRE_BLOCK = re.compile(r'id="tab-genres".*?(?=id="tab-|</section>|<footer)', re.S)
GENRE_HREF = re.compile(r'href="/films/genre/([a-z0-9\-]+)/?"')
LD_GENRE = re.compile(r'"genre"\s*:\s*\[([^\]]*)\]')

# 19 generos de TMDB, que es la taxonomia que usa Letterboxd. Lista cerrada:
# sirve para descartar cualquier cosa rara que capture el regex.
VALID_GENRES = {
    "action", "adventure", "animation", "comedy", "crime", "documentary", "drama",
    "family", "fantasy", "history", "horror", "music", "mystery", "romance",
    "science-fiction", "thriller", "tv-movie", "war", "western",
}


def extract_genres(html):
    """Lista de slugs de genero, en minuscula. [] si no se encuentran."""
    block = GENRE_BLOCK.search(html)
    found = GENRE_HREF.findall(block.group(0) if block else html)

    if not found:
        m = LD_GENRE.search(html)
        if m:
            found = [g.strip().strip('"').lower().replace(" ", "-")
                     for g in m.group(1).split(",")]

    return [g for g in dict.fromkeys(found) if g in VALID_GENRES]


def unescape(s):
    return (s.replace("&amp;", "&").replace("&#039;", "'").replace("&quot;", '"')
             .replace("&lt;", "<").replace("&gt;", ">").replace("&rsquo;", "\u2019"))


def fetch_film(slug):
    """{slug, title, year, rating, votes, poster, url}. rating puede ser None."""
    with _cache_lock:
        hit = _film_cache.get(slug)
    if hit:
        return hit

    url = f"{BASE}/film/{slug}/"
    data = {"slug": slug, "title": slug.replace("-", " ").title(),
            "year": None, "rating": None, "votes": None, "poster": None,
            "genres": [], "url": url}

    try:
        html = get(url)
    except Exception:
        return data  # fallo puntual: no lo guardamos en cache

    data["genres"] = extract_genres(html)

    m = OG_TITLE.search(html)
    if m:
        raw = unescape(m.group(1))
        ym = re.search(r"^(.*?)\s*\((\d{4})\)\s*$", raw)
        if ym:
            data["title"], data["year"] = ym.group(1), int(ym.group(2))
        else:
            data["title"] = raw

    m = OG_IMAGE.search(html)
    if m and "default-share" not in m.group(1):
        data["poster"] = m.group(1)

    # 1) JSON-LD embebido en la pagina
    m = LD_RATING.search(html)
    if m:
        data["rating"] = float(m.group(1))
        c = LD_COUNT.search(html)
        if c:
            data["votes"] = int(c.group(1))

    # 2) endpoint del histograma (lo que usa la propia web para pintar el promedio)
    if data["rating"] is None:
        try:
            csi = get(f"{BASE}/csi/film/{slug}/rating-histogram/")
            m = CSI_AVG.search(csi)
            if m:
                data["rating"] = float(m.group(1))
                data["votes"] = int(m.group(2).replace(",", ""))
        except Exception:
            pass

    with _cache_lock:
        _film_cache[slug] = data
    return data


# ─────────────────────────────────────────────────────────────
# Fase 1: cruzar. Fase 2: rankear.
# ─────────────────────────────────────────────────────────────

def find_shared(raw_a, raw_b, seen_a, seen_b):
    a = parse_username(raw_a)
    b = parse_username(raw_b)
    if not a:
        raise ValueError("El primer perfil no se entiende. Pega el link o el usuario.")
    if not b:
        raise ValueError("El segundo perfil no se entiende. Pega el link o el usuario.")

    mismo = (a == b)   # permitido: equivale a ordenar un watchlist propio por rating
    # Solo reutilizamos la lectura si ademas las opciones son identicas.
    reusar = mismo and bool(seen_a) == bool(seen_b)

    with ThreadPoolExecutor(max_workers=2) as pool:
        fa = pool.submit(build_pool, a, seen_a)
        fb = None if reusar else pool.submit(build_pool, b, seen_b)
        pool_a, stats_a = fa.result()
        pool_b, stats_b = (dict(pool_a), dict(stats_a)) if reusar else fb.result()

    shared = [{"slug": s, "a": pool_a[s], "b": pool_b[s]}
              for s in pool_a if s in pool_b]

    with _cache_lock:
        cached = sum(1 for s in shared if s["slug"] in _film_cache)

    return {"a": stats_a, "b": stats_b, "shared": shared, "cached": cached,
            "same": mismo}


def rank(slugs):
    if not isinstance(slugs, list):
        raise ValueError("Lista de peliculas invalida.")
    slugs = [s for s in slugs if isinstance(s, str) and re.fullmatch(r"[a-z0-9\-]+", s)]
    if not slugs:
        return []
    slugs = slugs[:MAX_RANK]

    with ThreadPoolExecutor(max_workers=FETCH_WORKERS) as pool:
        films = list(pool.map(fetch_film, slugs))

    # sin rating (estrenos futuros, muy obscuras) al final
    films.sort(key=lambda f: (f["rating"] is not None, f["rating"] or 0, f["votes"] or 0),
               reverse=True)
    save_cache()
    return films


# ─────────────────────────────────────────────────────────────
# Trivial: pool de peliculas para el juego local
# ─────────────────────────────────────────────────────────────

# Nombre publico del set -> lista interna. Cerrado a proposito.
TRIVIA_SETS = {
    "descubrimiento": "alltime",
    "siglo21": "modern",
    "premiadas": "winners",
}


def trivia_pool(sets):
    """
    Peliculas para el juego, unidas y sin repetir. Todo sale de la semilla:
    cero peticiones a Letterboxd.

    Se descarta lo que no tenga anio o rating, porque las preguntas comparan
    justamente esos campos y una ficha incompleta rompe la ronda.
    """
    claves = [TRIVIA_SETS[x] for x in sets if x in TRIVIA_SETS]
    if not claves:
        raise ValueError("Elige al menos un set valido.")

    vistos = set()
    pool = []
    for k in claves:
        for slug in slugs_de_lista(k):
            if slug in vistos:
                continue
            vistos.add(slug)
            with _cache_lock:
                f = _film_cache.get(slug)
            if not f or f.get("year") is None or f.get("rating") is None:
                continue
            pool.append({
                "slug": slug,
                "title": f.get("title") or slug,
                "year": f["year"],
                "rating": f["rating"],      # sin redondear
                "poster": f.get("poster"),
                "url": f.get("url"),
            })
    return pool


# ─────────────────────────────────────────────────────────────
# Recomendacion: la mejor del top 500 que ninguno haya visto
# ─────────────────────────────────────────────────────────────

def list_page(url, page):
    """
    Slugs de una pagina de una lista publica, en el orden en que estan.

    En produccion esto sale siempre de la semilla. Si no esta ahi, devolvemos
    vacio en vez de salir a la red: las listas se descargan una sola vez con
    --warm y se suben al repo.
    """
    key = (url, page)
    with _list_lock:
        hit = _list_pages.get(key)
    if hit is not None:
        return hit

    if not MODO_WARM:
        return []          # sin semilla y sin permiso de descargar

    full = url if page == 1 else f"{url}page/{page}/"
    try:
        slugs = extract_slugs(get(full))
    except Exception:
        slugs = []

    with _list_lock:
        _list_pages[key] = slugs
    return slugs


def slugs_de_lista(list_key):
    """
    Todas las peliculas de una lista, sin repetidas y ordenadas de mejor a
    peor rating de Letterboxd.

    El orden original de cada lista no sirve para recomendar: 'winners'
    concatena Cannes, BAFTA y Oscar en orden cronologico, asi que sin ordenar
    la primera sugerencia seria siempre la mas antigua de Cannes. Como los
    ratings ya vienen en la semilla, esto no cuesta ninguna peticion.

    Las que no tienen rating quedan al final, igual que en el ranking.
    """
    conf = LISTS.get(list_key)
    if not conf:
        raise ValueError("Lista desconocida.")

    todos = []
    vistos = set()
    for url in conf["urls"]:
        for page in range(1, conf["pages"] + 1):
            slugs = list_page(url, page)
            if not slugs:
                break
            for s in slugs:
                if s not in vistos:
                    vistos.add(s)
                    todos.append(s)

    def puntaje(slug):
        f = _film_cache.get(slug) or {}
        r = f.get("rating")
        return (r is not None, r or 0, f.get("votes") or 0)

    with _cache_lock:
        todos.sort(key=puntaje, reverse=True)
    return todos


def _consultar_visto(url, metodo):
    """
    Devuelve (resultado, codigo):
      True  = la vio (200)
      False = no la vio (404)
      None  = no se pudo determinar (403, 429, timeout, lo que sea)
    """
    contar("vistas")           # la consulta de "la vio?"
    req = urllib.request.Request(url, method=metodo, headers={
        "User-Agent": UA, "Accept": "text/html",
    })
    try:
        with urllib.request.urlopen(req, timeout=15) as r:
            return (r.status == 200), r.status
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return False, 404
        return None, e.code
    except Exception:
        return None, None


def has_watched(username, slug, incierto=None):
    """
    True si el usuario registro esa pelicula como vista.

    Usa /{usuario}/film/{slug}/, que responde 200 solo si la vio y 404 si no.
    Verificado: una pelicula en su watchlist pero no vista da 404, asi que
    esta ruta distingue "vista" de "quiere verla".

    Si la consulta no se resuelve (403, rate limit, timeout) devolvemos True,
    o sea "tratala como vista", para no recomendar algo que quiza ya vieron.
    Pero lo anotamos en 'incierto': si TODO falla, quien llama tiene que poder
    distinguir "ya vieron todo" de "no pudimos preguntar".
    """
    key = f"{username}/{slug}"
    with _watch_lock:
        if key in _watch_cache:
            return _watch_cache[key]

    url = f"{BASE}/{username}/film/{slug}/"

    visto, codigo = _consultar_visto(url, "HEAD")
    if visto is None and codigo == 405:
        visto, codigo = _consultar_visto(url, "GET")   # no aceptan HEAD

    if visto is None:
        if incierto is not None:
            incierto.append(codigo)
        return True          # no sabemos: no la ofrecemos, y no lo cacheamos

    with _watch_lock:
        _watch_cache[key] = visto
    return visto


def take_unwatched(list_key, a, b, want=None, n=1, skip=None, incierto=None):
    """
    Baja por una lista publica en su orden y devuelve hasta n peliculas
    que NINGUNO de los dos haya visto. Sin repetir.

    skip = slugs ya elegidos en otra lista, para no ofrecer la misma dos veces.

    want=None  -> cualquier genero. No hace falta abrir fichas durante el
                  barrido: basta preguntar si la vieron. Solo se abren las
                  fichas de las ganadoras.
    want={...} -> hay que abrir cada ficha para conocer su genero.

    Pedir n=2 en una sola pasada evita recorrer la lista dos veces.
    """
    conf = LISTS.get(list_key)
    if not conf:
        raise ValueError("Lista desconocida.")

    skip = skip or set()
    encontradas = []
    posicion = 0
    revisadas = 0

    slugs = slugs_de_lista(list_key)

    for i in range(0, len(slugs), SCAN_CHUNK):
        tanda = slugs[i:i + SCAN_CHUNK]

        if want:
            with ThreadPoolExecutor(max_workers=FETCH_WORKERS) as pool:
                fichas = list(pool.map(fetch_film, tanda))
        else:
            fichas = [{"slug": s} for s in tanda]

        for f in fichas:
            posicion += 1
            if f["slug"] in skip:
                continue        # ya mostrada: no cuenta como trabajo nuevo
            revisadas += 1
            if want and not (set(f.get("genres") or []) & want):
                continue
            # Sin perfil no hay a quien preguntarle: se ofrecen todas.
            if a and has_watched(a, f["slug"], incierto):
                continue
            if b and has_watched(b, f["slug"], incierto):
                continue
            completa = f if want else fetch_film(f["slug"])
            encontradas.append({**completa, "rank": posicion, "scanned": revisadas})
            if len(encontradas) >= n:
                save_cache()
                return encontradas

        if revisadas >= MAX_SCAN:
            break

    save_cache()
    return encontradas


def first_unwatched(list_key, a, b, want=None, skip=None, incierto=None):
    """La primera que ninguno vio y que no este ya mostrada, o None."""
    r = take_unwatched(list_key, a, b, want, 1, skip, incierto)
    return r[0] if r else None


def _dos_usuarios(raw_a, raw_b, obligatorio=True):
    """
    Devuelve (a, b). Si obligatorio=False acepta que no haya perfiles: es el
    caso "no tengo Letterboxd", donde no hay a quien preguntarle si la vio.
    """
    a = parse_username(raw_a)
    b = parse_username(raw_b)
    if obligatorio and (not a or not b):
        raise ValueError("Perfiles invalidos.")
    return a, b


def limpiar_skip(bruto):
    """Slugs ya mostrados que llegan del cliente. Se validan y se acotan."""
    if not isinstance(bruto, list):
        return set()
    return {s for s in bruto[:400]
            if isinstance(s, str) and re.fullmatch(r"[a-z0-9\-]+", s)}


def pick_recommendation(mode, raw_a, raw_b, skip=None):
    """La mejor del top 500 del genero del modo que ninguno haya visto."""
    want = MODE_GENRES.get(mode)
    if not want:
        raise ValueError("Modo desconocido.")
    a, b = _dos_usuarios(raw_a, raw_b, obligatorio=False)
    incierto = []
    pick = first_unwatched("top500", a, b, want, limpiar_skip(skip), incierto)
    # Si no hay resultado pero hubo consultas sin resolver, no es que ya las
    # vieran todas: es que Letterboxd no contesto.
    return {"pick": pick, "incierto": bool(incierto) and pick is None}


# Los dos modos de medidor. Cada uno reparte sus 3 huecos entre una o varias
# listas. "winners" es identico a "discovery" salvo que bebe de una sola fuente.
DISCOVERY_MODES = {
    "discovery": {
        "fuentes": [("alltime", 3)],
        "labels": ["", "", ""],
    },
    "winners": {
        "fuentes": [("winners", 3)],
        "labels": ["", "", ""],
    },
    "siglo21": {
        "fuentes": [("modern", 3)],
        "labels": ["", "", ""],
    },
}

# Generos que se pueden pedir desde el medidor. Lista cerrada a proposito.
DISCOVERY_GENRES = ["horror", "romance", "comedy", "thriller", "drama", "action",
                    "science-fiction", "war", "animation"]


def discover(raw_a, raw_b, genre=None, skip=None, modo="discovery"):
    """
    Tres peliculas que ninguno vio, repartidas entre las fuentes del modo.

    skip = slugs ya mostrados en rondas anteriores. Es lo que hace que el
    boton de "mas recomendaciones" avance, sin llevar contadores.

    genre=None -> cualquier genero, y no hace falta abrir fichas durante el
                  barrido. Rapido.
    genre=x    -> hay que abrir la ficha de cada candidata. Mas lento.
    """
    conf = DISCOVERY_MODES.get(modo)
    if not conf:
        raise ValueError("Modo desconocido.")

    a, b = _dos_usuarios(raw_a, raw_b, obligatorio=False)
    ya = limpiar_skip(skip)

    want = None
    if genre:
        if genre not in DISCOVERY_GENRES:
            raise ValueError("Genero no disponible.")
        want = {genre}

    incierto = []

    def buscar(list_key, n, extra=None):
        try:
            return take_unwatched(list_key, a, b, want, n,
                                  ya | (extra or set()), incierto)
        except Exception:
            return []

    fuentes = conf["fuentes"]
    with ThreadPoolExecutor(max_workers=len(fuentes)) as pool:
        futuros = [pool.submit(buscar, key, n) for key, n in fuentes]
        resultados = [f.result() for f in futuros]

    # Una misma pelicula puede estar en dos listas. Si una fuente devuelve algo
    # que otra ya ocupo, se rebusca excluyendolo. Solo pasa a veces, asi que no
    # vale la pena pedir candidatas de mas por adelantado.
    films = []
    usados = set()
    for (key, n), encontradas in zip(fuentes, resultados):
        limpias = [f for f in encontradas if f["slug"] not in usados]
        if len(limpias) < n:
            limpias = [f for f in buscar(key, n, usados) if f["slug"] not in usados]
        hueco = limpias[:n]
        usados.update(f["slug"] for f in hueco)
        films.extend(hueco + [None] * (n - len(hueco)))

    etapas = [{"label": conf["labels"][i], "film": films[i]} for i in range(3)]
    vacio = not any(e["film"] for e in etapas)
    return {"stages": etapas, "incierto": bool(incierto) and vacio}


# ─────────────────────────────────────────────────────────────
# UI
# ─────────────────────────────────────────────────────────────

PAGE = r"""<!doctype html>
<html lang="es">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Watchlist Double Bill</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Instrument+Serif:ital@0;1&family=Inter:wght@400;500;600&family=IBM+Plex+Mono:wght@400;500&family=Poppins:wght@600&display=swap" rel="stylesheet">
<style>
  :root{
    --night:#141a2e; --panel:#1c2440; --edge:#2c3557;
    --bone:#ece6d9; --dim:#8b93b4;
    --signal:#ff4d3d; --beam:#7fd6cd;
    --gold:#e3b85a; --rose:#de7e98; --clay:#c4693f;
    --geo:"Poppins",var(--sans);
    --serif:"Instrument Serif",Georgia,serif;
    --sans:"Inter",system-ui,-apple-system,sans-serif;
    --mono:"IBM Plex Mono",ui-monospace,monospace;
  }
  *{box-sizing:border-box}
  body{margin:0;background:var(--night);color:var(--bone);font-family:var(--sans);
       font-size:15px;line-height:1.5;-webkit-font-smoothing:antialiased}
  .wrap{max-width:760px;margin:0 auto;padding:56px 24px 96px}

  .eyebrow{font-family:var(--mono);font-size:11px;letter-spacing:.22em;
           text-transform:uppercase;color:var(--dim);margin:0 0 10px}
  h1{font-family:var(--serif);font-weight:400;font-size:clamp(38px,7vw,60px);
     line-height:1.02;margin:0 0 12px}

  /* Logo: circulos + logotipo. Es un boton, reinicia la pagina. */
  .logo{display:flex;align-items:center;gap:15px;width:auto;background:none;
        border:0;padding:0;margin:0 0 16px;cursor:pointer;transition:opacity .15s}
  .logo:hover:not(:disabled){opacity:.85;filter:none}
  .logo:focus-visible{outline:2px solid var(--gold);outline-offset:6px;border-radius:2px}
  .logo svg{height:clamp(44px,8vw,58px);width:auto;display:block}
  .logo .word{font-family:var(--geo);font-weight:600;color:var(--bone);
              font-size:clamp(30px,5.5vw,42px);line-height:1;letter-spacing:-.015em}
  .lede{color:var(--dim);max-width:46ch;margin:0 0 40px}

  .bill{display:grid;grid-template-columns:1fr 112px 1fr;gap:14px;align-items:start}
  .amp{font-family:var(--geo);font-weight:600;font-size:34px;color:var(--bone);
       line-height:1;padding-top:9px;user-select:none}
  .mid{display:flex;flex-direction:column;align-items:center}
  .hint{margin-top:8px;white-space:nowrap;text-align:center;
        font-family:var(--mono);font-size:11px;color:var(--dim)}
  input[type=text]{width:100%;background:var(--panel);border:1px solid var(--edge);
        color:var(--bone);border-radius:3px;padding:13px 14px;font-family:var(--mono);
        font-size:13px;transition:border-color .15s}
  input[type=text]::placeholder{color:#5c648a}
  input[type=text]:focus{outline:none;border-color:var(--beam)}
  input[type=text]:focus-visible{outline:2px solid var(--beam);outline-offset:1px}

  .opt{display:flex;align-items:center;gap:8px;margin-top:9px;font-size:12.5px;
       color:var(--dim);cursor:pointer}
  .opt input{accent-color:var(--signal);width:14px;height:14px;cursor:pointer;margin:0}
  .opt:hover{color:var(--bone)}

  button{width:100%;background:var(--signal);color:#fff;border:0;border-radius:3px;
         padding:15px;font-family:var(--sans);font-weight:600;font-size:14px;
         letter-spacing:.02em;cursor:pointer;transition:filter .15s}
  button:hover:not(:disabled){filter:brightness(1.12)}
  button:disabled{opacity:.45;cursor:progress}
  #go{margin-top:22px;background:var(--clay)}
  button.ghost{background:transparent;color:var(--beam);border:1px solid var(--edge);
               font-weight:500;margin-top:24px}
  button.ghost:hover:not(:disabled){background:var(--panel);filter:none}

  .note{margin-top:14px;font-size:12.5px;color:var(--dim)}
  button.sinlb{margin-top:9px;padding:11px;font-size:12.5px;
               color:var(--gold);border-color:var(--gold)}
  button.sinlb:hover:not(:disabled){background:rgba(227,184,90,.09)}
  .status{margin-top:28px;font-family:var(--mono);font-size:12.5px;color:var(--beam);
          min-height:19px}
  .status.err{color:var(--signal)}

  .tally{margin:44px 0 8px;padding-top:22px;border-top:1px solid var(--edge);
         font-family:var(--mono);font-size:12px;color:var(--dim);letter-spacing:.04em;
         line-height:1.7}
  .tally b{color:var(--bone);font-weight:500}

  .gate{background:var(--panel);border:1px solid var(--edge);border-radius:3px;
        padding:20px;margin-top:24px}
  .gate p{margin:0 0 14px;font-size:14px}
  .gate button{width:auto;padding:11px 20px}

  /* ── modos ─────────────────────────────────────────────
     Los botones viven fuera del deck y no cambian de piel:
     el tema se queda adentro de la lista. */
  .modes{display:flex;gap:8px;margin:26px 0 4px;flex-wrap:wrap}
  .mode{width:auto;background:transparent;border:1px solid var(--edge);color:var(--dim);
        padding:8px 15px;font-size:12.5px;font-weight:500;border-radius:999px;
        transition:color .15s,border-color .15s}
  .mode:hover:not(:disabled){color:var(--bone);border-color:var(--dim);filter:none}
  .mode:disabled{opacity:.35;cursor:not-allowed}
  .mode[aria-pressed="true"]{color:#fff;border-color:transparent}
  .mode[data-mode="valentine"][aria-pressed="true"]{background:#b8465f}
  .mode[data-mode="halloween"][aria-pressed="true"]{background:#c25a1e}

  /* ── el deck: unico elemento que se tematiza ───────────
     Cada modo redefine dos tokens locales y agrega una sola firma. */
  .deck{--acc:var(--signal);--sc:var(--beam);--rule:var(--edge);
        position:relative;margin-top:14px}
  .deck::before{content:"";position:absolute;inset:-14px -18px auto;height:220px;
                pointer-events:none;opacity:0;transition:opacity .5s ease;border-radius:4px}

  .deck.valentine{--acc:#e8788f;--sc:#f2aabb;--rule:#3b2b3c}
  .deck.valentine::before{opacity:1;
    background:radial-gradient(120% 100% at 22% 0%, rgba(232,120,143,.13), transparent 62%)}

  .deck.halloween{--acc:#ff8c42;--sc:#e6a63f;--rule:#3a3145}
  .deck.halloween .rank{text-shadow:0 0 9px rgba(255,140,66,.55)}

  .deck.discovery{--acc:#a48ef2;--sc:#c0b1f7;--rule:#332f4d}
  .deck.winners{--acc:#e0b955;--sc:#ecd08a;--rule:#3b3628}
  .deck.winners::before{opacity:1;
    background:radial-gradient(120% 100% at 22% 0%, rgba(224,185,85,.12), transparent 62%)}

  .deck.siglo21{--acc:#5fb0e0;--sc:#9ad0f0;--rule:#28374a}
  .deck.siglo21::before{opacity:1;
    background:radial-gradient(120% 100% at 22% 0%, rgba(95,176,224,.11), transparent 62%)}

  .disc-titulo{font-family:var(--mono);font-size:11px;letter-spacing:.13em;
               text-transform:uppercase;color:var(--acc);margin:0 0 16px}

  /* ── medidor de descubrimiento ──────────────────────────
     La barra es puro chiste visual: no mide nada. */
  /* El medidor y su columna lateral de generos. */
  .disc{display:grid;grid-template-columns:1fr 128px;gap:28px;align-items:start}
  .genres{display:flex;flex-direction:column;gap:6px}
  .genres p{font-family:var(--mono);font-size:10px;letter-spacing:.16em;
            text-transform:uppercase;color:var(--dim);margin:0 0 4px}
  .gbtn{width:100%;text-align:left;background:transparent;border:1px solid var(--rule);
        color:var(--dim);padding:7px 11px;font-size:12.5px;font-weight:500;
        border-radius:3px;transition:color .15s,border-color .15s,background .15s}
  .gbtn:hover:not([aria-pressed="true"]){color:var(--bone);border-color:var(--dim);
        filter:none}
  .gbtn[aria-pressed="true"]{background:var(--acc);border-color:transparent;color:#16192b}

  .meter{margin:2px 0 10px}
  .track{position:relative;height:3px;border-radius:3px;margin-bottom:26px;
         background:linear-gradient(90deg,#7fd6cd 0%,#e6a63f 52%,#c96fd0 100%);
         transform-origin:left;animation:fill 1.1s cubic-bezier(.2,.8,.3,1) both}
  @keyframes fill{from{transform:scaleX(0)}to{transform:scaleX(1)}}
  .track i{position:absolute;top:50%;width:9px;height:9px;border-radius:50%;
           background:var(--night);border:2px solid currentColor;
           transform:translate(-50%,-50%)}
  .track i:nth-child(1){left:16.6%;color:#7fd6cd}
  .track i:nth-child(2){left:50%;color:#e6a63f}
  .track i:nth-child(3){left:83.3%;color:#c96fd0}

  .stops{display:grid;grid-template-columns:repeat(3,1fr);gap:26px}
  /* Centradas: asi cada etiqueta cae justo debajo de su punto en la barra. */
  .stop-label{font-family:var(--mono);font-size:11px;letter-spacing:.14em;
              text-transform:uppercase;margin:0 0 14px;color:var(--dim);
              text-align:center}
  .stops>div:nth-child(1) .stop-label{color:#7fd6cd}
  .stops>div:nth-child(2) .stop-label{color:#e6a63f}
  .stops>div:nth-child(3) .stop-label{color:#c96fd0}
  .stop-film img{width:100%;border-radius:2px;background:var(--panel);display:block;
                 margin-bottom:12px}
  .stop-film .st{font-family:var(--serif);font-size:19px;line-height:1.15}
  .stop-film .st a{color:var(--bone);text-decoration:none}
  .stop-film .st a:hover{text-decoration:underline;text-decoration-color:currentColor}
  .stop-film .sm{font-family:var(--mono);font-size:11px;color:var(--dim);margin-top:6px}
  .stop-none{font-family:var(--mono);font-size:11.5px;color:var(--dim)}
  .disclaimer{font-family:var(--mono);font-size:11px;color:var(--dim);
              margin:24px 0 0;padding-top:14px;border-top:1px solid var(--rule)}
  .mas-row{display:flex;gap:8px;align-items:center;margin-top:22px;flex-wrap:wrap}
  .mas-row .ronda{font-family:var(--mono);font-size:11px;color:var(--dim)}
  button.mas{margin-top:0;padding:10px 16px;font-size:12.5px}
  .pick .mas-row{margin-top:14px;gap:6px}
  .pick button.mas{flex:1;padding:9px 8px;font-size:12px}
  .pick #atrasPick{flex:0 0 38px}
  button.mas:disabled{opacity:.4;cursor:default;color:var(--dim)}

  .warn{color:var(--sc,var(--beam))}

  /* ── Trivial ─────────────────────────────────────────── */
  button.tvbtn{margin-top:9px;padding:11px;font-size:12.5px;
               color:var(--rose);border-color:var(--rose)}
  button.tvbtn:hover:not(:disabled){background:rgba(222,126,152,.09)}

  .tv{--acc:var(--rose)}
  .tv h3{font-family:var(--geo);font-weight:600;font-size:23px;margin:0 0 4px;
         color:var(--bone)}
  .tv .kicker{font-family:var(--mono);font-size:11px;letter-spacing:.16em;
              text-transform:uppercase;color:var(--acc);margin:0 0 22px}
  .tv .campo{font-family:var(--mono);font-size:10.5px;letter-spacing:.14em;
             text-transform:uppercase;color:var(--dim);margin:0 0 8px}
  .tv-sets{display:flex;gap:8px;flex-wrap:wrap;margin-bottom:24px}
  .tv-nombres{display:grid;grid-template-columns:1fr 1fr;gap:12px;margin-bottom:26px}
  .tv-acciones{display:flex;gap:8px;flex-wrap:wrap;align-items:center}
  .tv-acciones button{width:auto;padding:12px 20px;font-size:13px}
  .tv .primario{background:var(--clay);color:#fff;border:0;font-weight:600}

  .tv-barra{display:flex;justify-content:space-between;align-items:baseline;
            font-family:var(--mono);font-size:11.5px;color:var(--dim);
            padding-bottom:12px;border-bottom:1px solid var(--edge);margin-bottom:22px}
  .tv-barra b{color:var(--bone);font-weight:500}

  .tv-preg{font-family:var(--serif);font-size:clamp(24px,4.5vw,32px);line-height:1.15;
           margin:0 0 20px;color:var(--bone)}
  .tv-par{display:grid;grid-template-columns:1fr 1fr;gap:20px;margin:0 0 24px}
  .tv-film{text-align:center}
  .tv-film img{width:100%;max-width:148px;border-radius:3px;background:var(--panel);
               display:block;margin:0 auto}
  .tv-film .hueco{width:100%;max-width:148px;aspect-ratio:2/3;border-radius:3px;
                  background:var(--panel);margin:0 auto}
  .tv-film .t{font-size:14px;line-height:1.25;margin-top:10px}
  .tv-film .lado{font-family:var(--mono);font-size:10px;letter-spacing:.16em;
                 text-transform:uppercase;color:var(--dim);margin-bottom:8px}
  .tv-film .dato{font-family:var(--serif);font-size:26px;color:var(--acc);margin-top:8px}

  .tv-turno{font-family:var(--mono);font-size:12px;color:var(--acc);
            margin:0 0 12px;letter-spacing:.04em}
  .tv-ops{display:grid;grid-template-columns:1fr 1fr 1fr;gap:8px}
  .tv-ops button{width:100%;background:transparent;border:1px solid var(--edge);
                 color:var(--bone);font-weight:500;padding:13px 8px;font-size:13px}
  .tv-ops button:hover:not(:disabled){border-color:var(--acc);filter:none}

  .tv-rev{display:grid;grid-template-columns:1fr 1fr;gap:10px;margin:0 0 18px}
  .tv-rev div{border:1px solid var(--edge);border-radius:3px;padding:12px 14px}
  .tv-rev .quien{font-family:var(--mono);font-size:10.5px;letter-spacing:.12em;
                 text-transform:uppercase;color:var(--dim);margin-bottom:6px}
  .tv-rev .eligio{font-size:15px}
  .tv-rev .bien{color:#7fd6cd}
  .tv-rev .mal{color:var(--signal)}
  .tv-veredicto{font-family:var(--mono);font-size:12.5px;color:var(--dim);
                margin:0 0 18px;line-height:1.7}
  .tv-veredicto b{color:var(--bone);font-weight:500}

  .tv-final{display:grid;grid-template-columns:1fr 1fr;gap:12px;margin:0 0 22px}
  .tv-final div{border:1px solid var(--edge);border-radius:3px;padding:18px;
                text-align:center}
  .tv-final .n{font-family:var(--mono);font-size:11px;letter-spacing:.12em;
               text-transform:uppercase;color:var(--dim)}
  .tv-final .p{font-family:var(--serif);font-size:44px;color:var(--acc);line-height:1;
               margin-top:6px}
  .tv-final .gana{border-color:var(--acc)}
  .tv-gana{font-family:var(--serif);font-size:clamp(24px,5vw,34px);margin:0 0 22px;
           color:var(--bone)}

  @media (max-width:560px){
    .tv-nombres{grid-template-columns:1fr}
    .tv-ops{grid-template-columns:1fr}
  }

  .credits{max-width:760px;margin:0 auto;padding:0 24px 60px;
           font-family:var(--mono);font-size:11.5px;color:var(--dim);line-height:1.9}
  .credits .sep{color:var(--edge);margin:0 6px}
  .credits a{color:var(--dim);text-decoration:none;border-bottom:1px solid var(--edge);
             padding-bottom:1px;transition:color .15s,border-color .15s}
  .credits a:hover{color:var(--bone);border-color:var(--beam)}

  .deck-label{font-family:var(--mono);font-size:11px;letter-spacing:.18em;
              text-transform:uppercase;color:var(--acc);margin:0 0 2px}

  /* Dos columnas solo cuando hay modo activo: la recomendacion vive a la derecha. */
  .split{display:grid;grid-template-columns:1fr 232px;gap:30px;align-items:start}

  .pick{border:1px solid var(--rule);border-radius:3px;padding:16px;
        position:sticky;top:20px}
  .pick h4{font-family:var(--mono);font-size:10.5px;letter-spacing:.16em;
           text-transform:uppercase;color:var(--acc);margin:0 0 12px;font-weight:500}
  .pick img{width:100%;border-radius:2px;display:block;margin-bottom:12px;
            background:var(--panel)}
  .pick .pt{font-family:var(--serif);font-size:20px;line-height:1.15;margin:0 0 5px}
  .pick .pt a{color:var(--bone);text-decoration:none}
  .pick .pt a:hover{text-decoration:underline;text-decoration-color:var(--acc)}
  .pick .pm{font-family:var(--mono);font-size:11px;color:var(--dim);margin:0 0 11px}
  .pick .pr{font-family:var(--serif);font-size:23px;color:var(--sc);line-height:1}
  .pick .pw{font-size:12px;color:var(--dim);margin:11px 0 0;line-height:1.45;
            padding-top:11px;border-top:1px solid var(--rule)}
  .pick .loading{font-family:var(--mono);font-size:11.5px;color:var(--dim)}

  ol{list-style:none;margin:0;padding:0}
  li{display:grid;grid-template-columns:34px 46px 1fr auto;gap:14px;align-items:center;
     padding:15px 0;border-bottom:1px solid var(--rule,var(--edge));
     opacity:0;animation:in .35s ease forwards}
  @keyframes in{to{opacity:1}}
  .rank{font-family:var(--mono);font-size:12px;color:var(--acc)}
  .poster{width:46px;height:69px;border-radius:2px;background:var(--panel);object-fit:cover}
  .title{font-size:15.5px}
  .title a{color:var(--bone);text-decoration:none}
  .title a:hover{text-decoration:underline;text-decoration-color:var(--sc)}
  .meta{font-family:var(--mono);font-size:11.5px;color:var(--dim);margin-top:3px}
  .prov{font-family:var(--mono);font-size:11px;color:#6a7299;margin-top:3px}
  .prov .seen{color:var(--sc)}
  .score{font-family:var(--serif);font-size:27px;color:var(--sc);text-align:right;
         line-height:1}
  .score small{display:block;font-family:var(--mono);font-size:10px;color:var(--dim);
               margin-top:4px;letter-spacing:.06em}
  .score.none{color:var(--dim);font-size:15px}
  .empty{padding:26px 0;color:var(--dim);font-size:14px}

  @media (max-width:640px){
    .split{grid-template-columns:1fr;gap:22px}
    .pick{position:static}
    .stops{grid-template-columns:1fr;gap:16px}
    .stop-label{text-align:left}
    .disc{grid-template-columns:1fr;gap:18px}
    .genres{flex-direction:row;flex-wrap:wrap;order:-1}
    .gbtn{width:auto}
    .genres p{width:100%;margin:0}
  }
  @media (max-width:560px){
    .logo{flex-wrap:wrap;gap:10px}
    .bill{grid-template-columns:1fr;gap:8px}
    .amp{text-align:center;font-size:34px;padding:0}
    .hint{margin-top:2px}
    li{grid-template-columns:26px 40px 1fr auto;gap:11px}
  }
  @media (prefers-reduced-motion:reduce){
    li{animation:none;opacity:1}
    .deck::before{transition:none}
    .track{animation:none}
  }
</style>
</head>
<body>
<div class="wrap">
  <p class="eyebrow">Letterboxd</p>
  <button class="logo" id="logo" aria-label="Volver al inicio">
    <svg viewBox="8 5 84 50" role="img" aria-hidden="true">
      <defs>
        <clipPath id="lente"><circle cx="33" cy="30" r="25"/></clipPath>
      </defs>
      <circle cx="33" cy="30" r="25" fill="#e3b85a"/>
      <circle cx="67" cy="30" r="25" fill="#de7e98"/>
      <g clip-path="url(#lente)">
        <circle cx="67" cy="30" r="25" fill="#c4693f"/>
      </g>
    </svg>
    <span class="word">doublebill</span>
  </button>
  <div id="app">
  <p class="lede">Las peliculas que ambos quieren ver, ordenadas por el promedio
     de Letterboxd.</p>

  <div class="bill">
    <div>
      <input type="text" id="a" placeholder="usuario" autocomplete="off" spellcheck="false">
      <label class="opt"><input type="checkbox" id="seenA"> Agregar vistas recientes</label>
    </div>
    <div class="mid">
      <span class="amp" aria-hidden="true">&amp;</span>
      <span class="hint">&iquest;alguno repite?</span>
    </div>
    <div>
      <input type="text" id="b" placeholder="otro usuario" autocomplete="off" spellcheck="false">
      <label class="opt"><input type="checkbox" id="seenB"> Agregar vistas recientes</label>
    </div>
  </div>
  <button id="go">Match watchlists</button>
  <button class="ghost sinlb" id="sinCuenta">Usar sin Letterboxd</button>
  <button class="ghost tvbtn" id="btnTrivia">Trivial &mdash; 2 jugadores</button>
  <p class="note">Basta el nombre de usuario; tambien vale pegar el link del perfil.
     Solo funciona con perfiles publicos, y de las peliculas ya vistas solo se puede
     leer la actividad reciente.</p>

  <p class="status" id="status" role="status" aria-live="polite"></p>
  <div id="gate"></div>
  <div id="out"></div>
  <div id="deck"></div>
  </div>

  <div id="trivia" class="tv" hidden></div>
</div>

<footer class="credits">
  Hecho por <a href="https://letterboxd.com/alvarovadilloz/" target="_blank" rel="noopener">alvarovadilloz</a>
  <span class="sep">|</span>
  Feedback: <a href="https://www.instagram.com/alvaro.vadillo.z/" target="_blank" rel="noopener">alvaro.vadillo.z</a>
</footer>

<script>
const $ = id => document.getElementById(id);
const PAGE_SIZE = 10;
const AUTO_RANK = 80;          // arriba de esto, preguntamos antes de pedir ratings

// Un modo pasa si la pelicula tiene AL MENOS UNO de estos generos (OR, no AND).
// Los modos con medidor no filtran la lista: solo agregan el trio.
const MODES = {
  valentine: { label:"Modo San Valentin",   genres:["romance"], boton:"\u2665 San Valentin" },
  halloween: { label:"Modo Halloween",      genres:["horror"],  boton:"\u25c8 Halloween" },
  discovery: { label:"Modo Descubrimiento", genres:null, medidor:true, boton:"\u25d0 Descubrimiento",
               titulo:"Top all-time por Letterboxd + Underseen" },
  winners:   { label:"Modo Premiadas",      genres:null, medidor:true, boton:"\uD83C\uDFC6 Premiadas",
               titulo:"Ganadoras a Mejor Pelicula: Oscar's \u00b7 Cannes \u00b7 BAFTA" },
  siglo21:   { label:"Modo Siglo XXI",      genres:null, medidor:true, boton:"\u25c9 Siglo XXI",
               titulo:"Las mejor puntuadas en IMDb de este siglo" }
};

// El slug es lo que entiende Letterboxd; el texto es lo que se ve en el boton.
const DISC_GENRES = [
  ["horror","horror"], ["romance","romance"], ["comedy","comedy"],
  ["thriller","thriller"], ["drama","drama"], ["action","action"],
  ["science-fiction","sci-fi"], ["war","war"], ["animation","animation"]
];
const nombreGenero = g => (DISC_GENRES.find(x => x[0] === g) || [g, g])[1];

let state = { films: [], shown: 0, prov: {}, users: null, mode: null,
              hasGenres: false, picks: {}, stages: {}, genre: null,
              skip: {}, agotado: {}, pickSkip: {}, pickAgotado: {},
              hist: {}, idx: {}, pickHist: {}, pickIdx: {}, sinCuenta: false };

const stars = r => {
  const full = Math.floor(r), half = r - full >= 0.25 && r - full < 0.75, up = r - full >= 0.75;
  return "\u2605".repeat(full + (up ? 1 : 0)) + (half ? "\u00bd" : "");
};
const esc = s => String(s).replace(/[&<>"]/g, c =>
  ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]));

function show(msg, isErr){
  const s = $("status");
  s.textContent = msg || "";
  s.className = "status" + (isErr ? " err" : "");
}

async function post(path, body){
  const res = await fetch(path, {
    method:"POST", headers:{"Content-Type":"application/json"},
    body: JSON.stringify(body)
  });
  const data = await res.json();
  if(!res.ok) throw new Error(data.error || "Algo fallo del lado del servidor.");
  return data;
}

async function cross(){
  const a = $("a").value.trim(), b = $("b").value.trim();
  if(!a || !b){ show("Faltan los dos perfiles.", true); return; }

  $("go").disabled = true;
  $("out").innerHTML = "";
  $("deck").innerHTML = "";
  $("gate").innerHTML = "";
  state = { films: [], shown: 0, prov: {}, users: null, mode: null,
            hasGenres: false, picks: {}, stages: {}, genre: null,
            skip: {}, agotado: {}, pickSkip: {}, pickAgotado: {},
            hist: {}, idx: {}, pickHist: {}, pickIdx: {}, sinCuenta: false };
  show("Leyendo los dos perfiles\u2026");

  try{
    const d = await post("/api/cross", {
      a, b, seen_a: $("seenA").checked, seen_b: $("seenB").checked
    });
    state.users = d;
    d.shared.forEach(s => state.prov[s.slug] = {a:s.a, b:s.b});
    renderTally(d);

    if(d.shared.length === 0){
      // Sin coincidencias no hay ranking, pero Descubrimiento no depende de el:
      // solo necesita los dos perfiles. Pintamos igual para dejarlo disponible.
      state.films = [];
      state.hasGenres = false;
      paint();
      show("");
      return;
    }

    const pending = d.shared.length - d.cached;
    if(d.shared.length > AUTO_RANK && pending > AUTO_RANK){
      show("");
      gate(d.shared, pending);
    }else{
      await doRank(d.shared.map(s => s.slug));
    }
  }catch(e){
    show(e.message, true);
  }finally{
    $("go").disabled = false;
  }
}

function gate(shared, pending){
  const secs = Math.ceil(pending / 3 * 0.9);   // 3 = FETCH_WORKERS del servidor
  $("gate").innerHTML = `<div class="gate">
      <p>Son <b>${shared.length}</b> coincidencias. Para ordenarlas hay que pedirle el
         rating a Letterboxd de cada una \u2014 unos ${secs} segundos la primera vez,
         instantaneo despues.</p>
      <button id="rankBtn">Pedir los ${shared.length} ratings</button>
    </div>`;
  $("rankBtn").addEventListener("click", async () => {
    $("rankBtn").disabled = true;
    $("gate").innerHTML = "";
    try{ await doRank(shared.map(s => s.slug)); }
    catch(e){ show(e.message, true); }
  });
}

async function doRank(slugs){
  show(`Pidiendo ${slugs.length} ratings\u2026`);
  const films = await post("/api/rank", { slugs });
  state.films = films;
  state.hasGenres = films.some(f => (f.genres || []).length > 0);
  paint();
  show("");
}

// Peliculas visibles con el modo actual. Sin modo (o en descubrimiento), todas.
function visible(){
  const want = state.mode && MODES[state.mode].genres;
  if(!want) return state.films;
  return state.films.filter(f => (f.genres || []).some(g => want.includes(g)));
}

function setMode(mode){
  state.mode = (state.mode === mode) ? null : mode;   // volver a tocar = apagar
  paint();
  if(state.mode && MODES[state.mode].medidor) cargarStages();
  else if(state.mode) cargarPick(state.mode);
}

// Redibuja botones + deck desde cero. Cambiar de modo no pide nada al servidor
// para la lista; las recomendaciones sí, pero se guardan por modo.
function paint(){
  const host = $("deck");
  const list = visible();
  state.shown = 0;

  const btn = m => {
    const on = state.mode === m;
    const filtra = MODES[m].genres;
    const dis = (filtra && !state.hasGenres) ? "disabled" : "";
    const title = dis ? ' title="Letterboxd no devolvio generos para estas peliculas."' : "";
    return `<button class="mode" data-mode="${m}" aria-pressed="${on}" ${dis}${title}>
              ${MODES[m].boton}
            </button>`;
  };

  const conPick = state.mode && MODES[state.mode].genres;   // solo los de genero
  const disc = state.mode && MODES[state.mode].medidor;
  host.innerHTML = `
    <div class="modes">${
      (state.sinCuenta ? ["discovery","winners","siglo21"]
                       : ["valentine","halloween","discovery","winners","siglo21"]).map(btn).join("")
    }</div>
    <div class="deck ${state.mode || ""}">
      ${disc ? `<div class="disc">
                  <div>
                    ${MODES[state.mode].titulo
                      ? `<p class="disc-titulo">${esc(MODES[state.mode].titulo)}</p>` : ""}
                    <div class="meter" id="meter"></div>
                  </div>
                  <aside class="genres" id="genres"></aside>
                </div>` : ""}
      <div class="${conPick ? "split" : ""}">
        <div id="cards"></div>
        ${conPick ? '<aside class="pick" id="pick"></aside>' : ""}
      </div>
    </div>`;

  host.querySelectorAll(".mode").forEach(b =>
    b.addEventListener("click", () => setMode(b.dataset.mode)));

  if(disc){
    const caja = $("genres");
    caja.innerHTML = `<p>Genero</p>` + DISC_GENRES.map(([g, txt]) =>
      `<button class="gbtn" data-g="${g}" aria-pressed="${state.genre === g}">${txt}</button>`
    ).join("");
    caja.querySelectorAll(".gbtn").forEach(b =>
      b.addEventListener("click", () => setGenre(b.dataset.g)));
  }

  const cards = $("cards");

  if(disc){
    pintarStages();
    return;                      // sin ranking abajo: el trio se queda con la pantalla
  }
  if(state.mode){
    cards.innerHTML = `<p class="deck-label">${MODES[state.mode].label} \u00b7
      ${list.length} de ${state.films.length}</p>`;
  }
  if(conPick) pintarPick(state.mode);

  if(state.films.length === 0){
    const mismo = state.users && state.users.same;
    cards.insertAdjacentHTML("beforeend",
      `<p class="empty">${mismo
        ? "Con un solo perfil no hay cruce ni ranking, pero Descubrimiento y Premiadas funcionan igual."
        : "No hay ranking que mostrar, pero el modo Descubrimiento funciona igual: no depende de lo que tengan en comun."}</p>`);
    return;
  }
  if(list.length === 0){
    cards.insertAdjacentHTML("beforeend",
      `<p class="empty">Ninguna de las ${state.films.length} coincidencias entra en este
       modo. Vuelve a tocar el boton para ver todas.</p>`);
    return;
  }
  more();
}

// ── medidor de descubrimiento ──
// Un solo genero a la vez: volver a tocar el activo lo apaga.
function setGenre(g){
  state.genre = (state.genre === g) ? null : g;
  paint();
  cargarStages();
}

function claveGenero(){ return `${state.mode}|${state.genre || "todos"}`; }

// mas=true pide la siguiente ronda en vez de reusar lo que ya se busco.
// dir: undefined = primera carga | 1 = siguiente | -1 = anterior
// Las rondas ya vistas se guardan, asi que retroceder (y volver a avanzar
// sobre lo ya visto) no cuesta ninguna peticion.
async function cargarStages(dir){
  const clave = claveGenero();
  if(!state.hist[clave]){
    state.hist[clave] = [];
    state.idx[clave] = -1;
    state.skip[clave] = [];
  }
  const h = state.hist[clave];

  if(dir === -1){                              // atras: siempre desde memoria
    if(state.idx[clave] > 0){ state.idx[clave]--; pintarStages(); }
    return;
  }
  if(dir === 1 && state.idx[clave] < h.length - 1){
    state.idx[clave]++;                        // adelante sobre lo ya cargado
    pintarStages();
    return;
  }
  if(dir === undefined && h.length){ pintarStages(); return; }

  // Aqui si hace falta una ronda nueva.
  state.stages[clave] = null;                  // en curso
  pintarStages();

  try{
    const d = await post("/api/discover", {
      a: state.users.a.user, b: state.users.b.user,
      genre: state.genre, skip: state.skip[clave], modo: state.mode
    });
    const hayAlgo = d.stages.some(e => e.film);

    if(d.incierto){
      // El servidor no pudo preguntarle a Letterboxd si las vieron. No es lo
      // mismo que "ya las vieron todas", y decirlo importa.
      state.stages[clave] = h.length
        ? undefined
        : { error: "Letterboxd no respondio a la verificacion. Prueba de nuevo en un momento." };
    }else if(!hayAlgo){
      state.agotado[clave] = true;             // no vaciar lo que ya se ve
      state.stages[clave] = undefined;
    }else{
      h.push(d.stages);
      state.idx[clave] = h.length - 1;
      state.stages[clave] = undefined;         // manda el historial
      d.stages.forEach(e => { if(e.film) state.skip[clave].push(e.film.slug); });
    }
  }catch(e){
    state.stages[clave] = { error: e.message };
  }
  if(state.mode && MODES[state.mode].medidor && claveGenero() === clave)
    pintarStages();
}

function pintarStages(){
  const box = $("meter");
  if(!box) return;
  const clave = claveGenero();
  const h = state.hist[clave] || [];
  const i = state.idx[clave];
  // Si hay historial, manda el historial; state.stages solo lleva error o carga.
  const s = (h.length && i >= 0 && state.stages[clave] === undefined)
    ? h[i] : state.stages[clave];

  if(s === undefined || s === null){
    const que = state.genre ? `peliculas de ${nombreGenero(state.genre)}` : "el medidor";
    box.innerHTML = `<div class="track"><i></i><i></i><i></i></div>
      <p class="stop-none">Buscando ${esc(que)}\u2026</p>`;
    return;
  }
  if(s.error){
    box.innerHTML = `<p class="stop-none">No se pudo medir: ${esc(s.error)}</p>`;
    return;
  }

  const col = e => {
    const f = e.film;
    const cuerpo = !f
      ? `<p class="stop-none">${state.genre
           ? "Nada de " + esc(nombreGenero(state.genre)) + " por aca." : "Ya vieron todo aca."}</p>`
      : `<div class="stop-film">
           ${f.poster ? `<img src="${esc(f.poster)}" alt="" loading="lazy">` : ""}
           <div class="st"><a href="${esc(f.url)}" target="_blank" rel="noopener">${esc(f.title)}</a></div>
           <div class="sm">${f.year || ""}${f.rating ? " \u00b7 " + f.rating.toFixed(2) : ""}</div>
         </div>`;
    // La parada del medio va sin etiqueta, pero el hueco se mantiene para que
    // las tres columnas arranquen a la misma altura.
    const etiqueta = e.label
      ? `<p class="stop-label">${esc(e.label)}</p>`
      : `<p class="stop-label" aria-hidden="true">&nbsp;</p>`;
    return `<div>${etiqueta}${cuerpo}</div>`;
  };

  // Atras solo se habilita si hay rondas guardadas detras: nunca pide nada.
  const hayAtras = i > 0;
  const agotado = state.agotado[clave] && i >= h.length - 1;
  const ronda = h.length ? `<span class="ronda">${i + 1} de ${h.length}</span>` : "";

  box.innerHTML = `<div class="track"><i></i><i></i><i></i></div>
    <div class="stops">${s.map(col).join("")}</div>
    <div class="mas-row">
      <button class="ghost mas" id="atrasStages" ${hayAtras ? "" : "disabled"}>
        \u2190 Anteriores</button>
      <button class="ghost mas" id="masStages" ${agotado ? "disabled" : ""}>
        ${agotado ? "No hay mas por aca" : "Mas recomendaciones \u2192"}</button>
      ${ronda}
    </div>
    <p class="disclaimer">${state.sinCuenta
      ? "Sin perfiles no se puede saber que ya vieron: estas son las mejor valoradas."
      : "Probablemente ninguna la vieron."}</p>`;

  const bA = $("atrasStages");
  if(bA) bA.addEventListener("click", () => cargarStages(-1));
  const bM = $("masStages");
  if(bM) bM.addEventListener("click", () => cargarStages(1));
}

// ── recomendacion del top 500 que ninguno vio ──
// mas=true pide la siguiente en vez de reusar la que ya se busco.
// dir: undefined = primera carga | 1 = siguiente | -1 = anterior
async function cargarPick(mode, dir){
  const h = state.pickHist[mode] || (state.pickHist[mode] = []);
  if(!state.pickSkip[mode]) state.pickSkip[mode] = [];
  if(state.pickIdx[mode] === undefined) state.pickIdx[mode] = -1;

  if(dir === -1){                              // atras: siempre desde memoria
    if(state.pickIdx[mode] > 0){ state.pickIdx[mode]--; pintarPick(mode); }
    return;
  }
  if(dir === 1 && state.pickIdx[mode] < h.length - 1){
    state.pickIdx[mode]++;
    pintarPick(mode);
    return;
  }
  if(dir === undefined && h.length){ pintarPick(mode); return; }

  state.picks[mode] = null;                    // en curso
  pintarPick(mode);

  try{
    const d = await post("/api/pick", {
      mode, a: state.users.a.user, b: state.users.b.user,
      skip: state.pickSkip[mode]
    });
    if(d.incierto){
      state.picks[mode] = h.length
        ? undefined
        : { error: "Letterboxd no respondio a la verificacion. Prueba de nuevo en un momento." };
    }else if(!d.pick){
      state.pickAgotado[mode] = true;
      state.picks[mode] = h.length ? undefined : null;
    }else{
      h.push(d.pick);
      state.pickIdx[mode] = h.length - 1;
      state.picks[mode] = undefined;
      state.pickSkip[mode].push(d.pick.slug);
    }
  }catch(e){
    state.picks[mode] = { error: e.message };
  }
  if(state.mode === mode) pintarPick(mode);

}

function pintarPick(mode){
  const box = $("pick");
  if(!box) return;
  const titulo = "Para esta noche";
  const h = state.pickHist[mode] || [];
  const i = state.pickIdx[mode];
  const p = (h.length && i >= 0 && state.picks[mode] === undefined)
    ? h[i] : state.picks[mode];

  if(p === undefined){
    box.innerHTML = `<h4>${titulo}</h4>
      <p class="loading">Buscando en el top 500\u2026</p>`;
    return;
  }
  if(p === null){
    box.innerHTML = `<h4>${titulo}</h4>
      <p class="pw" style="border:0;padding:0">Ya vieron todas las del genero que hay
      en el top 500. Impresionante.</p>`;
    return;
  }
  if(p.error){
    box.innerHTML = `<h4>${titulo}</h4>
      <p class="pw" style="border:0;padding:0">No se pudo buscar: ${esc(p.error)}</p>`;
    return;
  }

  const gen = (p.genres || []).map(g => esc(g.replace(/-/g," "))).join(", ");
  const hayAtras = i > 0;
  const agotado = state.pickAgotado[mode] && i >= h.length - 1;
  const boton = `<div class="mas-row">
      <button class="ghost mas" id="atrasPick" ${hayAtras ? "" : "disabled"}>\u2190</button>
      <button class="ghost mas" id="masPick" ${agotado ? "disabled" : ""}>
        ${agotado ? "No hay mas" : "Otra \u2192"}</button>
    </div>`;

  box.innerHTML = `<h4>${titulo}</h4>
    ${p.poster ? `<img src="${esc(p.poster)}" alt="" loading="lazy">` : ""}
    <p class="pt"><a href="${esc(p.url)}" target="_blank" rel="noopener">${esc(p.title)}</a></p>
    <p class="pm">${p.year || ""}${gen ? " \u00b7 " + gen : ""}</p>
    <p class="pr">${p.rating ? p.rating.toFixed(2) : "\u2014"}</p>
    <p class="pw">Puesto ${p.rank} del top 500 de Letterboxd. Probablemente
       ninguno de los dos la vio.</p>
    ${boton}`;

  const bA = $("atrasPick");
  if(bA) bA.addEventListener("click", () => cargarPick(mode, -1));
  const bM = $("masPick");
  if(bM) bM.addEventListener("click", () => cargarPick(mode, 1));
}

function renderTally(d){
  const line = p => `${esc(p.user)}: <b>${p.watchlist}</b> por ver` +
    (p.include_seen ? ` + <b>${p.seen}</b> vistas recientes = <b>${p.pool}</b>` : "");
  let html = `<p class="tally">`;
  html += d.same
    ? `${line(d.a)}<br><span class="warn">Es el mismo perfil dos veces: esto no es un
       cruce, es su propio watchlist ordenado por rating.</span><br>`
    : `${line(d.a)}<br>${line(d.b)}<br>`;
  html += d.shared.length === 0
    ? `\u2192 <b>ninguna en comun</b> todavia. Buena excusa para que cada uno le
       agregue algo al otro.</p>`
    : `\u2192 <b>${d.shared.length}</b> en comun</p>`;
  $("out").innerHTML = html;
}

function more(){
  const films = visible();
  const slice = films.slice(state.shown, state.shown + PAGE_SIZE);
  const start = state.shown;
  const rows = slice.map((f, i) => {
    const n = start + i + 1;
    const p = state.prov[f.slug] || {};
    const tag = (user, kind) => kind === "seen"
      ? `<span class="seen">${esc(user)} ya la vio</span>`
      : `${esc(user)} por ver`;
    const poster = f.poster
      ? `<img class="poster" src="${esc(f.poster)}" alt="" loading="lazy">`
      : `<span class="poster"></span>`;
    const score = f.rating
      ? `<div class="score">${f.rating.toFixed(2)}<small>${stars(f.rating)}</small></div>`
      : `<div class="score none">sin rating</div>`;
    const votes = f.votes ? ` \u00b7 ${f.votes.toLocaleString("es")} ratings` : "";
    const gen = (f.genres || []).length
      ? " \u00b7 " + f.genres.map(g => esc(g.replace(/-/g," "))).join(", ") : "";
    const proc = state.users.same
      ? tag(state.users.a.user, p.a)
      : `${tag(state.users.a.user, p.a)} \u00b7 ${tag(state.users.b.user, p.b)}`;
    return `<li style="animation-delay:${i*45}ms">
      <span class="rank">${String(n).padStart(2,"0")}</span>
      ${poster}
      <div>
        <div class="title"><a href="${esc(f.url)}" target="_blank" rel="noopener">${esc(f.title)}</a></div>
        <div class="meta">${f.year || ""}${votes}${gen}</div>
        <div class="prov">${proc}</div>
      </div>
      ${score}
    </li>`;
  }).join("");

  const cards = $("cards");
  const old = cards.querySelector(".more");
  if(old) old.remove();

  const ol = document.createElement("ol");
  ol.innerHTML = rows;
  cards.appendChild(ol);
  state.shown += slice.length;

  const left = films.length - state.shown;
  if(left > 0){
    const btn = document.createElement("button");
    btn.className = "ghost more";
    btn.textContent = `Ver las siguientes ${Math.min(PAGE_SIZE, left)} \u00b7 quedan ${left}`;
    btn.addEventListener("click", more);
    cards.appendChild(btn);
  }else if(films.length > PAGE_SIZE){
    const p = document.createElement("p");
    p.className = "note more";
    p.textContent = `Esas son las ${films.length}. No hay mas.`;
    cards.appendChild(p);
  }
}

// Sin perfiles no hay watchlist que cruzar, pero las listas publicas y las
// recomendaciones funcionan igual: se entra directo al medidor.
function sinCuenta(){
  state = { films: [], shown: 0, prov: {}, users: { a:{user:""}, b:{user:""} },
            mode: null, hasGenres: false, picks: {}, stages: {}, genre: null,
            skip: {}, agotado: {}, pickSkip: {}, pickAgotado: {},
            hist: {}, idx: {}, pickHist: {}, pickIdx: {}, sinCuenta: true };
  $("out").innerHTML = "";
  $("gate").innerHTML = "";
  show("");
  paint();
  setMode("discovery");
}


// ═══════════════════════════════════════════════════════════
// Trivial: juego local de dos jugadores. Todo vive en memoria;
// recargar la pagina pierde la partida y esta bien asi.
// ═══════════════════════════════════════════════════════════

// Lista extensible. Para sumar una pregunta basta con anadir una entrada:
// nadie mas necesita cambiar. "disponible" deja fuera la pregunta cuando
// alguna de las dos peliculas no tiene ese dato.
//
// Pendiente: {"id":"duracion", enunciado:"\u00bfCu\u00e1l dura m\u00e1s?",
//   valor:f=>f.runtime, gana:"mayor", formato:v=>v+" min"} -- falta que la
//   semilla traiga la duracion.
const TV_PREGUNTAS = [
  { id:"anio",
    enunciado:"\u00bfCu\u00e1l se estren\u00f3 antes?",
    valor: f => f.year,
    gana: "menor",
    formato: v => String(v) },
  { id:"rating",
    enunciado:"\u00bfCu\u00e1l tiene mejor rating?",
    valor: f => f.rating,
    gana: "mayor",
    formato: v => Number(v).toFixed(2) },
];

const TV_SETS = [
  ["descubrimiento","Descubrimiento"],
  ["siglo21","Siglo XXI"],
  ["premiadas","Premiadas"],
];
const TV_RONDAS = 7;
const TV_OPS = [["izq","Izquierda"],["empate","Empate"],["der","Derecha"]];

let TV = null;                       // partida en curso
let TVnombres = ["", ""];            // se conservan entre partidas
let TVsets = ["descubrimiento"];

const tvBox = () => $("trivia");

function tvAbrir(){
  $("app").hidden = true;
  tvBox().hidden = false;
  tvConfig();
}
function tvCerrar(){
  TV = null;
  tvBox().hidden = true;
  tvBox().innerHTML = "";
  $("app").hidden = false;
}

// ── configuracion ──
function tvConfig(aviso){
  const sets = TV_SETS.map(([id,txt]) =>
    `<button class="gbtn" data-set="${id}" aria-pressed="${TVsets.includes(id)}">${txt}</button>`
  ).join("");
  tvBox().innerHTML = `
    <h3>Trivial</h3>
    <p class="kicker">Dos jugadores, un dispositivo</p>
    <p class="campo">De donde salen las peliculas</p>
    <div class="tv-sets">${sets}</div>
    <p class="campo">Nombres (opcional)</p>
    <div class="tv-nombres">
      <input type="text" id="tvN1" placeholder="Jugador 1" value="${esc(TVnombres[0])}"
             autocomplete="off" maxlength="18">
      <input type="text" id="tvN2" placeholder="Jugador 2" value="${esc(TVnombres[1])}"
             autocomplete="off" maxlength="18">
    </div>
    ${aviso ? `<p class="tv-veredicto">${esc(aviso)}</p>` : ""}
    <div class="tv-acciones">
      <button class="primario" id="tvGo">Empezar</button>
      <button class="ghost" id="tvSalir" style="margin-top:0">Salir</button>
    </div>`;

  tvBox().querySelectorAll("[data-set]").forEach(b =>
    b.addEventListener("click", () => {
      const id = b.dataset.set;
      TVsets = TVsets.includes(id) ? TVsets.filter(x => x !== id) : TVsets.concat(id);
      tvGuardarNombres();
      tvConfig();
    }));
  $("tvGo").addEventListener("click", tvEmpezar);
  $("tvSalir").addEventListener("click", tvCerrar);
}

function tvGuardarNombres(){
  if($("tvN1")) TVnombres = [$("tvN1").value.trim(), $("tvN2").value.trim()];
}

async function tvEmpezar(){
  tvGuardarNombres();
  if(!TVsets.length){ tvConfig("Elige al menos un set."); return; }

  $("tvGo").disabled = true;
  $("tvGo").textContent = "Cargando\u2026";
  let pool;
  try{
    const r = await fetch("/api/trivia/pool?sets=" + encodeURIComponent(TVsets.join(",")));
    const d = await r.json();
    if(!r.ok) throw new Error(d.error || "No se pudo cargar el pool.");
    pool = d.pool;
  }catch(e){
    tvConfig(e.message); return;
  }

  const faltan = TV_RONDAS * 2;
  if(pool.length < faltan){
    tvConfig(`Con esos sets solo hay ${pool.length} peliculas y hacen falta `
             + `${faltan}. Marca alguno mas.`);
    return;
  }

  // Barajado de Fisher-Yates: 14 peliculas unicas para toda la partida.
  const baraja = pool.slice();
  for(let i = baraja.length - 1; i > 0; i--){
    const j = Math.floor(Math.random() * (i + 1));
    [baraja[i], baraja[j]] = [baraja[j], baraja[i]];
  }
  const elegidas = baraja.slice(0, faltan);

  const rondas = [];
  for(let i = 0; i < TV_RONDAS; i++){
    const a = elegidas[i*2], b = elegidas[i*2 + 1];
    const posibles = TV_PREGUNTAS.filter(q =>
      q.valor(a) !== null && q.valor(a) !== undefined &&
      q.valor(b) !== null && q.valor(b) !== undefined);
    const q = posibles[Math.floor(Math.random() * posibles.length)];
    rondas.push({ a, b, q, r1:null, r2:null });
  }

  TV = { rondas, i:0, turno:1, puntos:[0,0],
         nombres:[TVnombres[0] || "Jugador 1", TVnombres[1] || "Jugador 2"] };
  tvRonda();
}

// ── ronda ──
function tvCorrecta(r){
  const va = r.q.valor(r.a), vb = r.q.valor(r.b);
  if(va === vb) return "empate";
  if(r.q.gana === "menor") return va < vb ? "izq" : "der";
  return va > vb ? "izq" : "der";
}

function tvFicha(f, lado){
  const img = f.poster
    ? `<img src="${esc(f.poster)}" alt="" loading="lazy">`
    : `<div class="hueco"></div>`;
  return `<div class="tv-film">
      <p class="lado">${lado}</p>
      ${img}
      <div class="t">${esc(f.title)}</div>
    </div>`;
}

function tvBarra(){
  const t = TV.nombres;
  return `<div class="tv-barra">
      <span>Ronda <b>${TV.i + 1}</b> de ${TV_RONDAS}</span>
      <span>${esc(t[0])} <b>${TV.puntos[0]}</b> &nbsp;&middot;&nbsp;
            ${esc(t[1])} <b>${TV.puntos[1]}</b></span>
    </div>`;
}

function tvRonda(){
  const r = TV.rondas[TV.i];
  const quien = TV.nombres[TV.turno - 1];
  tvBox().innerHTML = `
    ${tvBarra()}
    <p class="tv-preg">${r.q.enunciado}</p>
    <div class="tv-par">${tvFicha(r.a,"Izquierda")}${tvFicha(r.b,"Derecha")}</div>
    <p class="tv-turno">Turno de ${esc(quien)}${TV.turno === 2
        ? " \u00b7 la respuesta anterior est\u00e1 oculta" : ""}</p>
    <div class="tv-ops">${TV_OPS.map(([v,t]) =>
      `<button data-op="${v}">${t}</button>`).join("")}</div>`;

  tvBox().querySelectorAll("[data-op]").forEach(b =>
    b.addEventListener("click", () => tvElegir(b.dataset.op)));
}

function tvElegir(op){
  const r = TV.rondas[TV.i];
  if(TV.turno === 1){
    r.r1 = op;
    TV.turno = 2;
    tvRonda();              // se repinta sin rastro de lo elegido
    return;
  }
  r.r2 = op;
  tvRevelar();
}

// ── revelacion: solo cuando los dos respondieron ──
function tvRevelar(){
  const r = TV.rondas[TV.i];
  const ok = tvCorrecta(r);
  const a1 = r.r1 === ok, a2 = r.r2 === ok;

  let p1, p2;
  if(a1 && !a2){ p1 = 1; p2 = 0; }
  else if(!a1 && a2){ p1 = 0; p2 = 1; }
  else { p1 = 0.5; p2 = 0.5; }
  TV.puntos[0] += p1;
  TV.puntos[1] += p2;

  const etiqueta = v => (TV_OPS.find(o => o[0] === v) || [v,v])[1];
  const tarjeta = (n, elec, acierto, pts) => `<div>
      <p class="quien">${esc(n)}</p>
      <p class="eligio ${acierto ? "bien" : "mal"}">${etiqueta(elec)}</p>
      <p class="quien" style="margin:6px 0 0">+${pts}</p>
    </div>`;

  const va = r.q.formato(r.q.valor(r.a));
  const vb = r.q.formato(r.q.valor(r.b));
  const ultima = TV.i === TV_RONDAS - 1;

  tvBox().innerHTML = `
    ${tvBarra()}
    <p class="tv-preg">${r.q.enunciado}</p>
    <div class="tv-par">
      ${tvFicha(r.a,"Izquierda").replace("</div>",
        `<div class="dato">${va}</div></div>`)}
      ${tvFicha(r.b,"Derecha").replace("</div>",
        `<div class="dato">${vb}</div></div>`)}
    </div>
    <p class="tv-veredicto">Respuesta correcta: <b>${etiqueta(ok)}</b></p>
    <div class="tv-rev">
      ${tarjeta(TV.nombres[0], r.r1, a1, p1)}
      ${tarjeta(TV.nombres[1], r.r2, a2, p2)}
    </div>
    <div class="tv-acciones">
      <button class="primario" id="tvNext">${ultima ? "Ver resultado" : "Siguiente ronda"}</button>
    </div>`;

  $("tvNext").addEventListener("click", () => {
    if(ultima){ tvFinal(); return; }
    TV.i++; TV.turno = 1; tvRonda();
  });
}

// ── pantalla final ──
function tvFinal(){
  const [p1, p2] = TV.puntos;
  const [n1, n2] = TV.nombres;
  const titulo = p1 === p2 ? "Empate"
    : `Gana ${esc(p1 > p2 ? n1 : n2)}`;

  tvBox().innerHTML = `
    <h3>Fin de la partida</h3>
    <p class="kicker">${TV_RONDAS} rondas</p>
    <p class="tv-gana">${titulo}</p>
    <div class="tv-final">
      <div class="${p1 >= p2 ? "gana" : ""}">
        <p class="n">${esc(n1)}</p><p class="p">${p1}</p></div>
      <div class="${p2 >= p1 ? "gana" : ""}">
        <p class="n">${esc(n2)}</p><p class="p">${p2}</p></div>
    </div>
    <div class="tv-acciones">
      <button class="primario" id="tvOtra">Jugar otra vez</button>
      <button class="ghost" id="tvSalir2" style="margin-top:0">Salir</button>
    </div>`;

  $("tvOtra").addEventListener("click", () => { TV = null; tvConfig(); });
  $("tvSalir2").addEventListener("click", tvCerrar);
}

$("btnTrivia").addEventListener("click", tvAbrir);

$("logo").addEventListener("click", () => location.reload());
$("sinCuenta").addEventListener("click", sinCuenta);
$("go").addEventListener("click", cross);
["a","b"].forEach(id => $(id).addEventListener("keydown", e => { if(e.key==="Enter") cross(); }));
</script>
</body>
</html>
"""


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def _send(self, code, body, ctype):
        data = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _json(self, code, obj):
        self._send(code, json.dumps(obj), "application/json; charset=utf-8")

    def do_GET(self):
        if self.path == "/health":
            self.send_response(200)
            self.send_header("Content-Type", "text/plain; charset=utf-8")
            self.send_header("Content-Length", "2")
            self.end_headers()
            self.wfile.write(b"ok")
            return
        if self.path == "/api/stats":
            self._json(200, stats_red())
            return
        if self.path.startswith("/api/trivia/pool"):
            # Va en GET a proposito: el control de cuota vive en do_POST, y esta
            # ruta no genera ni una peticion a Letterboxd (todo sale de la semilla).
            consulta = urllib.parse.urlparse(self.path).query
            crudo = urllib.parse.parse_qs(consulta).get("sets", [""])[0]
            sets = [x.strip() for x in crudo.split(",") if x.strip()]
            try:
                self._json(200, {"pool": trivia_pool(sets)})
            except ValueError as e:
                self._json(400, {"error": str(e)})
            return
        if self.path in ("/", "/index.html"):
            self._send(200, PAGE, "text/html; charset=utf-8")
        else:
            self._send(404, "not found", "text/plain; charset=utf-8")

    def _ip(self):
        """La IP real del visitante. Detras de un proxy viene en el header."""
        reenviada = self.headers.get("X-Forwarded-For", "")
        if reenviada:
            return reenviada.split(",")[0].strip()
        return self.client_address[0]

    def _gratis(self, payload):
        """
        True si esta peticion no puede generar trafico a Letterboxd, asi que
        no tiene sentido cobrarle cuota.

        Es el caso "Usar sin Letterboxd": sin perfiles no hay a quien
        preguntarle si vio algo, y las listas ya vienen en la semilla.
        """
        if self.path not in ("/api/discover", "/api/pick"):
            return False
        return not parse_username(payload.get("a")) and \
               not parse_username(payload.get("b"))

    def do_POST(self):
        try:
            n = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(n) or b"{}")
        except ValueError:
            self._json(400, {"error": "Peticion malformada."})
            return

        if not self._gratis(payload) and not rate_ok(self._ip()):
            self._json(429, {"error": "Demasiadas busquedas seguidas. "
                                      "Espera unos minutos y vuelve a intentar."})
            return

        try:
            if self.path == "/api/cross":
                self._json(200, find_shared(payload.get("a"), payload.get("b"),
                                            payload.get("seen_a"), payload.get("seen_b")))
            elif self.path == "/api/rank":
                self._json(200, rank(payload.get("slugs")))
            elif self.path == "/api/pick":
                self._json(200, pick_recommendation(
                    payload.get("mode"), payload.get("a"), payload.get("b"),
                    payload.get("skip")))
            elif self.path == "/api/discover":
                self._json(200, discover(
                    payload.get("a"), payload.get("b"), payload.get("genre"),
                    payload.get("skip"), payload.get("modo") or "discovery"))
            else:
                self._json(404, {"error": "Ruta desconocida."})
        except ValueError as e:
            self._json(400, {"error": str(e)})
        except Exception as e:
            self._json(500, {"error": f"Error inesperado: {e}"})


def main():
    if "--warm" in sys.argv:
        load_seed()          # parte de lo ya descargado, no repite trabajo
        warm()
        return

    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    port = int(args[0]) if args else PORT
    host = HOST

    load_seed()              # lo que viene con el repo
    load_cache()             # lo que se haya guardado en esta maquina

    server = ThreadingHTTPServer((host, port), Handler)
    local = host in ("127.0.0.1", "localhost")

    if local:
        url = f"http://localhost:{port}"
        print(f"Watchlist Double Bill corriendo en {url}  (Ctrl+C para parar)")
        try:
            webbrowser.open(url)      # solo en tu maquina
        except Exception:
            pass
    else:
        print(f"Watchlist Double Bill escuchando en {host}:{port}")

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        save_cache()
        print("\nListo.")


if __name__ == "__main__":
    main()
