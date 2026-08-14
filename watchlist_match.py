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
RATE_MAX = 25           # peticiones por ventana y por IP

# Listas publicas de donde salen las recomendaciones.
LISTS = {
    "top500": {
        "url": "https://letterboxd.com/dave/list/letterboxd-top-500-films-history-collected/",
        "pages": 7,
    },
    # Sin uso desde que la parada del medio pasa a salir del top500.
    # Se deja lista por si se quiere volver a enchufar.
    "graduated": {
        "url": "https://letterboxd.com/maxedproduction/list/films-that-have-graduated-from-the-top-100/",
        "pages": 2,
    },
    "underseen": {
        "url": "https://letterboxd.com/official/list/top-100-underseen-films/",
        "pages": 2,
    },
}
LIST_URL = LISTS["top500"]["url"]   # la que usan San Valentin y Halloween
SCAN_CHUNK = 25         # cuantas fichas abrimos por tanda antes de volver a evaluar
MAX_SCAN = 250          # techo de fichas a revisar antes de rendirse

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
    todos = []
    paginas = {}

    for key, conf in LISTS.items():
        print(f"Leyendo lista '{key}'...")
        for page in range(1, conf["pages"] + 1):
            slugs = list_page(conf["url"], page)
            if not slugs:
                break
            paginas[f"{conf['url']}|{page}"] = slugs
            todos.extend(slugs)

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
          f"en {SEED_PATH} ({kb:.0f} KB).")
    print("Ahora sube ese archivo al repo y vuelve a desplegar.")


# ─────────────────────────────────────────────────────────────
# HTTP
# ─────────────────────────────────────────────────────────────

def get(url, timeout=20):
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


def build_pool(username, include_seen):
    """
    Devuelve (pool, stats).
      pool  : dict slug -> 'seen' | 'watchlist'
      stats : conteos para mostrar en la UI
    Si el mismo slug aparece en ambos lados, gana 'seen'.

    El watchlist se lee completo. Las vistas, solo la primera pagina
    (las siguientes estan bloqueadas del lado de Letterboxd).
    """
    watchlist = fetch_section(username, "watchlist")
    pool = {s: "watchlist" for s in watchlist}
    seen = []
    if include_seen:
        seen = fetch_section(username, "films", paginate=False)
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
# Recomendacion: la mejor del top 500 que ninguno haya visto
# ─────────────────────────────────────────────────────────────

def list_page(url, page):
    """Slugs de una pagina de una lista publica, en el orden en que estan."""
    key = (url, page)
    with _list_lock:
        hit = _list_pages.get(key)
    if hit is not None:
        return hit

    full = url if page == 1 else f"{url}page/{page}/"
    try:
        slugs = extract_slugs(get(full))
    except Exception:
        slugs = []

    with _list_lock:
        _list_pages[key] = slugs
    return slugs


def has_watched(username, slug):
    """
    True si el usuario registro esa pelicula como vista.

    Usa /{usuario}/film/{slug}/, que responde 200 solo si la vio.
    Verificado: una pelicula en su watchlist pero no vista da 404, asi que
    esta ruta si distingue "vista" de "quiere verla".
    """
    key = f"{username}/{slug}"
    with _watch_lock:
        if key in _watch_cache:
            return _watch_cache[key]

    url = f"{BASE}/{username}/film/{slug}/"
    req = urllib.request.Request(url, method="HEAD", headers={
        "User-Agent": UA, "Accept": "text/html",
    })
    try:
        with urllib.request.urlopen(req, timeout=15) as r:
            visto = r.status == 200
    except urllib.error.HTTPError as e:
        if e.code == 404:
            visto = False
        elif e.code == 405:                     # el servidor no acepta HEAD
            try:
                get(url)
                visto = True
            except urllib.error.HTTPError as e2:
                visto = e2.code != 404
            except Exception:
                return False                    # fallo puntual: no lo guardamos
        else:
            return False
    except Exception:
        return False

    with _watch_lock:
        _watch_cache[key] = visto
    return visto


def take_unwatched(list_key, a, b, want=None, n=1):
    """
    Baja por una lista publica en su orden y devuelve hasta n peliculas
    que NINGUNO de los dos haya visto. Sin repetir.

    want=None  -> cualquier genero. No hace falta abrir fichas durante el
                  barrido: basta preguntar si la vieron. Solo se abren las
                  fichas de las ganadoras.
    want={...} -> hay que abrir cada ficha para conocer su genero.

    Pedir n=2 en una sola pasada evita recorrer la lista dos veces.
    """
    conf = LISTS.get(list_key)
    if not conf:
        raise ValueError("Lista desconocida.")

    encontradas = []
    posicion = 0
    revisadas = 0

    for page in range(1, conf["pages"] + 1):
        slugs = list_page(conf["url"], page)
        if not slugs:
            break

        for i in range(0, len(slugs), SCAN_CHUNK):
            tanda = slugs[i:i + SCAN_CHUNK]

            if want:
                with ThreadPoolExecutor(max_workers=FETCH_WORKERS) as pool:
                    fichas = list(pool.map(fetch_film, tanda))
            else:
                fichas = [{"slug": s} for s in tanda]

            for f in fichas:
                posicion += 1
                revisadas += 1
                if want and not (set(f.get("genres") or []) & want):
                    continue
                if has_watched(a, f["slug"]) or has_watched(b, f["slug"]):
                    continue
                completa = f if want else fetch_film(f["slug"])
                encontradas.append({**completa, "rank": posicion, "scanned": revisadas})
                if len(encontradas) >= n:
                    save_cache()
                    return encontradas

            if revisadas >= MAX_SCAN:
                save_cache()
                return encontradas

    save_cache()
    return encontradas


def first_unwatched(list_key, a, b, want=None):
    """La primera que ninguno vio, o None."""
    r = take_unwatched(list_key, a, b, want, 1)
    return r[0] if r else None


def _dos_usuarios(raw_a, raw_b):
    a = parse_username(raw_a)
    b = parse_username(raw_b)
    if not a or not b:
        raise ValueError("Perfiles invalidos.")
    return a, b


def pick_recommendation(mode, raw_a, raw_b):
    """La mejor del top 500 del genero del modo que ninguno haya visto."""
    want = MODE_GENRES.get(mode)
    if not want:
        raise ValueError("Modo desconocido.")
    a, b = _dos_usuarios(raw_a, raw_b)
    return first_unwatched("top500", a, b, want)


# Etiquetas de las tres paradas. La del medio va sin texto a proposito.
DISCOVERY_LABELS = ["\u00bfa\u00fan?", "", "joder \U0001F6AC"]

# Generos que se pueden pedir desde el medidor. Lista cerrada a proposito.
DISCOVERY_GENRES = ["horror", "romance", "comedy", "thriller", "drama", "action"]


def discover(raw_a, raw_b, genre=None):
    """
    Tres peliculas que ninguno vio: las dos mejores del top 500 y la primera
    de la lista de underseen.

    genre=None -> cualquier genero, y no hace falta abrir fichas durante el
                  barrido. Rapido.
    genre=x    -> hay que abrir la ficha de cada candidata. Mas lento.
    """
    a, b = _dos_usuarios(raw_a, raw_b)

    want = None
    if genre:
        if genre not in DISCOVERY_GENRES:
            raise ValueError("Genero no disponible.")
        want = {genre}

    def buscar(list_key, n):
        try:
            return take_unwatched(list_key, a, b, want, n)
        except Exception:
            return []

    # Las dos primeras salen del mismo barrido, asi la segunda nunca repite
    # a la primera. La tercera es otra lista, va en paralelo.
    with ThreadPoolExecutor(max_workers=2) as pool:
        f_top = pool.submit(buscar, "top500", 2)
        f_und = pool.submit(buscar, "underseen", 1)
        top, under = f_top.result(), f_und.result()

    films = [
        top[0] if len(top) > 0 else None,
        top[1] if len(top) > 1 else None,
        under[0] if under else None,
    ]
    return [{"label": DISCOVERY_LABELS[i], "film": films[i]} for i in range(3)]


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
<link href="https://fonts.googleapis.com/css2?family=Instrument+Serif:ital@0;1&family=Inter:wght@400;500;600&family=IBM+Plex+Mono:wght@400;500&display=swap" rel="stylesheet">
<style>
  :root{
    --night:#141a2e; --panel:#1c2440; --edge:#2c3557;
    --bone:#ece6d9; --dim:#8b93b4;
    --signal:#ff4d3d; --beam:#7fd6cd;
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
  .lede{color:var(--dim);max-width:46ch;margin:0 0 40px}

  .bill{display:grid;grid-template-columns:1fr auto 1fr;gap:14px;align-items:start}
  .amp{font-family:var(--serif);font-style:italic;font-size:44px;color:var(--signal);
       line-height:1;padding-top:4px;user-select:none}
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
  #go{margin-top:22px}
  button.ghost{background:transparent;color:var(--beam);border:1px solid var(--edge);
               font-weight:500;margin-top:24px}
  button.ghost:hover:not(:disabled){background:var(--panel);filter:none}

  .note{margin-top:14px;font-size:12.5px;color:var(--dim)}
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

  .warn{color:var(--sc,var(--beam))}

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
    .bill{grid-template-columns:1fr;gap:8px}
    .amp{text-align:center;font-size:34px;padding:0}
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
  <h1>Watchlist<br>double bill</h1>
  <p class="lede">Las peliculas que ambos quieren ver, ordenadas por el promedio
     de Letterboxd.</p>

  <div class="bill">
    <div>
      <input type="text" id="a" placeholder="letterboxd.com/usuario" autocomplete="off" spellcheck="false">
      <label class="opt"><input type="checkbox" id="seenA"> Agregar sus ultimas 72 vistas</label>
    </div>
    <span class="amp" aria-hidden="true">&amp;</span>
    <div>
      <input type="text" id="b" placeholder="letterboxd.com/otro-usuario" autocomplete="off" spellcheck="false">
      <label class="opt"><input type="checkbox" id="seenB"> Agregar sus ultimas 72 vistas</label>
    </div>
  </div>
  <button id="go">Match watchlists</button>
  <p class="note">Solo funciona con perfiles publicos. De las peliculas ya vistas, Letterboxd
     deja leer solo la pagina mas reciente: hasta 72, no el historial completo.</p>

  <p class="status" id="status" role="status" aria-live="polite"></p>
  <div id="gate"></div>
  <div id="out"></div>
  <div id="deck"></div>
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
// Descubrimiento no filtra la lista: solo agrega el medidor.
const MODES = {
  valentine: { label:"Modo San Valentin",   genres:["romance"], boton:"\u2665 San Valentin" },
  halloween: { label:"Modo Halloween",      genres:["horror"],  boton:"\u25c8 Halloween" },
  discovery: { label:"Modo Descubrimiento", genres:null,        boton:"\u25d0 Descubrimiento" }
};

const DISC_GENRES = ["horror","romance","comedy","thriller","drama","action"];

let state = { films: [], shown: 0, prov: {}, users: null, mode: null,
              hasGenres: false, picks: {}, stages: {}, genre: null };

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
            hasGenres: false, picks: {}, stages: {}, genre: null };
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
  if(state.mode === "discovery") cargarStages();
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
  const disc = state.mode === "discovery";
  host.innerHTML = `
    <div class="modes">${btn("valentine")}${btn("halloween")}${btn("discovery")}</div>
    <div class="deck ${state.mode || ""}">
      ${disc ? `<div class="disc">
                  <div class="meter" id="meter"></div>
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
    caja.innerHTML = `<p>Genero</p>` + DISC_GENRES.map(g =>
      `<button class="gbtn" data-g="${g}" aria-pressed="${state.genre === g}">${g}</button>`
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
    cards.insertAdjacentHTML("beforeend",
      `<p class="empty">No hay ranking que mostrar, pero el modo Descubrimiento
       funciona igual: no depende de lo que tengan en comun.</p>`);
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

function claveGenero(){ return state.genre || "todos"; }

async function cargarStages(){
  const clave = claveGenero();
  if(state.stages[clave] !== undefined) return;   // ya la buscamos
  state.stages[clave] = null;                     // marca "en curso"
  try{
    const d = await post("/api/discover", {
      a: state.users.a.user, b: state.users.b.user, genre: state.genre
    });
    state.stages[clave] = d.stages;
  }catch(e){
    state.stages[clave] = { error: e.message };
  }
  if(state.mode === "discovery" && claveGenero() === clave) pintarStages();
}

function pintarStages(){
  const box = $("meter");
  if(!box) return;
  const s = state.stages[claveGenero()];

  if(s === undefined || s === null){
    const que = state.genre ? `peliculas de ${state.genre}` : "el medidor";
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
           ? "Nada de " + esc(state.genre) + " por aca." : "Ya vieron todo aca."}</p>`
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

  box.innerHTML = `<div class="track"><i></i><i></i><i></i></div>
    <div class="stops">${s.map(col).join("")}</div>`;
}

// ── recomendacion del top 500 que ninguno vio ──
async function cargarPick(mode){
  if(state.picks[mode] !== undefined) return;      // ya la tenemos
  try{
    const d = await post("/api/pick", {
      mode, a: state.users.a.user, b: state.users.b.user
    });
    state.picks[mode] = d.pick;                    // puede ser null
  }catch(e){
    state.picks[mode] = { error: e.message };
  }
  if(state.mode === mode) pintarPick(mode);        // por si cambio mientras buscaba
}

function pintarPick(mode){
  const box = $("pick");
  if(!box) return;
  const titulo = "Para esta noche";
  const p = state.picks[mode];

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
  box.innerHTML = `<h4>${titulo}</h4>
    ${p.poster ? `<img src="${esc(p.poster)}" alt="" loading="lazy">` : ""}
    <p class="pt"><a href="${esc(p.url)}" target="_blank" rel="noopener">${esc(p.title)}</a></p>
    <p class="pm">${p.year || ""}${gen ? " \u00b7 " + gen : ""}</p>
    <p class="pr">${p.rating ? p.rating.toFixed(2) : "\u2014"}</p>
    <p class="pw">Puesto ${p.rank} del top 500 de Letterboxd, y ninguno de los dos
       la registro como vista.</p>`;
}

function renderTally(d){
  const line = p => `${esc(p.user)}: <b>${p.watchlist}</b> por ver` +
    (p.include_seen ? ` + <b>${p.seen}</b> ultimas vistas = <b>${p.pool}</b>` : "");
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

    def do_POST(self):
        try:
            n = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(n) or b"{}")
        except ValueError:
            self._json(400, {"error": "Peticion malformada."})
            return

        if not rate_ok(self._ip()):
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
                self._json(200, {"pick": pick_recommendation(
                    payload.get("mode"), payload.get("a"), payload.get("b"))})
            elif self.path == "/api/discover":
                self._json(200, {"stages": discover(
                    payload.get("a"), payload.get("b"), payload.get("genre"))})
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
