# -*- coding: utf-8 -*-
"""
Editor de Spyder

Este es un archivo temporal.
"""
import re, urllib.request, urllib.error

UA = {"User-Agent": "watchlist-double-bill/0.3"}

def pedir(url):
    try:
        with urllib.request.urlopen(urllib.request.Request(url, headers=UA), 15) as r:
            return r.status, r.read().decode("utf-8","replace")
    except urllib.error.HTTPError as e:
        return e.code, ""
    except Exception as e:
        return type(e).__name__, ""

def revisar(user):
    print(f"\n=== {user} ===")
    cod, html = pedir(f"https://letterboxd.com/{user}/films/")
    slugs = list(dict.fromkeys(re.findall(r'data-item-slug="([^"]+)"', html)))
    print(f"  /films/ -> {cod} | {len(slugs)} vistas leidas")
    if not slugs:
        return
    print(f"  harakiri en esa pagina: {'harakiri' in slugs}")
    print(f"  perfect-blue en esa pagina: {'perfect-blue' in slugs}")
    for s in slugs[:3]:                      # slugs que SI vio, sacados de su perfil
        c, _ = pedir(f"https://letterboxd.com/{user}/film/{s}/")
        print(f"    /{user}/film/{s}/ -> {c}")

for u in ["giordano34", "ali", "alvarovadilloz"]:
    revisar(u)
