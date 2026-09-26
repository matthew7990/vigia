#!/usr/bin/env python3
"""Generate the benchmark corpus: deterministic HTML fixtures."""
import os, random

OUT = os.path.join(os.path.dirname(__file__), "corpus")
os.makedirs(OUT, exist_ok=True)
random.seed(42)


def page(title, body):
    return f"<!doctype html><html><head><title>{title}</title></head><body>{body}</body></html>"


def w(name, s):
    open(os.path.join(OUT, name), "w").write(s)
    print(f"{name}: {len(s)} B")


# small: minimal realistic page
w("small.html", page("small", """
<header><nav><a href="/">Home</a><a href="/docs">Docs</a></nav></header>
<main><h1>Hello</h1><p class="intro">A small page with <b>nested</b> inline tags.</p></main>
"""))

# table: 2000 rows - classic scraping target
rows = "".join(f'<tr><td>row{i}</td><td class="v">{i*7%997}</td><td><a href="/i/{i}">view</a></td></tr>' for i in range(2000))
w("table.html", page("table", f"<table><thead><tr><th>n</th><th>v</th><th>x</th></tr></thead><tbody>{rows}</tbody></table>"))

# nested: 300 levels deep
w("nested.html", page("nested", "<div>" * 300 + "deep text" + "</div>" * 300))

# links: 500 nav links
links = "".join(f'<a href="/p/{i}" class="nav">page {i}</a>' for i in range(500))
w("links.html", page("links", f"<nav>{links}</nav>"))

# forms: login + search + checkout-like
w("forms.html", page("forms", """
<form action="/login" method="post"><input name="user" placeholder="usuario"><input type="password" name="pass"><input type="submit" value="ok"></form>
<form action="/search" method="get"><input name="q"><select name="cat"><option>a</option><option>b</option></select></form>
<form action="/pay" method="post"><input name="card"><input name="cvv"><textarea name="notes"></textarea></form>
"""))

# malformed: unclosed + misnested + implied end tags
w("malformed.html", "<html><body><ul><li>one<li>two<li>three</ul><p>unclosed<b>bold<i>both</b>italic</i><div><span>stray</div></body>")

# article: realistic prose, biggest file
words = "datos agente navegador red pagina costo velocidad memoria token enlace tabla campo".split()
paras = "".join(f"<p>{' '.join(random.choice(words) for _ in range(80))}</p>" for _ in range(400))
w("article.html", page("article", f"<article>{paras}</article>"))
