#!/usr/bin/env python3
"""The oracle for md2html.bend: the same subset, written independently in
Python. run_md2html.sh diffs the two outputs. usage: md2html.py FILE"""
import sys

def spans(parts, mark, tag, out, inn):
    res = []
    for i, p in enumerate(parts):
        if i % 2 == 0:
            res.append(out(p))
        elif i == len(parts) - 1:          # never closed: the marker is text
            res.append(mark + out(p))
        else:
            res.append(f"<{tag}>{inn(p)}</{tag}>")
    return "".join(res)

def italic(t):
    return spans(t.split("*"), "*", "i", str, str)

def link(part):
    txt, sep, rest = part.partition("](")
    url, sep2, rest = rest.partition(")")
    if not sep2:
        return "[" + italic(part)
    return f'<a href="{url}">{italic(txt)}</a>{italic(rest)}'

def links(t):
    first, *more = t.split("[")
    return italic(first) + "".join(link(p) for p in more)

def bold(t):
    return spans(t.split("**"), "**", "b", links, links)

def inline(t):
    return spans(t.split("`"), "`", "code", bold, str)

SHUT = {None: [], "p": ["</p>"], "ul": ["</ul>"], "pre": ["</pre>"]}

def html(s):
    s = s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    out, o = [], None
    for l in s.splitlines():
        fence = l.startswith("```")
        if o == "pre":
            if fence:
                out.append("</pre>"); o = None
            else:
                out.append(l)
        elif fence:
            out += SHUT[o] + ["<pre>"]; o = "pre"
        elif not l.strip(" \t\n\r\x0b\x0c"):
            out += SHUT[o]; o = None
        elif l.startswith(("### ", "## ", "# ")):
            n = l.index(" ")
            out += SHUT[o] + [f"<h{n}>{inline(l[n + 1:])}</h{n}>"]; o = None
        elif l.startswith("- "):
            if o != "ul":
                out += SHUT[o] + ["<ul>"]
            out.append(f"<li>{inline(l[2:])}</li>"); o = "ul"
        else:
            if o != "p":
                out += SHUT[o] + ["<p>"]
            out.append(inline(l)); o = "p"
    return "\n".join(out + SHUT[o])

print(html(open(sys.argv[1], encoding="utf-8").read()))
