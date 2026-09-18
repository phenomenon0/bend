"""Small independently checked grammar specimens; no corpus execution."""
EXPRESSIONS = [
    "'a\\\r\nb'", "00e5", "0_0.2",
    "*a", "a[*b]", "a[*b,]", "f(*a if b else c)", "f(**a if b else c)",
    "((a,b))", "(())", "f(x=1,x=2)",
    "a + b * c ** d ** e", "-2**2", "2**-2", "~-+x", "not not x",
    "a or b or c", "a and b and c", "a or b and not c", "(a and b) and c",
    "a and (b and c)", "a < b <= c != d is e is not f in g not in h",
    "(a < b) < c", "a < (b < c)", "not a in b", "a not in b",
    "a if b else c if d else e", "(a if b else c) if d else e",
    "a | b ^ c & d << e + f * g", "a @ b // c % d / e - f",
    "()", "(a)", "((a))", "(a,)", "a,", "a,b,c", "(a,b,c)",
    "[]", "[a,b,]", "[*a,b]", "{}", "{a}", "{a,b,}", "{*a,b}",
    "{a:b,c:d,}", "{**a, b:c, **d}", "f()", "f(a,b,)", "f(*a,b,*c)",
    "f(a,k=b,**c)", "f(k=a,*b)", "f(**a,**b)", "f(a)(b).x[c]",
    "(a).b", "(f)(a)", "(a)[b]", "a[b,c]", "a[b,]", "a[(b,c)]",
    "(a)+b", "a+(b)", "-(a)", "(a) if (b) else (c)",
    "0x1_f", "1_000", "1.25e-9", "1e999", "3j", "True", "False", "None", "...",
    "'a' 'b'", "('a' # comment\n 'b')", "u'hello'", "U'hello'", "r'\\n'", "b'abc' b'def'",
    "'''two\nlines'''", "'é😀'", "( 'é' ).upper()", "x[(a)]", "([a, b])",
]
STATEMENTS = [
    "match=1", "case=2", "return *a", "a = *b", "x += *a",
    "x=1", "x=y=z", "a,b = c", "[a,*b] = c", "(a) = b", "a.b = c",
    "a[b] = c", "a[b,c] = d", "a.b[c].d = e", "a += b", "a[b] **= c",
    "a @= b", "a <<= b", "a |= b", "a += b,c", "a = (b)", "(a)",
    "pass; break; continue", "return", "return a,b", "return (a)", "x=1; y=2;",
    "if a: pass", "if a: x=1; y=2\nelse: pass",
    "if a:\n    pass\nelif b:\n    return c\nelse:\n    continue\n",
    "if a:\n    if b:\n        pass\n    else:\n        break\nelse:\n    pass\n",
    "while a:\n    x += 1\nelse:\n    return x\n",
    "if (a):\n\tpass\n\n# blank\nelse:\n\treturn (b)\n",
    "if a:\r\n    pass\r\nelse:\r\n    break\r\n",
    "if a:\n \f  pass\n", "x = ('a' # one\n 'b')\n",
    "x = 1 + \\\n 2\n", "x=1\n# trailing comment", "# just a comment", "\n\n",
]

INVALID = [
    "'\0'", "#\0",
    "b'a' 'b'",
    "(*a)", "f(**a,*b)", "{*a:b}", "[*a if b else c]",
    "x =", "1 = x", "f() = x", "(a+b) = c", "[a,1] = c", "a,b += c",
    "if x\n pass", "if x:\npass", "if x: if y: pass", "else: pass",
    "x y", "f(a b)", "[a b]", "{a b}", "f(x=1,2)", "a + not b",
    "a is not", "a not b", "(]", "'''unfinished", "if x:\n    pass\n  pass",
]

UNSUPPORTED = [
    "K", "a.K", "f(K=1)", "match x:\n    case _: pass\n",
    "import x", "from x import y", "def f(): pass", "class A: pass",
    "for x in y: pass", "lambda: 1", "[x for x in y]", "{x for x in y}",
    "{x:x for x in y}", "f(x for x in y)", "a[1:2]", "a[:2]", "f'{x}'",
    "(x := 1)", "assert x", "del x", "raise x", "global x", "with x: pass",
]
