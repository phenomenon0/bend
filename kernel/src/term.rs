// Quantities, core terms, the de Bruijn algebra, and the reader of the
// export format (bend2/export.ts documents it). Nothing here judges: it
// builds the book the checker (check.rs) re-checks from scratch.

use std::cell::{OnceCell, RefCell};
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use crate::eval::V;

// §2 Quant: None | Lone | Many, spelled 0 1 2 (-x, x, +x)
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Q {
    N,
    L,
    M,
}

impl Q {
    // sequential: two live uses saturate to Many
    pub fn add(a: Q, b: Q) -> Q {
        match (a, b) {
            (Q::N, q) | (q, Q::N) => q,
            _ => Q::M,
        }
    }
    // branches: pointwise max
    pub fn join(a: Q, b: Q) -> Q {
        match (a, b) {
            (Q::N, q) => q,
            (Q::L, Q::N) => Q::L,
            (Q::L, q) => q,
            (Q::M, _) => Q::M,
        }
    }
    // a match field binds at field times scrutinee
    pub fn mul(f: Q, s: Q) -> Q {
        match f {
            Q::N => Q::N,
            Q::L => s,
            Q::M => Q::add(s, s),
        }
    }
    pub fn le(a: Q, b: Q) -> bool {
        matches!((a, b), (Q::N, _) | (Q::L, Q::L) | (Q::L, Q::M) | (Q::M, Q::M))
    }
    // the demand on an argument: an erased binder kills it
    pub fn dem(q: Q, qt: Q) -> Q {
        if q == Q::N {
            Q::N
        } else {
            qt
        }
    }
    pub fn show(self) -> &'static str {
        match self {
            Q::N => "0",
            Q::L => "1",
            Q::M => "2",
        }
    }
}

// §1 Term. Ref names a definition or a family (global id); Adt and Ctr are
// the n-ary nodes the parser builds (a constructor carries its fields only:
// its family's parameters are read off the goal, check-ctr); Lam's flag is
// the + binder mark.
#[derive(PartialEq, Eq, Hash, Debug)]
pub enum Tm {
    Var(u32),
    Ref(u32),
    Typ(T),
    Qnt,
    Qua(Q),
    Min(T, T),
    All(Q, T, T),
    Lam(bool, T),
    App(T, T),
    Adt(u32, Vec<u32>, Vec<T>),
    Ctr(u32, Vec<T>),
    Mat(u32, T, T),
    Efq,
    Eql(T, T, T),
    Rfl,
    Rwt(T, T, T),
    Let(Q, T, T),
    Ann(T, T),
    Hol(String),
}

pub type T = Rc<Tm>;

pub fn mk(t: Tm) -> T {
    Rc::new(t)
}

// rebuild t, handing every variable (index, binder depth) to f
pub fn mapv(t: &T, d: u32, f: &dyn Fn(u32, u32) -> T) -> T {
    let g = |x: &T| mapv(x, d, f);
    let gs = |xs: &Vec<T>| xs.iter().map(|x| mapv(x, d, f)).collect();
    match &**t {
        Tm::Var(i) => f(*i, d),
        Tm::Ref(_) | Tm::Qnt | Tm::Qua(_) | Tm::Efq | Tm::Rfl | Tm::Hol(_) => t.clone(),
        Tm::Typ(x) => mk(Tm::Typ(g(x))),
        Tm::Min(a, b) => mk(Tm::Min(g(a), g(b))),
        Tm::All(q, a, b) => mk(Tm::All(*q, g(a), mapv(b, d + 1, f))),
        Tm::Lam(m, b) => mk(Tm::Lam(*m, mapv(b, d + 1, f))),
        Tm::App(a, b) => mk(Tm::App(g(a), g(b))),
        Tm::Adt(a, r, ps) => mk(Tm::Adt(*a, r.clone(), gs(ps))),
        Tm::Ctr(c, xs) => mk(Tm::Ctr(*c, gs(xs))),
        Tm::Mat(c, h, m) => mk(Tm::Mat(*c, g(h), g(m))),
        Tm::Eql(a, b, x) => mk(Tm::Eql(g(a), g(b), g(x))),
        Tm::Rwt(e, p, x) => mk(Tm::Rwt(g(e), g(p), g(x))),
        Tm::Let(q, v, b) => mk(Tm::Let(*q, g(v), mapv(b, d + 1, f))),
        Tm::Ann(x, y) => mk(Tm::Ann(g(x), g(y))),
    }
}

pub fn shift(t: &T, n: u32) -> T {
    if n == 0 {
        return t.clone();
    }
    mapv(t, 0, &|i, d| mk(Tm::Var(if i < d { i } else { i + n })))
}

// t[0 := w], w closed over the same context as t's free variables
pub fn subst(t: &T, w: &T) -> T {
    mapv(t, 0, &|i, d| {
        if i == d {
            shift(w, d)
        } else if i > d {
            mk(Tm::Var(i - 1))
        } else {
            mk(Tm::Var(i))
        }
    })
}

pub fn closed(t: &T, n: u32) -> bool {
    let ok = RefCell::new(true);
    mapv(t, 0, &|i, d| {
        if i >= d + n {
            *ok.borrow_mut() = false;
        }
        mk(Tm::Var(i))
    });
    ok.into_inner()
}

// applyB: applying a lambda beta-reduces it (the lhs algebra, §4)
pub fn apply_b(f: &T, a: &T) -> T {
    match &**f {
        Tm::Lam(_, b) => subst(b, a),
        _ => mk(Tm::App(f.clone(), a.clone())),
    }
}

pub fn spine(t: &T) -> (T, Vec<T>) {
    let mut xs = vec![];
    let mut h = t.clone();
    while let Tm::App(f, x) = &*h.clone() {
        xs.push(x.clone());
        h = f.clone();
    }
    xs.reverse();
    (h, xs)
}

// The book: families, constructors and definitions under global ids
pub struct Fam {
    pub pn: usize,
    pub base: bool,
    pub sig: T,
    pub ctrs: Vec<u32>,
    pub sigv: OnceCell<V>,
}

pub struct Ctor {
    pub name: String,
    pub fam: u32,
    pub fields: usize,
    pub ty: T,
    pub tyv: OnceCell<V>,
}

pub struct Def {
    pub n: usize,
    pub x: usize,
    pub law: bool,
    pub base: bool,
    pub unsafe_: bool,
    pub foreign: bool,
    // a template's ~ parameter, opened as an opaque constant for its check
    pub konst: bool,
    pub ty: Option<T>,
    pub body: Option<T>,
    pub tyv: OnceCell<V>,
    pub bodyv: OnceCell<V>,
}

pub enum GK {
    Fam(Fam),
    Def(Def),
    // an item the reader could not build
    Bad(String),
}

pub struct Glob {
    pub name: String,
    pub g: GK,
}

#[derive(Clone, Debug)]
pub enum Verdict {
    Ok,
    Axiom(&'static str),
    Reject(String),
    Unsup(String),
}

pub struct Book {
    pub globs: Vec<Rc<Glob>>,
    pub ctors: Vec<Rc<Ctor>>,
    pub names: HashMap<String, u32>,
    pub order: Vec<u32>,
    pub insts: HashMap<(u32, Vec<T>), u32>,
    pub verdict: Vec<Option<Verdict>>,
    pub deps: Vec<BTreeSet<u32>>,
    pub done: Vec<bool>,
    // a def's place in the file order
    pub pos: HashMap<u32, usize>,
    // a helper whose live calls reach a def filled later: its call sites,
    // held until that def checks (check.rs, the mutual pair)
    pub pending: HashMap<u32, (u32, Vec<Fwd>)>,
}

// a forward call site: the caller's columns and the call's arguments,
// both let-expanded, over the caller's context at the site
#[derive(Clone)]
pub struct Fwd {
    pub cols: Vec<T>,
    pub args: Vec<T>,
}

thread_local! {
    pub static BK: RefCell<Book> = RefCell::new(Book {
        globs: vec![], ctors: vec![], names: HashMap::new(), order: vec![],
        insts: HashMap::new(), verdict: vec![], deps: vec![], done: vec![],
        pos: HashMap::new(), pending: HashMap::new(),
    });
}

pub fn glob(k: u32) -> Rc<Glob> {
    BK.with(|b| b.borrow().globs[k as usize].clone())
}

pub fn ctor(c: u32) -> Rc<Ctor> {
    BK.with(|b| b.borrow().ctors[c as usize].clone())
}

pub fn push_glob(g: Glob) -> u32 {
    BK.with(|b| {
        let mut b = b.borrow_mut();
        b.globs.push(Rc::new(g));
        b.verdict.push(None);
        b.deps.push(BTreeSet::new());
        b.done.push(false);
        (b.globs.len() - 1) as u32
    })
}

pub fn gname(k: u32) -> String {
    glob(k).name.clone()
}

// S-expressions
pub enum Sx {
    Atom(String),
    Str(String),
    List(Vec<Sx>),
}

pub fn read_sx(src: &str) -> Result<Vec<Sx>, String> {
    let b = src.as_bytes();
    let mut stack: Vec<Vec<Sx>> = vec![vec![]];
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if c == b'#' && stack.len() == 1 {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
        } else if c.is_ascii_whitespace() {
            i += 1;
        } else if c == b'(' {
            stack.push(vec![]);
            i += 1;
        } else if c == b')' {
            let l = stack.pop().ok_or("unbalanced )")?;
            stack.last_mut().ok_or("unbalanced )")?.push(Sx::List(l));
            i += 1;
        } else if c == b'"' {
            let mut s = Vec::new();
            i += 1;
            while i < b.len() && b[i] != b'"' {
                if b[i] == b'\\' {
                    i += 1;
                }
                s.push(b[i]);
                i += 1;
            }
            i += 1;
            stack.last_mut().unwrap().push(Sx::Str(String::from_utf8_lossy(&s).into_owned()));
        } else {
            let j = i;
            while i < b.len() && !b[i].is_ascii_whitespace() && b[i] != b'(' && b[i] != b')' {
                i += 1;
            }
            stack.last_mut().unwrap().push(Sx::Atom(src[j..i].to_string()));
        }
    }
    if stack.len() != 1 {
        return Err("unbalanced (".into());
    }
    Ok(stack.pop().unwrap())
}

fn atom(s: &Sx) -> Result<&str, String> {
    match s {
        Sx::Atom(a) | Sx::Str(a) => Ok(a),
        _ => Err("expected an atom".into()),
    }
}

fn num(s: &Sx) -> Result<usize, String> {
    atom(s)?.parse().map_err(|_| "expected a number".to_string())
}

fn quant(s: &Sx) -> Result<Q, String> {
    match atom(s)? {
        "0" => Ok(Q::N),
        "1" => Ok(Q::L),
        "2" => Ok(Q::M),
        q => Err(format!("bad quantity {}", q)),
    }
}

struct Names {
    globs: HashMap<String, u32>,
    ctrs: HashMap<String, u32>,
}

fn term(nm: &Names, s: &Sx) -> Result<T, String> {
    let gl = |k: &str| nm.globs.get(k).copied().ok_or(format!("unknown name {}", k));
    let ct = |k: &str| nm.ctrs.get(k).copied().ok_or(format!("unknown constructor {}", k));
    let tm = |x: &Sx| term(nm, x);
    match s {
        Sx::Atom(a) => Ok(mk(match a.as_str() {
            "quant" => Tm::Qnt,
            "efq" => Tm::Efq,
            "rfl" => Tm::Rfl,
            _ => return Err(format!("bad term atom {}", a)),
        })),
        Sx::Str(_) => Err("bad term".into()),
        Sx::List(l) => {
            let h = atom(l.first().ok_or("empty term")?)?;
            let a = |i: usize| l.get(i).ok_or(format!("short {} node", h));
            let t = match (h, l.len()) {
                ("var", 2) => Tm::Var(num(a(1)?)? as u32),
                ("ref", 2) => Tm::Ref(gl(atom(a(1)?)?)?),
                ("kind", 2) => Tm::Typ(tm(a(1)?)?),
                ("q", 2) => Tm::Qua(quant(a(1)?)?),
                ("min", 3) => Tm::Min(tm(a(1)?)?, tm(a(2)?)?),
                ("all", 4) => Tm::All(quant(a(1)?)?, tm(a(2)?)?, tm(a(3)?)?),
                ("lam", 3) => Tm::Lam(atom(a(1)?)? == "+", tm(a(2)?)?),
                ("app", 3) => Tm::App(tm(a(1)?)?, tm(a(2)?)?),
                ("adt", n) if n >= 3 => {
                    let r = match a(2)? {
                        Sx::List(r) => r.iter().map(|x| ct(atom(x)?)).collect::<Result<Vec<_>, _>>()?,
                        _ => return Err("bad adt".into()),
                    };
                    let ps = l[3..].iter().map(tm).collect::<Result<Vec<_>, _>>()?;
                    Tm::Adt(gl(atom(a(1)?)?)?, r, ps)
                }
                ("ctr", n) if n >= 2 => Tm::Ctr(ct(atom(a(1)?)?)?, l[2..].iter().map(tm).collect::<Result<Vec<_>, _>>()?),
                ("mat", 4) => Tm::Mat(ct(atom(a(1)?)?)?, tm(a(2)?)?, tm(a(3)?)?),
                ("eql", 4) => Tm::Eql(tm(a(1)?)?, tm(a(2)?)?, tm(a(3)?)?),
                ("rwt", 4) => Tm::Rwt(tm(a(1)?)?, tm(a(2)?)?, tm(a(3)?)?),
                ("let", 4) => Tm::Let(quant(a(1)?)?, tm(a(2)?)?, tm(a(3)?)?),
                ("ann", 3) => Tm::Ann(tm(a(1)?)?, tm(a(2)?)?),
                ("hole", 2) => Tm::Hol(atom(a(1)?)?.to_string()),
                _ => return Err(format!("bad term node {}", h)),
            };
            Ok(mk(t))
        }
    }
}

// load the export into BK: names first (a law's fill may come after its
// uses), then every item's terms
pub fn load(src: &str) -> Result<(), String> {
    let items = read_sx(src)?;
    let mut it = items.iter();
    match it.next() {
        Some(Sx::List(h)) if h.len() == 2 && atom(&h[0])? == "bend-core" && atom(&h[1])? == "1" => {}
        _ => return Err("not a (bend-core 1) export".into()),
    }
    let items: Vec<&Vec<Sx>> = it
        .map(|s| match s {
            Sx::List(l) if l.len() >= 2 => Ok(l),
            _ => Err("bad item".to_string()),
        })
        .collect::<Result<_, _>>()?;
    let mut nm = Names { globs: HashMap::new(), ctrs: HashMap::new() };
    let mut nctr = 0u32;
    for (k, l) in items.iter().enumerate() {
        nm.globs.insert(atom(&l[1])?.to_string(), k as u32);
        if atom(&l[0])? == "adt" {
            for c in &l[5..] {
                if let Sx::List(c) = c {
                    nm.ctrs.insert(atom(c.get(1).ok_or("bad ctr")?)?.to_string(), nctr);
                    nctr += 1;
                }
            }
        }
    }
    let mut ctors = vec![];
    for (k, l) in items.iter().enumerate() {
        let name = atom(&l[1])?.to_string();
        let g = match atom(&l[0])? {
            "adt" => (|| -> Result<GK, String> {
                let pn = num(l.get(2).ok_or("short adt")?)?;
                let base = matches!(l.get(3), Some(Sx::List(f)) if f.len() == 2);
                let sig = term(&nm, l.get(4).ok_or("short adt")?)?;
                let mut cs = vec![];
                for c in &l[5..] {
                    let c = match c {
                        Sx::List(c) if c.len() == 4 && atom(&c[0])? == "ctr" => c,
                        _ => return Err("bad ctr".into()),
                    };
                    cs.push(nm.ctrs[atom(&c[1])?]);
                    ctors.push(Rc::new(Ctor {
                        name: atom(&c[1])?.to_string(),
                        fam: k as u32,
                        fields: num(&c[2])?,
                        ty: term(&nm, &c[3])?,
                        tyv: OnceCell::new(),
                    }));
                }
                Ok(GK::Fam(Fam { pn, base, sig, ctrs: cs, sigv: OnceCell::new() }))
            })(),
            "def" => (|| -> Result<GK, String> {
                if l.len() != 7 {
                    return Err("short def".into());
                }
                let fl: Vec<&str> = match &l[4] {
                    Sx::List(f) => f[1..].iter().map(atom).collect::<Result<_, _>>()?,
                    _ => return Err("bad flags".into()),
                };
                let body = match &l[6] {
                    Sx::Atom(a) if a == "none" => None,
                    s => Some(term(&nm, s)?),
                };
                Ok(GK::Def(Def {
                    n: num(&l[2])?,
                    x: num(&l[3])?,
                    law: fl.contains(&"law"),
                    base: fl.contains(&"base"),
                    unsafe_: fl.contains(&"unsafe"),
                    foreign: fl.contains(&"foreign"),
                    konst: false,
                    ty: Some(term(&nm, &l[5])?),
                    body,
                    tyv: OnceCell::new(),
                    bodyv: OnceCell::new(),
                }))
            })(),
            h => Err(format!("bad item {}", h)),
        };
        let g = g.unwrap_or_else(GK::Bad);
        let id = push_glob(Glob { name, g });
        BK.with(|b| {
            let mut b = b.borrow_mut();
            let n = b.order.len();
            b.pos.insert(id, n);
            b.order.push(id);
        });
    }
    BK.with(|b| {
        let mut b = b.borrow_mut();
        b.ctors = ctors;
        b.names = nm.globs;
    });
    Ok(())
}

// a short printout of a term, for rejections
pub fn show(t: &T, fuel: &mut usize) -> String {
    if *fuel == 0 {
        return "..".into();
    }
    *fuel -= 1;
    let mut s = |x: &T| show(x, fuel);
    match &**t {
        Tm::Var(i) => format!("#{}", i),
        Tm::Ref(k) => gname(*k),
        Tm::Typ(g) => format!("Kind({})", s(g)),
        Tm::Qnt => "Quant".into(),
        Tm::Qua(q) => format!("&{}", q.show()),
        Tm::Min(a, b) => format!("({} <&> {})", s(a), s(b)),
        Tm::All(q, a, b) => format!("(@{}:{} -> {})", q.show(), s(a), s(b)),
        Tm::Lam(_, b) => format!("(λ {})", s(b)),
        Tm::App(f, x) => format!("{}({})", s(f), s(x)),
        Tm::Adt(a, r, ps) => {
            let ps: Vec<String> = ps.iter().map(|p| s(p)).collect();
            let r: Vec<String> = r.iter().map(|c| format!("-{}", ctor(*c).name)).collect();
            format!("{}{}<{}>", gname(*a), r.join(""), ps.join(", "))
        }
        Tm::Ctr(c, xs) => {
            let xs: Vec<String> = xs.iter().map(|p| s(p)).collect();
            format!("{}{{{}}}", ctor(*c).name, xs.join(", "))
        }
        Tm::Mat(c, h, m) => format!("\\{{{}: {}; {}}}", ctor(*c).name, s(h), s(m)),
        Tm::Efq => "\\{}".into(),
        Tm::Eql(a, b, x) => format!("{{{} == {} : {}}}", s(a), s(b), s(x)),
        Tm::Rfl => "{==}".into(),
        Tm::Rwt(e, p, f) => format!("(%{} : {}; {})", s(e), s(p), s(f)),
        Tm::Let(q, v, b) => format!("({}x = {}; {})", q.show(), s(v), s(b)),
        Tm::Ann(x, y) => format!("{{{} : {}}}", s(x), s(y)),
        Tm::Hol(k) => format!("?{}", k),
    }
}
