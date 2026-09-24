// §8 Equal: reduction and conversion, by evaluation to weak-head values.
// Terms evaluate in an environment of shared thunks (call by need); a
// binder is a Rust closure; a stuck term is a neutral: a head (a rigid
// variable at a de Bruijn level, an opaque or unapplied reference, a match
// stuck on a neutral scrutinee, an applied \{}, a rewrite whose evidence is
// not {==}) and a spine. Delta is lazy: evaluation never unfolds a
// definition; whnf unfolds a saturated one (the weak dref); conversion
// compares two references by name and arguments first and unfolds only
// when that fails, at any arity (the strong drefS). Conversion is compare
// EQ (joinability, with eta on both sides) and compare LE (kinds by the
// quantity order, a residual with more constructors peeled fits fewer, a
// function type's domains swapped), as bend.lean §8 states them.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::term::*;

pub type V = Rc<Val>;
pub type Clo = Rc<dyn Fn(V) -> V>;

pub enum Val {
    Lam(bool, Clo),
    All(Q, V, Clo),
    Typ(V),
    Qnt,
    Qua(Q),
    Min(V, V),
    Adt(u32, Rc<Vec<u32>>, Vec<V>),
    Ctr(u32, Vec<V>),
    Mat(u32, V, V),
    Efq,
    Eql(V, V, V),
    Rfl,
    Neu(Head, Vec<V>),
    // a saturated reference whose unfolding is stuck, kept by its name
    // (the neutral) with that unfolding beside it
    Stuck(V, V),
    // a shared cell: the term and its environment, then its value, then
    // its weak head normal form (each fill replaces the last)
    Thk(RefCell<Option<V>>, Env, T),
}

#[derive(Clone)]
pub enum Head {
    Var(u32),
    Ref(u32),
    Mat(u32, V, V, V),
    Efq,
    Rwt(V, V, V),
    Hol(String),
}

#[derive(Clone, Default)]
pub struct Env(pub Option<Rc<(V, Env)>>);

impl Env {
    pub fn push(&self, v: V) -> Env {
        Env(Some(Rc::new((v, self.clone()))))
    }
    pub fn get(&self, i: u32) -> V {
        let mut e = self;
        for _ in 0..i {
            e = &e.0.as_ref().expect("unbound index").1;
        }
        e.0.as_ref().expect("unbound index").0.clone()
    }
}

// Failures unwind to the definition under check (check.rs catches them)
pub enum Fail {
    Reject(String),
    Unsup(String),
}

pub fn reject(m: String) -> ! {
    std::panic::panic_any(Fail::Reject(m))
}

pub fn unsup(m: String) -> ! {
    std::panic::panic_any(Fail::Unsup(m))
}

thread_local! {
    pub static FUEL: Cell<u64> = const { Cell::new(0) };
}

fn tick() {
    FUEL.with(|f| {
        let n = f.get();
        if n == 0 {
            unsup("fuel exhausted (reduction budget)".into());
        }
        f.set(n - 1);
    })
}

pub fn v(x: Val) -> V {
    Rc::new(x)
}

pub fn var(l: u32) -> V {
    v(Val::Neu(Head::Var(l), vec![]))
}

pub fn typ(q: Q) -> V {
    v(Val::Typ(v(Val::Qua(q))))
}

pub fn force(x: &V) -> V {
    let mut x = x.clone();
    loop {
        let next = match &*x {
            Val::Thk(c, env, t) => {
                let got = c.borrow().clone();
                match got {
                    Some(y) => y,
                    None => {
                        let y = force(&eval(env, t));
                        *c.borrow_mut() = Some(y.clone());
                        y
                    }
                }
            }
            _ => return x,
        };
        x = next;
    }
}

fn lazy(env: &Env, t: &T) -> V {
    match &**t {
        Tm::Var(i) => env.get(*i),
        Tm::Qnt | Tm::Qua(_) | Tm::Rfl | Tm::Efq | Tm::Ref(_) | Tm::Lam(..) | Tm::All(..) => eval(env, t),
        _ => v(Val::Thk(RefCell::new(None), env.clone(), t.clone())),
    }
}

pub fn ref_val(k: u32) -> V {
    match &glob(k).g {
        GK::Fam(f) if f.pn == 0 => v(Val::Adt(k, Rc::new(vec![]), vec![])),
        _ => v(Val::Neu(Head::Ref(k), vec![])),
    }
}

pub fn eval(env: &Env, t: &T) -> V {
    match &**t {
        Tm::Var(i) => env.get(*i),
        Tm::Ref(k) => ref_val(*k),
        Tm::Typ(g) => v(Val::Typ(lazy(env, g))),
        Tm::Qnt => v(Val::Qnt),
        Tm::Qua(q) => v(Val::Qua(*q)),
        Tm::Min(a, b) => v(Val::Min(lazy(env, a), lazy(env, b))),
        Tm::All(q, a, b) => {
            let (e, b) = (env.clone(), b.clone());
            v(Val::All(*q, lazy(env, a), Rc::new(move |x| eval(&e.push(x), &b))))
        }
        Tm::Lam(m, b) => {
            let (e, b) = (env.clone(), b.clone());
            v(Val::Lam(*m, Rc::new(move |x| eval(&e.push(x), &b))))
        }
        Tm::App(f, x) => apply(&eval(env, f), lazy(env, x)),
        Tm::Adt(a, r, ps) => v(Val::Adt(*a, Rc::new(r.clone()), ps.iter().map(|p| lazy(env, p)).collect())),
        Tm::Ctr(c, xs) => v(Val::Ctr(*c, xs.iter().map(|p| lazy(env, p)).collect())),
        Tm::Mat(c, h, m) => v(Val::Mat(*c, lazy(env, h), lazy(env, m))),
        Tm::Efq => v(Val::Efq),
        Tm::Eql(a, b, x) => v(Val::Eql(lazy(env, a), lazy(env, b), lazy(env, x))),
        Tm::Rfl => v(Val::Rfl),
        Tm::Rwt(e, p, f) => {
            let ev = whnf(&eval(env, e));
            if matches!(&*ev, Val::Rfl) {
                eval(env, f)
            } else {
                v(Val::Neu(Head::Rwt(ev, lazy(env, p), lazy(env, f)), vec![]))
            }
        }
        Tm::Let(_, x, b) => eval(&env.push(lazy(env, x)), b),
        Tm::Ann(x, _) => eval(env, x),
        Tm::Hol(k) => v(Val::Neu(Head::Hol(k.clone()), vec![])),
    }
}

pub fn apply(f: &V, x: V) -> V {
    let f = force(f);
    match &*f {
        Val::Lam(_, c) => {
            tick();
            c(x)
        }
        Val::Mat(c, h, m) => {
            let s = whnf(&x);
            match &*s {
                Val::Ctr(c2, fs) if c2 == c => {
                    tick();
                    fs.iter().fold(h.clone(), |acc, a| apply(&acc, a.clone()))
                }
                Val::Ctr(..) => apply(m, s),
                _ => v(Val::Neu(Head::Mat(*c, h.clone(), m.clone(), s), vec![])),
            }
        }
        Val::Neu(h, sp) => {
            let mut sp = sp.clone();
            sp.push(x);
            v(Val::Neu(h.clone(), sp))
        }
        Val::Efq => v(Val::Neu(Head::Efq, vec![x])),
        Val::Stuck(o, _) => apply(o, x),
        _ => reject("an application of a non-function".into()),
    }
}

pub fn def_tyv(k: u32) -> V {
    let g = glob(k);
    match &g.g {
        GK::Def(d) => d.tyv.get_or_init(|| eval(&Env::default(), d.ty.as_ref().expect("a typed def"))).clone(),
        GK::Fam(f) => f.sigv.get_or_init(|| eval(&Env::default(), &f.sig)).clone(),
        GK::Bad(m) => unsup(format!("a reference to {}, which the reader refused: {}", g.name, m)),
    }
}

pub fn ctor_tyv(c: u32) -> V {
    let k = ctor(c);
    k.tyv.get_or_init(|| eval(&Env::default(), &k.ty)).clone()
}

// the body of a definition that unfolds, with its arity
fn delta(k: u32) -> Option<(usize, V)> {
    let g = glob(k);
    match &g.g {
        GK::Def(d) if !d.konst => {
            let b = d.body.as_ref()?;
            Some((d.n, d.bodyv.get_or_init(|| eval(&Env::default(), b)).clone()))
        }
        _ => None,
    }
}

fn unfold(x: &V, any: bool) -> Option<V> {
    if let Val::Neu(Head::Ref(k), sp) = &*x.clone() {
        let (n, b) = delta(*k)?;
        if any || sp.len() >= n {
            tick();
            return Some(sp.iter().fold(b, |acc, a| apply(&acc, a.clone())));
        }
    }
    None
}

// the weak head normal form (the machine's reach: no binder entered); a
// cell keeps it, so shared work runs once
pub fn whnf(x: &V) -> V {
    let y = force(x);
    let w = match &*y {
        Val::Neu(Head::Ref(_), _) => match unfold(&y, false) {
            Some(u) => {
                let w = whnf(&u);
                if matches!(&*w, Val::Neu(..) | Val::Stuck(..)) {
                    v(Val::Stuck(y.clone(), w))
                } else {
                    w
                }
            }
            None => y.clone(),
        },
        Val::Min(a, b) => min(a, b),
        _ => y.clone(),
    };
    if let Val::Thk(c, ..) = &**x {
        *c.borrow_mut() = Some(w.clone());
    }
    w
}

// the meet, reduced only when forced: &2 is the identity, &0 absorbs, two
// literals meet, a stuck side keeps it stuck
fn min(a: &V, b: &V) -> V {
    let a = whnf(a);
    match &*a {
        Val::Qua(Q::M) => return whnf(b),
        Val::Qua(Q::N) => return a,
        _ => {}
    }
    let b = whnf(b);
    match (&*a, &*b) {
        (_, Val::Qua(Q::M)) => a,
        (_, Val::Qua(Q::N)) => b,
        (Val::Qua(Q::L), Val::Qua(Q::L)) => b,
        _ => v(Val::Min(a, b)),
    }
}

// whnf without delta, for conversion
fn whnf_nd(x: &V) -> V {
    let x = force(x);
    if let Val::Min(a, b) = &*x {
        return min(a, b);
    }
    x
}

fn is_fun(x: &Val) -> bool {
    matches!(x, Val::Lam(..) | Val::Mat(..) | Val::Neu(..) | Val::Efq | Val::Stuck(..))
}

// a neutral, or a stuck reference read by its name
fn neu(x: &V) -> Option<(&Head, &Vec<V>)> {
    match &**x {
        Val::Neu(h, sp) => Some((h, sp)),
        Val::Stuck(o, _) => neu(o),
        _ => None,
    }
}

pub fn eq(a: &V, b: &V, l: u32) -> bool {
    conv(a, b, false, l)
}

pub fn le(a: &V, b: &V, l: u32) -> bool {
    conv(a, b, true, l)
}

pub fn conv(a: &V, b: &V, le: bool, l: u32) -> bool {
    if Rc::ptr_eq(a, b) {
        return true;
    }
    let a = whnf_nd(a);
    let b = whnf_nd(b);
    if Rc::ptr_eq(&a, &b) {
        return true;
    }
    // eta: a lambda on either side compares its body against the other
    // side applied to a fresh variable
    if matches!(&*a, Val::Lam(..)) || matches!(&*b, Val::Lam(..)) {
        if !is_fun(&a) || !is_fun(&b) {
            return retry(&a, &b, le, l);
        }
        let x = var(l);
        return conv(&apply(&a, x.clone()), &apply(&b, x), le, l + 1);
    }
    let same = match (&*a, &*b) {
        (Val::Typ(g), Val::Typ(h)) => {
            if le {
                kle(g, h, l)
            } else {
                eq(g, h, l)
            }
        }
        (Val::Qnt, Val::Qnt) | (Val::Efq, Val::Efq) | (Val::Rfl, Val::Rfl) => true,
        (Val::Qua(p), Val::Qua(q)) => p == q,
        (Val::Min(a1, a2), Val::Min(b1, b2)) => eq(a1, b1, l) && eq(a2, b2, l),
        (Val::All(p, a1, a2), Val::All(q, b1, b2)) => {
            let x = var(l);
            p == q && conv(b1, a1, le, l) && conv(&a2(x.clone()), &b2(x), le, l + 1)
        }
        (Val::Adt(f, r, ps), Val::Adt(g, s, qs)) => {
            f == g
                && ps.len() == qs.len()
                && s.iter().all(|c| r.contains(c))
                && (le || r.iter().all(|c| s.contains(c)))
                && ps.iter().zip(qs.iter()).all(|(p, q)| eq(p, q, l))
        }
        (Val::Ctr(c, xs), Val::Ctr(d, ys)) => {
            c == d && xs.len() == ys.len() && xs.iter().zip(ys.iter()).all(|(x, y)| eq(x, y, l))
        }
        (Val::Mat(c, h, m), Val::Mat(d, i, n)) => c == d && eq(h, i, l) && eq(m, n, l),
        (Val::Eql(a1, a2, a3), Val::Eql(b1, b2, b3)) => eq(a1, b1, l) && eq(a2, b2, l) && eq(a3, b3, l),
        _ => match (neu(&a), neu(&b)) {
            (Some((h, xs)), Some((k, ys))) => {
                xs.len() == ys.len() && head_eq(h, k, l) && xs.iter().zip(ys.iter()).all(|(x, y)| eq(x, y, l))
            }
            _ => false,
        },
    };
    same || retry(&a, &b, le, l)
}

// lazy delta: unfold the later-defined reference first, both when equal
fn retry(a: &V, b: &V, le: bool, l: u32) -> bool {
    fn open(x: &V) -> Option<(u32, V)> {
        match &**x {
            Val::Stuck(o, u) => neu(o).and_then(|(h, _)| if let Head::Ref(k) = h { Some((*k, u.clone())) } else { None }),
            Val::Neu(Head::Ref(k), _) => delta(*k).map(|_| (*k, unfold(x, true).unwrap())),
            _ => None,
        }
    }
    match (open(a), open(b)) {
        (Some((x, ua)), Some((y, ub))) if x == y => conv(&ua, &ub, le, l),
        (Some((x, ua)), Some((y, _))) if x > y => conv(&ua, b, le, l),
        (Some(_), Some((_, ub))) => conv(a, &ub, le, l),
        (Some((_, ua)), None) => conv(&ua, b, le, l),
        (None, Some((_, ub))) => conv(a, &ub, le, l),
        _ => false,
    }
}

fn head_eq(h: &Head, k: &Head, l: u32) -> bool {
    match (h, k) {
        (Head::Var(i), Head::Var(j)) => i == j,
        (Head::Ref(i), Head::Ref(j)) => i == j,
        (Head::Efq, Head::Efq) => true,
        (Head::Hol(i), Head::Hol(j)) => i == j,
        (Head::Mat(c, h1, m1, s1), Head::Mat(d, h2, m2, s2)) => {
            c == d && eq(s1, s2, l) && eq(h1, h2, l) && eq(m1, m2, l)
        }
        (Head::Rwt(e1, p1, f1), Head::Rwt(e2, p2, f2)) => eq(e1, e2, l) && eq(p1, p2, l) && eq(f1, f2, l),
        _ => false,
    }
}

// KLe: Kind(g) fits Kind(h) when g is &2, h is &0 or &1, a meet on the
// left fits under both sides, a meet on the right under either, or g and
// h convert; a stuck quantity fits only itself
fn kle(g: &V, h: &V, l: u32) -> bool {
    let g = whnf(g);
    let h = whnf(h);
    if matches!(&*g, Val::Qua(Q::M)) || matches!(&*h, Val::Qua(Q::N) | Val::Qua(Q::L)) {
        return true;
    }
    if let Val::Min(g1, g2) = &*g {
        return kle(g1, &h, l) && kle(g2, &h, l);
    }
    if let Val::Min(h1, h2) = &*h {
        return kle(&g, h1, l) || kle(&g, h2, l);
    }
    eq(&g, &h, l)
}

// readback, at depth l (a variable at level i reads as index l - 1 - i)
pub fn quote(x: &V, l: u32) -> T {
    let x = force(x);
    let q = |y: &V| quote(y, l);
    match &*x {
        Val::Lam(m, c) => mk(Tm::Lam(*m, quote(&c(var(l)), l + 1))),
        Val::All(p, a, c) => mk(Tm::All(*p, q(a), quote(&c(var(l)), l + 1))),
        Val::Typ(g) => mk(Tm::Typ(q(g))),
        Val::Qnt => mk(Tm::Qnt),
        Val::Qua(p) => mk(Tm::Qua(*p)),
        Val::Min(a, b) => mk(Tm::Min(q(a), q(b))),
        Val::Adt(a, r, ps) => mk(Tm::Adt(*a, (**r).clone(), ps.iter().map(q).collect())),
        Val::Ctr(c, xs) => mk(Tm::Ctr(*c, xs.iter().map(q).collect())),
        Val::Mat(c, h, m) => mk(Tm::Mat(*c, q(h), q(m))),
        Val::Efq => mk(Tm::Efq),
        Val::Eql(a, b, t) => mk(Tm::Eql(q(a), q(b), q(t))),
        Val::Rfl => mk(Tm::Rfl),
        Val::Neu(h, sp) => {
            let h = match h {
                Head::Var(i) => mk(Tm::Var(l - 1 - i)),
                Head::Ref(k) => mk(Tm::Ref(*k)),
                Head::Mat(c, hh, m, s) => mk(Tm::App(mk(Tm::Mat(*c, q(hh), q(m))), q(s))),
                Head::Efq => mk(Tm::Efq),
                Head::Rwt(e, p, f) => mk(Tm::Rwt(q(e), q(p), q(f))),
                Head::Hol(k) => mk(Tm::Hol(k.clone())),
            };
            sp.iter().fold(h, |f, a| mk(Tm::App(f, q(a))))
        }
        Val::Stuck(o, _) => quote(o, l),
        Val::Thk(..) => unreachable!(),
    }
}

pub fn showv(x: &V, l: u32) -> String {
    let mut fuel = 60;
    show(&quote(x, l), &mut fuel)
}
