// §9 Check and §10 Valid, algorithmically: one bidirectional pass over
// the exported terms, at demand None (dead) or Lone (live), measuring the
// uses of every binder. The rules are bend.lean Part I's, named alike; a
// term the declarative judgment types only through a guess (a constructor
// or a match outside a goal) is refused as "cannot infer", as a checker
// must. Types are values (eval.rs); conversion is compare LE / EQ.

use std::collections::BTreeSet;
use std::panic::{self, AssertUnwindSafe};
use std::rc::Rc;

use crate::eval::*;
use crate::term::*;

pub struct Bind {
    q: Q,
    ty: V,
    // a let binder's value, as a term over the context below it (δ)
    letv: Option<T>,
}

// the equation of the definition under check (bend.lean's LHS): its left
// hand side as a term valid at depth d, the columns still to bind and the
// column quantities
#[derive(Clone)]
pub struct Lhs {
    t: T,
    d: u32,
    n: usize,
    qs: Rc<Vec<Q>>,
    k: u32,
}

type U = Vec<Q>;

fn uadd(mut a: U, b: &U) -> U {
    if a.len() < b.len() {
        a.resize(b.len(), Q::N);
    }
    for (i, q) in b.iter().enumerate() {
        a[i] = Q::add(a[i], *q);
    }
    a
}

fn ujoin(mut a: U, b: &U) -> U {
    if a.len() < b.len() {
        a.resize(b.len(), Q::N);
    }
    for (i, q) in b.iter().enumerate() {
        a[i] = Q::join(a[i], *q);
    }
    a
}

pub struct Ck {
    bs: Vec<Bind>,
    env: Env,
    cur: u32,
    templ: bool,
    unsafe_kinds: bool,
    z: u32,
    pub deps: BTreeSet<u32>,
    selfs: bool,
    fwd: Vec<(u32, Fwd)>,
}

fn all_of(x: &V, what: &str, l: u32) -> (Q, V, Clo) {
    match &*whnf(x) {
        Val::All(q, a, b) => (*q, a.clone(), b.clone()),
        _ => reject(format!("{}: expected a function type, got {}", what, showv(x, l))),
    }
}

fn fam_of(k: u32) -> (usize, Vec<u32>) {
    match &glob(k).g {
        GK::Fam(f) => (f.pn, f.ctrs.clone()),
        _ => reject(format!("{} is not a datatype", gname(k))),
    }
}

// PEq and PLt (§6), on let-expanded terms: a pattern is a variable or a
// constructor of patterns
fn peq(t: &T, p: &T) -> bool {
    match (&**strip(t), &**p) {
        (Tm::Var(i), Tm::Var(j)) => i == j,
        (Tm::Ctr(c, xs), Tm::Ctr(d, ys)) => c == d && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| peq(x, y)),
        _ => false,
    }
}

fn plt(t: &T, p: &T) -> bool {
    let t = strip(t);
    match &**p {
        Tm::Ctr(c, ys) => {
            if ys.iter().any(|y| peq(&t, y) || plt(&t, y)) {
                return true;
            }
            match &**t {
                Tm::Ctr(d, xs) if c == d && xs.len() == ys.len() => {
                    let mut lt = false;
                    for (x, y) in xs.iter().zip(ys) {
                        if plt(x, y) {
                            lt = true;
                        } else if !peq(x, y) {
                            return false;
                        }
                    }
                    lt
                }
                _ => false,
            }
        }
        _ => false,
    }
}

fn strip(t: &T) -> &T {
    match &**t {
        Tm::Ann(x, _) => strip(x),
        _ => t,
    }
}

// Tree (§10): the body is a case tree over its n columns
fn tree(n: usize, t: &T) -> bool {
    if n == 0 {
        return true;
    }
    match &**t {
        Tm::Lam(_, f) => tree(n - 1, f),
        Tm::Mat(c, h, m) => tree(n - 1 + ctor(*c).fields, h) && tree(n, m),
        Tm::Efq => true,
        _ => false,
    }
}

impl Ck {
    pub fn new(cur: u32, templ: bool, unsafe_kinds: bool, z: u32) -> Ck {
        Ck { bs: vec![], env: Env::default(), cur, templ, unsafe_kinds, z, deps: BTreeSet::new(), selfs: false, fwd: vec![] }
    }

    fn lvl(&self) -> u32 {
        self.bs.len() as u32
    }

    fn bind(&mut self, q: Q, ty: V, val: V, letv: Option<T>) {
        self.bs.push(Bind { q, ty, letv });
        self.env = self.env.push(val);
    }

    fn unbind(&mut self) {
        self.bs.pop();
        let e = self.env.0.as_ref().unwrap().1.clone();
        self.env = e;
    }

    fn ev(&self, t: &T) -> V {
        eval(&self.env, t)
    }

    fn sh(&self, x: &V) -> String {
        showv(x, self.lvl())
    }

    // Ctx.δ: every let-bound variable replaced by its value
    fn dexp(&self, t: &T, len: usize) -> T {
        mapv(t, 0, &|i, d| {
            if i < d || (i - d) as usize >= len {
                return mk(Tm::Var(i));
            }
            let idx = (i - d) as usize;
            let at = len - 1 - idx;
            match &self.bs[at].letv {
                Some(v) => shift(&self.dexp(v, at), (idx + 1) as u32 + d),
                None => mk(Tm::Var(i)),
            }
        })
    }

    fn lhs_lam(&self, l: &Lhs) -> Lhs {
        if l.n == 0 {
            return l.clone();
        }
        let t = shift(&l.t, self.lvl() + 1 - l.d);
        Lhs { t: apply_b(&t, &mk(Tm::Var(0))), d: self.lvl() + 1, n: l.n - 1, ..l.clone() }
    }

    fn lhs_mat(&self, l: &Lhs, c: u32, fields: usize) -> Lhs {
        if l.n == 0 {
            return l.clone();
        }
        let t = shift(&l.t, self.lvl() - l.d);
        let xs = (0..fields).map(|i| mk(Tm::Var((fields - 1 - i) as u32))).collect();
        let mut e = apply_b(&shift(&t, fields as u32), &mk(Tm::Ctr(c, xs)));
        for _ in 0..fields {
            e = mk(Tm::Lam(false, e));
        }
        Lhs { t: e, d: self.lvl(), n: l.n - 1 + fields, ..l.clone() }
    }

    // SpineLt: live columns compare EQ left to right until one argument is
    // a strict subterm of its column; an erased column is skipped
    fn descends(&self, l: &Lhs, sp: &[T]) -> bool {
        let t = shift(&l.t, self.lvl() - l.d);
        let cols = spine(&t).1;
        let len = self.bs.len();
        for (j, (c, a)) in cols.iter().zip(sp).enumerate() {
            if l.qs.get(j).copied().unwrap_or(Q::L) == Q::N {
                continue;
            }
            let (c, a) = (self.dexp(c, len), self.dexp(a, len));
            if peq(&a, &c) {
                continue;
            }
            return plt(&a, &c);
        }
        false
    }

    // Γ ⊢ t : ? at demand qt, with sp the arguments pending above t
    fn infer(&mut self, l: &Lhs, t: &T, qt: Q, sp: &[T]) -> (V, U) {
        match &**t {
            Tm::Var(i) => {
                let lv = self.bs.len() - 1 - *i as usize;
                let mut u = vec![Q::N; lv + 1];
                u[lv] = qt;
                (self.bs[lv].ty.clone(), u)
            }
            Tm::Ref(k) => {
                let (ty, _) = self.infer_ref(l, *k, qt, sp);
                (ty, vec![])
            }
            Tm::Typ(g) => {
                self.check(l, g, Q::N, &v(Val::Qnt));
                (typ(Q::L), vec![])
            }
            Tm::Qnt => (typ(Q::L), vec![]),
            Tm::Qua(_) => (v(Val::Qnt), vec![]),
            Tm::Min(a, b) => {
                let ua = self.check(l, a, qt, &v(Val::Qnt));
                let ub = self.check(l, b, qt, &v(Val::Qnt));
                (v(Val::Qnt), uadd(ua, &ub))
            }
            Tm::All(q, a, b) => {
                let kq = if self.unsafe_kinds && *q == Q::M { Q::L } else { *q };
                self.check(l, a, Q::N, &typ(kq));
                let av = self.ev(a);
                self.bind(*q, av, var(self.lvl()), None);
                self.check(l, b, Q::N, &typ(Q::L));
                self.unbind();
                (typ(Q::L), vec![])
            }
            Tm::App(..) => {
                let (h, xs) = spine(t);
                if let Tm::Lam(_, f) = &*h {
                    // (λ f)(a): one beta step (appLam)
                    let mut r = subst(f, &xs[0]);
                    for x in &xs[1..] {
                        r = mk(Tm::App(r, x.clone()));
                    }
                    return self.infer(l, &r, qt, sp);
                }
                let mut all: Vec<T> = xs.clone();
                all.extend_from_slice(sp);
                let (mut ft, mut u, skip) = match &*h {
                    Tm::Ref(k) => {
                        let (ty, skip) = self.infer_ref(l, *k, qt, &all);
                        (ty, vec![], skip)
                    }
                    _ => {
                        let (ty, u) = self.infer(l, &h, qt, &all);
                        (ty, u, 0)
                    }
                };
                for x in &xs[skip.min(xs.len())..] {
                    let (q, a, b) = all_of(&ft, "an application", self.lvl());
                    let ux = self.check(l, x, Q::dem(q, qt), &a);
                    u = uadd(u, &ux);
                    ft = b(self.ev(x));
                }
                if skip > xs.len() {
                    reject(format!("a template {} applied to too few ~ arguments", show(&h, &mut 5)));
                }
                (ft, u)
            }
            Tm::Adt(a, r, ps) => {
                let (pn, cs) = fam_of(*a);
                if ps.len() != pn || !r.iter().all(|c| cs.contains(c)) {
                    reject(format!("{} with {} parameters and its own constructors", gname(*a), pn));
                }
                self.deps.insert(*a);
                let mut tel = def_tyv(*a);
                let mut u = vec![];
                for p in ps {
                    let (q, d, b) = all_of(&tel, "a family's parameters", self.lvl());
                    u = uadd(u, &self.check(l, p, Q::dem(q, qt), &d));
                    tel = b(self.ev(p));
                }
                (tel, u)
            }
            Tm::Eql(a, b, ty) => {
                self.check(l, ty, Q::N, &typ(Q::L));
                let tv = self.ev(ty);
                self.check(l, a, Q::N, &tv);
                self.check(l, b, Q::N, &tv);
                (typ(Q::M), vec![])
            }
            Tm::Ann(x, ty) => {
                self.check(l, ty, Q::N, &typ(Q::L));
                let tv = self.ev(ty);
                let u = self.check(l, x, qt, &tv);
                (tv, u)
            }
            _ => reject(format!("cannot infer {} (a goal is needed)", show(t, &mut 12))),
        }
    }

    // infer-ref: a live reference points at a definition already checked
    // or at this one; a live self-reference descends; a live call to a
    // template from outside a template's own text is its instance at the
    // closed ~ arguments (the returned count of spine entries it took)
    fn infer_ref(&mut self, l: &Lhs, k: u32, qt: Q, sp: &[T]) -> (V, usize) {
        self.deps.insert(k);
        let g = glob(k);
        let d = match &g.g {
            GK::Fam(f) => {
                if f.pn > 0 {
                    reject(format!("a bare parameterized family head {}", g.name));
                }
                return (def_tyv(k), 0);
            }
            GK::Bad(m) => unsup(format!("a reference to {}, which the reader refused: {}", g.name, m)),
            GK::Def(d) => d,
        };
        if qt == Q::N {
            return (def_tyv(k), 0);
        }
        if d.x > 0 && !self.templ {
            let i = self.instance(k, d, sp);
            self.deps.insert(i);
            return (def_tyv(i), d.x);
        }
        let (done, pend, later) = BK.with(|b| {
            let b = b.borrow();
            let later = match (b.pos.get(&k), b.pos.get(&self.cur)) {
                (Some(i), Some(j)) => i > j && self.cur == l.k,
                _ => false,
            };
            (b.done[k as usize], b.pending.get(&k).cloned(), later)
        });
        if k == l.k {
            self.selfs = true;
            if !self.descends(l, sp) {
                let mut f = 40;
                let sps: Vec<String> = sp.iter().map(|a| show(a, &mut f)).collect();
                reject(format!("a self-call of {} that does not descend: ({})", g.name, sps.join(", ")));
            }
        } else if let Some((_, sites)) = pend.clone().filter(|(to, _)| *to == self.cur) {
            // a call back into a helper whose own live calls reach this
            // def: each cycle, this call composed with a site of the
            // helper's, must descend against this def's columns
            let len = self.bs.len();
            let a: Vec<T> = sp.iter().map(|x| self.dexp(x, len)).collect();
            for f in &sites {
                let b = compose(f, &a);
                if !self.descends(l, &b) {
                    reject(format!("a mutual call through {} that does not descend", g.name));
                }
            }
        } else if let Some((to, sites)) = pend.filter(|_| !self.templ && self.z == 0 && self.cur == l.k) {
            // a call into a helper that is itself waiting on a later def:
            // this def waits on it too, its sites the helper's composed
            // with this call
            let len = self.bs.len();
            let a: Vec<T> = sp.iter().map(|x| self.dexp(x, len)).collect();
            let t = shift(&l.t, self.lvl() - l.d);
            let cols: Vec<T> = spine(&t).1.iter().map(|c| self.dexp(c, len)).collect();
            for f in &sites {
                self.fwd.push((to, Fwd { cols: cols.clone(), args: compose(f, &a) }));
            }
        } else if !done && later && !self.templ && self.z == 0 && d.x == 0 && d.body.is_some() {
            // a forward call (the base file's helper-law pairs): held as a
            // site, and checked for descent when the callee checks
            let len = self.bs.len();
            let t = shift(&l.t, self.lvl() - l.d);
            let cols = spine(&t).1.iter().map(|c| self.dexp(c, len)).collect();
            let args = sp.iter().map(|x| self.dexp(x, len)).collect();
            self.fwd.push((k, Fwd { cols, args }));
        } else if !done {
            reject(format!("a live reference to {}, which is not checked before this definition (a forward or mutual call)", g.name));
        }
        if d.body.is_none() && !d.konst && !d.foreign && !d.base {
            reject(format!("a live use of the unfilled law {}", g.name));
        }
        (def_tyv(k), 0)
    }

    fn instance(&mut self, k: u32, d: &Def, sp: &[T]) -> u32 {
        if sp.len() < d.x {
            reject(format!("the template {} applied to fewer than its {} ~ arguments", gname(k), d.x));
        }
        let args: Vec<T> = sp[..d.x].to_vec();
        let mut tel = def_tyv(k);
        for a in &args {
            if !closed(a, 0) {
                reject(format!("the template {} applied to an open ~ argument", gname(k)));
            }
            let (_, dom, b) = all_of(&tel, "a template", 0);
            let mut ck = Ck::new(self.cur, false, false, self.z);
            let l0 = Lhs { t: mk(Tm::Ref(u32::MAX)), d: 0, n: 0, qs: Rc::new(vec![]), k: u32::MAX };
            ck.check(&l0, a, Q::N, &dom);
            self.deps.extend(ck.deps);
            tel = b(eval(&Env::default(), a));
        }
        let key = (k, args.clone());
        if let Some(i) = BK.with(|b| b.borrow().insts.get(&key).copied()) {
            let done = BK.with(|b| b.borrow().done[i as usize]);
            if !done && i != self.cur {
                reject(format!("an instance of {} that calls itself back without descending", gname(k)));
            }
            return i;
        }
        if self.z >= 64 {
            unsup(format!("a template {} that instantiates itself more than 64 levels deep", gname(k)));
        }
        let body = args.iter().fold(d.body.clone().expect("a template body"), |b, a| apply_b(&b, a));
        let n = BK.with(|b| b.borrow().insts.len());
        let name = format!("{}~{}", gname(k), n);
        let def = Def {
            n: d.n - d.x,
            x: 0,
            law: false,
            base: d.base,
            unsafe_: d.unsafe_,
            foreign: false,
            konst: false,
            ty: None,
            body: Some(body),
            tyv: tel.clone().into(),
            bodyv: Default::default(),
        };
        let i = push_glob(Glob { name: name.clone(), g: GK::Def(def) });
        BK.with(|b| b.borrow_mut().insts.insert(key, i));
        let (vd, deps) = check_def(i, self.z + 1);
        BK.with(|b| {
            let mut b = b.borrow_mut();
            b.verdict[i as usize] = Some(vd.clone());
            b.deps[i as usize] = deps;
            b.done[i as usize] = true;
        });
        match vd {
            Verdict::Reject(m) => reject(format!("instance {}: {}", name, m)),
            Verdict::Unsup(m) => unsup(format!("instance {}: {}", name, m)),
            _ => i,
        }
    }

    // Γ ⊢ t : ty at demand qt
    pub fn check(&mut self, l: &Lhs, t: &T, qt: Q, ty: &V) -> U {
        match &**t {
            Tm::Lam(mark, f) => {
                let (q, a, b) = all_of(ty, "a lambda", self.lvl());
                // a + mark rebinds an affine binder reusable: its domain
                // must be Data (a Many binder forms only at Data)
                let q = if *mark && q == Q::L { Q::M } else { q };
                if q == Q::M && !self.unsafe_kinds {
                    let at = quote(&a, self.lvl());
                    self.check(l, &at, Q::N, &typ(Q::M));
                }
                let lv = self.lvl();
                let l2 = self.lhs_lam(l);
                self.bind(q, a, var(lv), None);
                let mut u = self.check(&l2, f, qt, &b(var(lv)));
                self.unbind();
                self.close(&mut u, lv, q, "a lambda binder");
                u
            }
            Tm::Let(q, x, b) => {
                let (a, ux) = self.infer(l, x, Q::dem(*q, qt), &[]);
                let at = quote(&a, self.lvl());
                self.check(l, &at, Q::N, &typ(*q));
                let lv = self.lvl();
                let xv = self.ev(x);
                self.bind(*q, a, xv, Some(x.clone()));
                let mut u = self.check(l, b, qt, ty);
                self.unbind();
                self.close(&mut u, lv, *q, "a let binder");
                uadd(ux, &u)
            }
            Tm::Ctr(c, xs) => {
                let tw = whnf(ty);
                let (a, r, ps) = match &*tw {
                    Val::Adt(a, r, ps) => (*a, r.clone(), ps.clone()),
                    _ => reject(format!("constructor {} against {}", ctor(*c).name, self.sh(ty))),
                };
                let k = ctor(*c);
                if k.fam != a || r.contains(c) {
                    reject(format!("constructor {} against {}", k.name, self.sh(ty)));
                }
                if xs.len() != k.fields {
                    reject(format!("{} with {} fields", k.name, k.fields));
                }
                self.deps.insert(a);
                let mut tel = ctor_tyv(*c);
                for p in &ps {
                    tel = all_of(&tel, "a constructor's parameters", self.lvl()).2(p.clone());
                }
                let mut u = vec![];
                for x in xs {
                    let (q, d, b) = all_of(&tel, "a constructor's fields", self.lvl());
                    u = uadd(u, &self.check(l, x, Q::dem(q, qt), &d));
                    tel = b(self.ev(x));
                }
                u
            }
            Tm::Mat(..) | Tm::Efq => {
                let (q, d, b) = all_of(ty, "a match", self.lvl());
                if qt != Q::N && q == Q::N {
                    reject("a live match on an erased scrutinee".into());
                }
                let dw = whnf(&d);
                let (a, r, ps) = match &*dw {
                    Val::Adt(a, r, ps) => (*a, r.clone(), ps.clone()),
                    _ => reject(format!("a match on a non-datatype {}", self.sh(&d))),
                };
                let (_, cs) = fam_of(a);
                self.deps.insert(a);
                let Tm::Mat(c, h, m) = &**t else {
                    // check-efq: no constructor left, or a live binding in
                    // scope has an emptied datatype
                    if cs.iter().all(|c| r.contains(c)) || self.ctx_dead() {
                        return vec![];
                    }
                    let left: Vec<String> = cs.iter().filter(|c| !r.contains(c)).map(|c| ctor(*c).name.clone()).collect();
                    reject(format!("a match missing cases for {}", left.join(", ")));
                };
                if !cs.contains(c) || r.contains(c) {
                    reject(format!("a case {} not among the remaining constructors of {}", ctor(*c).name, gname(a)));
                }
                let k = ctor(*c);
                let mut tel = ctor_tyv(*c);
                for p in &ps {
                    tel = all_of(&tel, "a constructor's parameters", self.lvl()).2(p.clone());
                }
                let goal = mat_goal(tel, k.fields, q, b.clone(), *c, vec![]);
                let uh = self.check(&self.lhs_mat(l, *c, k.fields), h, qt, &goal);
                let mut r2 = (*r).clone();
                r2.push(*c);
                let mg = v(Val::All(q, v(Val::Adt(a, Rc::new(r2), ps)), b));
                let um = self.check(l, m, qt, &mg);
                ujoin(uh, &um)
            }
            Tm::Rfl => {
                let tw = whnf(ty);
                match &*tw {
                    Val::Eql(a, b, _) => {
                        if !eq(a, b, self.lvl()) {
                            reject(format!("{{==}} at {} != {}", self.sh(a), self.sh(b)));
                        }
                        vec![]
                    }
                    _ => reject(format!("{{==}} against {}", self.sh(ty))),
                }
            }
            Tm::Rwt(e, p, f) => {
                let (et, ue) = self.infer(l, e, qt, &[]);
                let ew = whnf(&et);
                let (a, b, tt) = match &*ew {
                    Val::Eql(a, b, tt) => (a.clone(), b.clone(), tt.clone()),
                    _ => reject(format!("a rewrite by a non-equation {}", self.sh(&et))),
                };
                // the J motive: @x:T -> @_:{a == x : T} -> Type
                let (a2, t2) = (a.clone(), tt.clone());
                let mt = v(Val::All(Q::L, tt.clone(), Rc::new(move |x| {
                    v(Val::All(Q::L, v(Val::Eql(a2.clone(), x, t2.clone())), Rc::new(|_| typ(Q::L))))
                })));
                self.check(l, p, Q::N, &mt);
                let pv = self.ev(p);
                let bg = apply(&apply(&pv, b), self.ev(e));
                if !le(&bg, ty, self.lvl()) {
                    reject(format!("a rewrite giving {} where {} is expected", self.sh(&bg), self.sh(ty)));
                }
                let ag = apply(&apply(&pv, a), v(Val::Rfl));
                let uf = self.check(l, f, qt, &ag);
                uadd(ue, &uf)
            }
            Tm::Hol(k) => unsup(format!("a hole ?{}", k)),
            _ => {
                let (a, u) = self.infer(l, t, qt, &[]);
                if !le(&a, ty, self.lvl()) {
                    reject(format!("{} : {} where {} is expected", show(t, &mut 20), self.sh(&a), self.sh(ty)));
                }
                u
            }
        }
    }

    // a binder's measured use must not exceed its declared quantity
    fn close(&self, u: &mut U, lv: u32, q: Q, what: &str) {
        let used = u.get(lv as usize).copied().unwrap_or(Q::N);
        if !Q::le(used, q) {
            reject(format!("{} of quantity {} used at {}", what, q.show(), used.show()));
        }
        u.truncate(lv as usize);
    }

    // CtxDead: a live binding whose type is an emptied datatype
    fn ctx_dead(&self) -> bool {
        self.bs.iter().any(|b| {
            b.q != Q::N
                && match &*whnf(&b.ty) {
                    Val::Adt(a, r, _) => fam_of(*a).1.iter().all(|c| r.contains(c)),
                    _ => false,
                }
        })
    }
}

// the arguments a helper's forward call passes, given the arguments a
// caller passes the helper: the helper's columns at the site match the
// caller's arguments, binding the site's variables; a variable they do
// not bind is opaque (equal to nothing, smaller than nothing)
fn compose(f: &Fwd, a: &[T]) -> Vec<T> {
    fn bind(p: &T, a: &T, sg: &mut Vec<(u32, T)>) {
        match (&**p, &**a) {
            (Tm::Var(i), _) => sg.push((*i, a.clone())),
            (Tm::Ctr(c, ps), Tm::Ctr(e, xs)) if c == e && ps.len() == xs.len() => {
                for (p, x) in ps.iter().zip(xs) {
                    bind(p, x, sg);
                }
            }
            _ => {}
        }
    }
    let mut sg = vec![];
    for (p, x) in f.cols.iter().zip(a) {
        bind(p, x, &mut sg);
    }
    f.args.iter().map(|b| mapv(b, 0, &|i, d| {
        if i < d {
            return mk(Tm::Var(i));
        }
        match sg.iter().find(|(j, _)| *j == i - d) {
            Some((_, t)) => shift(t, d),
            None => mk(Tm::Hol("opaque".into())),
        }
    })).collect()
}

// MatGoal: the arm's goal, the instantiated field telescope with each
// field's quantity times the scrutinee's, tipped at the motive applied to
// the constructor of the fields
fn mat_goal(tel: V, n: usize, q: Q, b: Clo, c: u32, xs: Vec<V>) -> V {
    if n == 0 {
        return b(v(Val::Ctr(c, xs)));
    }
    let (qf, a, rest) = all_of(&tel, "a constructor's fields", 0);
    v(Val::All(Q::mul(qf, q), a, Rc::new(move |x| {
        let mut ys = xs.clone();
        ys.push(x.clone());
        mat_goal(rest(x), n - 1, q, b.clone(), c, ys)
    })))
}

fn caught(r: std::thread::Result<Verdict>) -> Verdict {
    match r {
        Ok(v) => v,
        Err(e) => match e.downcast::<Fail>() {
            Ok(f) => match *f {
                Fail::Reject(m) => Verdict::Reject(m),
                Fail::Unsup(m) => Verdict::Unsup(m),
            },
            Err(e) => {
                let m = e.downcast_ref::<&str>().map(|s| s.to_string())
                    .or_else(|| e.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "a kernel fault".into());
                Verdict::Unsup(format!("kernel fault: {}", m))
            }
        },
    }
}

const FUEL_PER_DEF: u64 = 50_000_000;

fn with_fuel<F: FnOnce() -> Verdict>(f: F) -> Verdict {
    let saved = FUEL.with(|x| x.get());
    FUEL.with(|x| x.set(FUEL_PER_DEF));
    let r = caught(panic::catch_unwind(AssertUnwindSafe(f)));
    FUEL.with(|x| x.set(saved));
    r
}

// Book.Ok for a definition: its type is a type (dead), its column
// quantities are read off it, its body is a case tree over the columns
// and checks LIVE against the type under its own equation. A foreign,
// native or unfilled def, and an @unsafe one, is an axiom: only its type
// is checked.
pub fn check_def(k: u32, z: u32) -> (Verdict, BTreeSet<u32>) {
    let g = glob(k);
    let d = match &g.g {
        GK::Def(d) => d,
        GK::Bad(m) => return (Verdict::Reject(format!("ill-formed: {}", m)), BTreeSet::new()),
        GK::Fam(_) => return check_fam(k),
    };
    let mut deps = BTreeSet::new();
    let vd = with_fuel(|| {
        let l0 = Lhs { t: mk(Tm::Ref(k)), d: 0, n: 0, qs: Rc::new(vec![]), k };
        if let Some(ty) = &d.ty {
            let mut ck = Ck::new(k, true, d.unsafe_, z);
            ck.check(&l0, ty, Q::N, &typ(Q::L));
            deps.extend(ck.deps);
        }
        let body = match &d.body {
            None if d.foreign => {
                // foreign code answers only through IO: its type's tip is
                // an application of base's IO, so it proves nothing
                let mut t = d.ty.clone().expect("a typed def");
                while let Tm::All(_, _, b) = &*t.clone() {
                    t = b.clone();
                }
                let io = match &*spine(&t).0 {
                    Tm::Ref(h) => matches!(&glob(*h).g, GK::Def(Def { base: true, .. })) && gname(*h) == "IO",
                    _ => false,
                };
                if !io {
                    reject("a foreign def that does not return base IO(..)".into());
                }
                return Verdict::Axiom("foreign");
            }
            None if d.base => return Verdict::Axiom("native"),
            None => return Verdict::Axiom("unfilled"),
            Some(_) if d.unsafe_ => return Verdict::Axiom("unsafe"),
            Some(b) => b.clone(),
        };
        let mut tel = def_tyv(k);
        let mut qs = vec![];
        for _ in 0..d.n {
            match &*whnf(&tel) {
                Val::All(q, _, b) => {
                    qs.push(*q);
                    tel = b(var(qs.len() as u32 - 1));
                }
                _ => break,
            }
        }
        qs.resize(d.n, Q::L);
        if !tree(d.n, &body) {
            reject(format!("a body that is not a case tree over its {} columns", d.n));
        }
        // a template checks once, its ~ parameters opaque constants
        let (mut t, mut body, mut ty) = (mk(Tm::Ref(k)), body, def_tyv(k));
        for j in 0..d.x {
            let (_, a, b) = all_of(&ty, "a template's ~ parameters", 0);
            let c = push_glob(Glob {
                name: format!("{}~{}", g.name, j),
                g: GK::Def(Def {
                    n: 0, x: 0, law: false, base: true, unsafe_: false, foreign: false, konst: true,
                    ty: None, body: None, tyv: a.into(), bodyv: Default::default(),
                }),
            });
            BK.with(|b| b.borrow_mut().done[c as usize] = true);
            t = mk(Tm::App(t, mk(Tm::Ref(c))));
            body = apply_b(&body, &mk(Tm::Ref(c)));
            ty = b(ref_val(c));
        }
        let l = Lhs { t, d: 0, n: d.n - d.x, qs: Rc::new(qs), k };
        let mut ck = Ck::new(k, d.x > 0, false, z);
        ck.check(&l, &body, Q::L, &ty);
        deps.extend(ck.deps);
        if let Some((to, _)) = ck.fwd.first() {
            let to = *to;
            if ck.selfs || ck.fwd.iter().any(|(t, _)| *t != to) {
                reject("forward calls from a recursive helper, or to two defs (only a helper-law pair is checked)".into());
            }
            let sites = ck.fwd.into_iter().map(|(_, f)| f).collect();
            BK.with(|b| b.borrow_mut().pending.insert(k, (to, sites)));
        }
        Verdict::Ok
    });
    (vd, deps)
}

// Book.Ok for a family: its signature is a type tipped at a kind Kind(G)
// after its parameters; each constructor is a telescope of the parameters
// then its fields, tipped at the family at its own parameters; a parameter
// or a non-affine field's domain fits Kind(q), an affine field's Kind(G)
fn check_fam(k: u32) -> (Verdict, BTreeSet<u32>) {
    let g = glob(k);
    let GK::Fam(f) = &g.g else { unreachable!() };
    let mut deps = BTreeSet::new();
    let vd = with_fuel(|| {
        let l0 = Lhs { t: mk(Tm::Ref(k)), d: 0, n: 0, qs: Rc::new(vec![]), k };
        let mut ck = Ck::new(k, true, false, 0);
        ck.check(&l0, &f.sig, Q::N, &typ(Q::L));
        let mut s = f.sig.clone();
        for _ in 0..f.pn {
            match &*s.clone() {
                Tm::All(q, a, b) => {
                    let av = ck.ev(a);
                    ck.bind(*q, av, var(ck.lvl()), None);
                    s = b.clone();
                }
                _ => reject("a signature with fewer binders than parameters".into()),
            }
        }
        let gk = match &*whnf(&ck.ev(&s)) {
            Val::Typ(gk) => gk.clone(),
            _ => reject("a signature not tipped at a kind".into()),
        };
        deps.extend(ck.deps.iter());
        for c in &f.ctrs {
            let kc = ctor(*c);
            let mut ck = Ck::new(k, true, false, 0);
            let mut s = kc.ty.clone();
            let n = f.pn + kc.fields;
            for i in 0..n {
                match &*s.clone() {
                    Tm::All(q, a, b) => {
                        let goal = if i >= f.pn && *q == Q::L { v(Val::Typ(gk.clone())) } else { typ(*q) };
                        ck.check(&l0, a, Q::N, &goal);
                        let av = ck.ev(a);
                        ck.bind(*q, av, var(i as u32), None);
                        s = b.clone();
                    }
                    _ => reject(format!("constructor {} is not a telescope of {} binders", kc.name, n)),
                }
            }
            let tip_ok = match &*s {
                Tm::Adt(a, r, ps) => {
                    *a == k && r.is_empty() && ps.len() == f.pn
                        && ps.iter().enumerate().all(|(j, p)| **p == Tm::Var((n - 1 - j) as u32))
                }
                _ => false,
            };
            if !tip_ok {
                reject(format!("constructor {} not tipped at {} applied to its own parameters", kc.name, g.name));
            }
            deps.extend(ck.deps.iter());
        }
        Verdict::Ok
    });
    deps.remove(&k);
    (vd, deps)
}
