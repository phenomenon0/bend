// bend-kernel: an independent re-checker for Bend's core calculus.
//
// It reads the book bend.ts exported (bend <file> --export <out>) and
// checks every family and definition from scratch, in file order, against
// the rules of bend2/bend.lean Part I (§9 Check, §10 Valid), with its own
// terms, evaluator and conversion (eval.rs), and prints one verdict per
// item:
//
//   OK           the item checks (a law also lists the axioms it rests on)
//   AXIOM        a foreign, native (a bodiless base def), unfilled or
//                @unsafe def: taken on trust, its type alone checked
//   REJECT       the kernel refuses it, and says why
//   UNSUPPORTED  the kernel cannot decide it (fuel, a hole, a fault)
//
// An item that leans on a REJECT or UNSUPPORTED one lists it among its
// axioms as !name: nothing is accepted silently. The verdict (and exit
// status 0) is PASS when every item outside base is OK or AXIOM, no law
// of the file is left unfilled or leans on an @unsafe def or an unfilled
// law, and no law of the file, nor main, leans on a refused item; -q prints only the
// refusals and the file's laws (and main) with their axioms.
//
// usage: bend-kernel <file.core> [-q] [--axioms NAME]..

mod check;
mod eval;
mod term;

use std::collections::BTreeSet;

use term::*;

fn axioms(k: u32, out: &mut BTreeSet<String>, seen: &mut BTreeSet<u32>) {
    if !seen.insert(k) {
        return;
    }
    let (vd, deps) = BK.with(|b| {
        let b = b.borrow();
        (b.verdict[k as usize].clone(), b.deps[k as usize].clone())
    });
    let g = glob(k);
    match vd {
        Some(Verdict::Axiom(kind)) => {
            out.insert(format!("{} ({})", g.name, kind));
        }
        Some(Verdict::Reject(_)) | Some(Verdict::Unsup(_)) => {
            out.insert(format!("!{}", g.name));
        }
        _ => {}
    }
    for d in deps {
        axioms(d, out, seen);
    }
}

fn run() -> i32 {
    let args: Vec<String> = std::env::args().collect();
    let mut file = None;
    let mut quiet = false;
    let mut want: Vec<String> = vec![];
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-q" => quiet = true,
            "--axioms" => {
                i += 1;
                want.push(args.get(i).cloned().unwrap_or_default());
            }
            f => file = Some(f.to_string()),
        }
        i += 1;
    }
    let Some(file) = file else {
        eprintln!("usage: bend-kernel <file.core> [-q] [--axioms NAME]..");
        return 2;
    };
    let src = match std::fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("bend-kernel: {}: {}", file, e);
            return 2;
        }
    };
    if let Err(e) = load(&src) {
        eprintln!("bend-kernel: {}: {}", file, e);
        return 2;
    }
    std::panic::set_hook(Box::new(|_| {}));
    let order = BK.with(|b| b.borrow().order.clone());
    for &k in &order {
        let (vd, deps) = check::check_def(k, 0);
        BK.with(|b| {
            let mut b = b.borrow_mut();
            let ok = matches!(vd, Verdict::Ok);
            // a helper that calls ahead is done only once its callee is
            b.done[k as usize] = !b.pending.contains_key(&k) || !ok;
            b.verdict[k as usize] = Some(vd);
            b.deps[k as usize] = deps;
            let waiting: Vec<u32> = b.pending.iter().filter(|(_, (to, _))| *to == k).map(|(h, _)| *h).collect();
            for h in waiting {
                b.pending.remove(&h);
                b.done[h as usize] = true;
                if !ok {
                    let m = format!("its forward call's callee {} is refused", b.globs[k as usize].name);
                    b.verdict[h as usize] = Some(Verdict::Reject(m));
                }
            }
        });
    }
    BK.with(|b| {
        let mut b = b.borrow_mut();
        let left: Vec<(u32, u32)> = b.pending.iter().map(|(h, (to, _))| (*h, *to)).collect();
        for (h, to) in left {
            let m = format!("a forward call to {}, which never checks", b.globs[to as usize].name);
            b.verdict[h as usize] = Some(Verdict::Reject(m));
        }
    });
    // counts: [ok, axiom, reject, unsupported], for base and for the rest
    let mut cnt = [[0usize; 4]; 2];
    let mut leans = 0;
    for &k in &order {
        let g = glob(k);
        let law = matches!(&g.g, GK::Def(d) if d.law && d.body.is_some());
        let base = matches!(&g.g, GK::Def(Def { base: true, .. }) | GK::Fam(Fam { base: true, .. }));
        let own = !base && (law || g.name == "main");
        let vd = BK.with(|b| b.borrow().verdict[k as usize].clone()).unwrap();
        let tag = if base { " [base]" } else { "" };
        let line = match &vd {
            Verdict::Ok => {
                cnt[!base as usize][0] += 1;
                if law || own || want.contains(&g.name) {
                    let mut out = BTreeSet::new();
                    let deps = BK.with(|b| b.borrow().deps[k as usize].clone());
                    let mut seen = BTreeSet::from([k]);
                    for d in deps {
                        axioms(d, &mut out, &mut seen);
                    }
                    // a law of the file proves nothing if it leans on a
                    // refused item, an @unsafe def or an unfilled law
                    let weak = |a: &String| a.starts_with('!') || (law && (a.ends_with("(unsafe)") || a.ends_with("(unfilled)")));
                    if own && out.iter().any(weak) {
                        leans += 1;
                    }
                    let list: Vec<String> = out.into_iter().collect();
                    let lt = if law { " [law]" } else { "" };
                    (!quiet || own || want.contains(&g.name)).then(|| format!("OK {}{}{} axioms: {}", g.name, lt, tag,
                        if list.is_empty() { "none".into() } else { list.join(", ") }))
                } else {
                    (!quiet).then(|| format!("OK {}{}", g.name, tag))
                }
            }
            Verdict::Axiom(kind) => {
                cnt[!base as usize][1] += 1;
                if !base && *kind == "unfilled" {
                    leans += 1;
                    println!("OPEN {}: an unfilled law, a claim with no proof", g.name);
                }
                if !base && law && *kind == "unsafe" {
                    leans += 1;
                    println!("OPEN {}: a law filled by an @unsafe def, a claim with no proof", g.name);
                }
                (!quiet).then(|| format!("AXIOM {}{} ({})", g.name, tag, kind))
            }
            Verdict::Reject(m) => {
                cnt[!base as usize][2] += 1;
                Some(format!("REJECT {}{}: {}", g.name, tag, m))
            }
            Verdict::Unsup(m) => {
                cnt[!base as usize][3] += 1;
                Some(format!("UNSUPPORTED {}{}: {}", g.name, tag, m))
            }
        };
        if let Some(line) = line {
            println!("{}", line);
        }
    }
    for (i, what) in ["base", "file"].iter().enumerate() {
        let c = cnt[i];
        println!("summary {}: {} ok, {} axiom, {} reject, {} unsupported", what, c[0], c[1], c[2], c[3]);
    }
    // the verdict: every item of the file checks, no law of the file is
    // left unfilled, and no law of the file (nor main) leans on an item
    // the kernel refused
    let pass = cnt[1][2] + cnt[1][3] == 0 && leans == 0;
    println!("verdict: {}", if pass { "PASS" } else { "FAIL" });
    if pass {
        0
    } else {
        1
    }
}

fn main() {
    // deep terms (literals, long proofs) recurse deeply: a large stack
    let h = std::thread::Builder::new().stack_size(4 << 30).spawn(run).expect("a checker thread");
    std::process::exit(h.join().unwrap_or(3));
}
