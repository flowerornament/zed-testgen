//! Branch coverage for Zed functions of integer parameters, from the compiler's own backward
//! solver (`zedc::store::preimage`).
//!
//! Every arm of every `if` in a function's body has a path condition: the guards that must hold
//! to reach it. For each arm the tool asks two questions of that condition:
//!
//! - **Is it dead?** `preimage` over unbounded integer inputs gives a box that holds every input
//!   reaching the arm. An empty box with no reported stop proves no integer input reaches it.
//! - **What reaches it?** `witness` searches boxes growing out from zero for one input that
//!   meets the condition. The function is then run on that input to give a test row.
//!
//! A witness is confirmed independently of the path conditions: the arm is replaced in the
//! kernel term by a sentinel atom, the function is run on the witness by the reference
//! evaluator, and the sentinel must come back. A dead arm is confirmed by enumeration over a
//! small box, which can refute the solver but cannot prove it.
//!
//! Usage: zed-testgen <file.zed> [--knockout]
//!   --knockout  builds every `else` guard without its negation, to show the checks catch it.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zedc::ast::unit;
use zedc::check::check;
use zedc::elab::{Unit, elaborate};
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve;
use zedc::store::interval::IntervalSet;
use zedc::store::preimage::{Demand, Domains, Point, Stop, preimage, witness};

/// The boxes searched for a witness, smallest first, so a test row uses small inputs.
const SEARCH: [(i64, i64); 6] = [
    (0, 10),
    (-10, 10),
    (0, 1000),
    (-1000, 1000),
    (0, 1_000_000),
    (-1_000_000, 1_000_000),
];

/// The half-width of the box a dead arm is enumerated over, per input count.
fn enumeration_radius(inputs: usize) -> Option<i64> {
    match inputs {
        1 => Some(2000),
        2 => Some(60),
        3 => Some(12),
        _ => None,
    }
}

const SENTINEL: &str = "testgenArmReached";

/// One guard on the way to an arm: the `if`'s condition, under the lets around it, and
/// which way it went.
#[derive(Clone)]
struct Guard {
    cond: Term,
    holds: bool,
}

/// An arm of an `if`: the guards that reach it, and its place in the body as child indexes.
struct Arm {
    guards: Vec<Guard>,
    route: Vec<usize>,
}

/// What enumerating a small box says about an arm the solver calls dead.
enum Enumeration {
    /// No point of the box of this half-width reaches the arm.
    Agrees(i64),
    /// This point reaches the arm: the solver is wrong.
    Refutes(Vec<i64>),
    /// Too many inputs to enumerate.
    Skipped,
}

/// What the solver and the checks found for one arm.
enum Finding {
    Reached { point: Point, value: String, confirmed: bool },
    Dead { enumeration: Enumeration },
    NoneInBox { stops: Vec<Stop> },
    Undecided { stops: Vec<Stop> },
}

fn wrap(lets: &[(Arc<str>, Term)], t: &Term) -> Term {
    lets.iter().rev().fold(t.clone(), |body, (x, v)| {
        Term::Let(x.clone(), Arc::new(v.clone()), Arc::new(body))
    })
}

/// Every arm of every `if` reachable in `t` without entering a lambda. Child indexes: `If`
/// 0 condition, 1 then, 2 else; `Let` 0 value, 1 body; `Prim` its arguments; `App` 0 the
/// function, then its arguments from 1.
fn walk(
    t: &Term,
    route: &mut Vec<usize>,
    lets: &mut Vec<(Arc<str>, Term)>,
    guards: &mut Vec<Guard>,
    arms: &mut Vec<Arm>,
) {
    match t {
        Term::If(c, a, b) => {
            let cond = wrap(lets, c);
            for (i, branch, holds) in [(1, a, true), (2, b, false)] {
                guards.push(Guard { cond: cond.clone(), holds });
                route.push(i);
                arms.push(Arm { guards: guards.clone(), route: route.clone() });
                walk(branch, route, lets, guards, arms);
                route.pop();
                guards.pop();
            }
        }
        Term::Let(x, v, body) => {
            route.push(0);
            walk(v, route, lets, guards, arms);
            route.pop();
            lets.push((x.clone(), (**v).clone()));
            route.push(1);
            walk(body, route, lets, guards, arms);
            route.pop();
            lets.pop();
        }
        Term::Prim(_, args) => {
            for (i, a) in args.iter().enumerate() {
                route.push(i);
                walk(a, route, lets, guards, arms);
                route.pop();
            }
        }
        Term::App(f, args) => {
            route.push(0);
            walk(f, route, lets, guards, arms);
            route.pop();
            for (i, a) in args.iter().enumerate() {
                route.push(i + 1);
                walk(a, route, lets, guards, arms);
                route.pop();
            }
        }
        _ => {}
    }
}

/// `t` with the subterm at `route` replaced by `by`.
fn replace(t: &Term, route: &[usize], by: &Term) -> Term {
    let Some((&i, rest)) = route.split_first() else {
        return by.clone();
    };
    let at = |s: &Term| Arc::new(replace(s, rest, by));
    match (t, i) {
        (Term::If(c, a, b), 0) => Term::If(at(c), a.clone(), b.clone()),
        (Term::If(c, a, b), 1) => Term::If(c.clone(), at(a), b.clone()),
        (Term::If(c, a, b), 2) => Term::If(c.clone(), a.clone(), at(b)),
        (Term::Let(x, v, body), 0) => Term::Let(x.clone(), at(v), body.clone()),
        (Term::Let(x, v, body), 1) => Term::Let(x.clone(), v.clone(), at(body)),
        (Term::Prim(p, args), i) => {
            let mut args = args.clone();
            args[i] = replace(&args[i], rest, by);
            Term::Prim(*p, args)
        }
        (Term::App(f, args), 0) => Term::App(at(f), args.clone()),
        (Term::App(f, args), i) => {
            let mut args = args.clone();
            args[i - 1] = replace(&args[i - 1], rest, by);
            Term::App(f.clone(), args)
        }
        _ => unreachable!("a route only names children `walk` entered"),
    }
}

/// The path condition of `arm`: its guards in order, each negated where it went to `else`.
/// With `knockout`, an `else` guard is left unnegated, a deliberate defect.
fn condition(arm: &Arm, knockout: bool) -> Term {
    arm.guards
        .iter()
        .map(|g| {
            if g.holds || knockout {
                g.cond.clone()
            } else {
                Term::Prim(Prim::Not, vec![g.cond.clone()])
            }
        })
        .reduce(|acc, g| Term::Prim(Prim::And, vec![acc, g]))
        .expect("an arm has at least one guard")
}

fn domains(params: &[Arc<str>], lo: i64, hi: i64) -> Domains {
    params
        .iter()
        .map(|p| (p.clone(), IntervalSet::of(lo, hi)))
        .collect()
}

fn run(t: &Term) -> Result<Value, String> {
    Evaluator::new(World::new())
        .run(&zedc::interp::prelude(t.clone()))
        .map_err(|e| e.to_string())
}

/// `f(args)`, where `f` is `fun` closed over the unit.
fn call(unit: &Unit, fun: &Term, args: &[i64]) -> Result<Value, String> {
    let lits = args.iter().map(|n| Term::Lit(Value::Int(*n))).collect();
    run(&unit.close(Term::App(Arc::new(fun.clone()), lits)))
}

/// Whether the arm runs on `args`: the arm is replaced by a sentinel atom, which no other
/// code can produce, and the sentinel must appear in the result, alone or merged with other
/// failures into `#errs`. One-sided: a later `else` that strips the atom gives a false
/// "no", never a false "yes".
fn reaches(unit: &Unit, params: &[Arc<str>], body: &Term, arm: &Arm, args: &[i64]) -> bool {
    let marked = replace(body, &arm.route, &Term::Lit(Value::atom(SENTINEL)));
    let fun = Term::Lam(params.to_vec(), Arc::new(marked));
    matches!(call(unit, &fun, args), Ok(v) if v.to_string().contains(&format!("#{SENTINEL}")))
}

/// Every point of the box of half-width `r` around zero, in order.
fn points(n: usize, r: i64) -> Vec<Vec<i64>> {
    (0..n).fold(vec![vec![]], |acc, _| {
        acc.into_iter()
            .flat_map(|p| {
                (-r..=r).map(move |v| {
                    let mut q = p.clone();
                    q.push(v);
                    q
                })
            })
            .collect()
    })
}

fn examine(unit: &Unit, kernel: &Arc<str>, params: &[Arc<str>], body: &Term, arm: &Arm, knockout: bool) -> Finding {
    let cond = unit.close(condition(arm, knockout));
    let all: Domains = params.iter().map(|p| (p.clone(), IntervalSet::top())).collect();
    let pre = preimage(&cond, &all, &Demand::Bool(true));
    if pre.stops.is_empty() && pre.domains.values().any(IntervalSet::is_empty) {
        let enumeration = match enumeration_radius(params.len()) {
            None => Enumeration::Skipped,
            Some(r) => match points(params.len(), r)
                .into_iter()
                .find(|p| reaches(unit, params, body, arm, p))
            {
                Some(p) => Enumeration::Refutes(p),
                None => Enumeration::Agrees(r),
            },
        };
        return Finding::Dead { enumeration };
    }
    let mut decided_none = false;
    for (lo, hi) in SEARCH {
        match witness(&cond, &domains(params, lo, hi), &BTreeMap::new(), &Demand::Bool(true)) {
            Some(Some(point)) => {
                let args: Vec<i64> = params.iter().map(|p| point[p]).collect();
                let value = match call(unit, &Term::Var(kernel.clone()), &args) {
                    Ok(v) => v.to_string(),
                    Err(e) => format!("<error: {e}>"),
                };
                let confirmed = reaches(unit, params, body, arm, &args);
                return Finding::Reached { point, value, confirmed };
            }
            Some(None) => decided_none = true,
            None => {}
        }
    }
    if decided_none {
        Finding::NoneInBox { stops: pre.stops }
    } else {
        Finding::Undecided { stops: pre.stops }
    }
}

fn describe(arm: &Arm) -> String {
    arm.guards
        .iter()
        .map(|g| {
            let c = innermost(&g.cond).to_string();
            if g.holds { c } else { format!("not ({c})") }
        })
        .collect::<Vec<_>>()
        .join("  and  ")
}

/// The condition itself, under the lets `wrap` put around it.
fn innermost(t: &Term) -> &Term {
    match t {
        Term::Let(_, _, body) => innermost(body),
        _ => t,
    }
}

/// The parameter types of a printed signature `(int, int) -> …`, when it has that shape.
fn int_params(sig: &str) -> bool {
    let Some(inner) = sig.strip_prefix('(').and_then(|s| s.split(") -> ").next()) else {
        return false;
    };
    !inner.is_empty() && inner.split(", ").all(|p| p == "int")
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let knockout = args.iter().any(|a| a == "--knockout");
    let path = args.iter().find(|a| !a.starts_with("--")).expect("usage: zed-testgen <file.zed> [--knockout]");
    let text = std::fs::read_to_string(path).expect("read the file");
    let tokens = lex_fence(&text).expect("lex");
    let tree = parse(&text, &tokens, "Unit", TOP).expect("parse");
    let stmts = unit(&text, &tokens, &tree).expect("unit");
    let res = resolve(&stmts).expect("resolve");
    let info = check(&stmts, &res);
    if !info.errors.is_empty() {
        for e in &info.errors {
            eprintln!("type error: {}", e.message);
        }
        std::process::exit(1);
    }
    let unit = elaborate(&stmts, &res).unwrap_or_else(|es| {
        for e in es {
            eprintln!("elaboration error: {}", e.message);
        }
        std::process::exit(1)
    });
    let sigs: BTreeMap<String, String> = info
        .sigs
        .iter()
        .map(|(id, s)| (res.binders[*id].name.clone(), s.to_string()))
        .collect();

    let (mut total, mut reached, mut dead, mut unconfirmed, mut refuted) = (0, 0, 0, 0, 0);
    for def in &unit.defs {
        let Term::Lam(params, body) = &def.term else { continue };
        let Some(sig) = sigs.get(&def.name) else { continue };
        if !int_params(sig) {
            println!("{}  {sig}\n  skipped: only functions of integer parameters are analysed\n", def.name);
            continue;
        }
        let mut arms = Vec::new();
        walk(body, &mut Vec::new(), &mut Vec::new(), &mut Vec::new(), &mut arms);
        println!("{}  {sig}  ({} arms)", def.name, arms.len());
        let mut rows = Vec::new();
        for arm in &arms {
            total += 1;
            let finding = examine(&unit, &def.kernel, params, body, arm, knockout);
            let what = match &finding {
                Finding::Reached { point, value, confirmed } => {
                    reached += 1;
                    if !confirmed {
                        unconfirmed += 1;
                    }
                    let args: Vec<String> = params.iter().map(|p| point[p].to_string()).collect();
                    let key = if args.len() == 1 { args[0].clone() } else { format!("({})", args.join(", ")) };
                    let row = format!("{key} -> {value}");
                    if !rows.contains(&row) {
                        rows.push(row);
                    }
                    let mark = if *confirmed { "confirmed" } else { "NOT CONFIRMED: the sentinel did not come back" };
                    format!("reached by {} -> {value}   [{mark}]", key)
                }
                Finding::Dead { enumeration } => {
                    dead += 1;
                    match enumeration {
                        Enumeration::Agrees(r) => format!("DEAD for every integer input   [no input in ±{r} reaches it]"),
                        Enumeration::Skipped => "DEAD for every integer input   [too many inputs to enumerate]".into(),
                        Enumeration::Refutes(p) => {
                            refuted += 1;
                            format!("called DEAD, but REFUTED: {:?} reaches it", p)
                        }
                    }
                }
                Finding::NoneInBox { stops } => {
                    let s: Vec<String> = stops.iter().map(ToString::to_string).collect();
                    format!("no input within ±1000000 reaches it (not proved for all integers){}", if s.is_empty() { String::new() } else { format!("; stops: {}", s.join("; ")) })
                }
                Finding::Undecided { stops } => {
                    let s: Vec<String> = stops.iter().map(ToString::to_string).collect();
                    format!("undecided{}", if s.is_empty() { String::new() } else { format!(": {}", s.join("; ")) })
                }
            };
            println!("  when  {}\n        {what}", describe(arm));
        }
        if !rows.is_empty() {
            println!("  generated:  test {{ {} }}", rows.join(", "));
        }
        println!();
    }
    println!(
        "{total} arms: {reached} reached, {dead} dead, {} other; {unconfirmed} witnesses not confirmed, {refuted} dead claims refuted",
        total - reached - dead
    );
    if unconfirmed > 0 || refuted > 0 {
        std::process::exit(2);
    }
}
