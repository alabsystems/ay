// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MILP FAST-PATH for the SMT2 lane (#milp-fastpath).
//!
//! the downstream optimization consumer's `mip-diff` subprocess oracle pipes big-M MILP feasibility scripts into
//! `ay -in`: `(set-logic QF_LRA)`, one `declare-const … Real` per column,
//! binaries as `(assert (or (= c 0.0) (= c 1.0)))`, bounds and rows as linear
//! `<=`/`>=`/`=` assertions over exact dyadic literals, then `(check-sat)` +
//! `(get-value (c0 … cN))`. The generic DPLL(T)+LRA lane treats each binary as
//! a case split with no bounding, no cuts and no incumbents — on the cifar100
//! w2 window (6,277 columns / 4,245 rows / 16 binaries) it produces NO verdict
//! at 300s, while `ay-milp`'s branch-and-cut solves the same window to proven
//! optimality in ~200s. This module recognises exactly that shape and routes
//! it to [`ay_milp::BabSession`].
//!
//! SOUNDNESS CONTRACT. The routing is FAIL-CLOSED at every step:
//! - The script must parse COMPLETELY into the recognised fragment — any
//!   unrecognised command, non-linear term, strict inequality, or numeric
//!   literal that is not EXACTLY representable as the `f64` the model stores
//!   (ay-milp's models denote exact dyadic rationals) makes this function
//!   decline, and the standard lane handles the input unchanged.
//! - The verdict map inherits ay-milp's own contract: `sat` only from an
//!   exactly `check_point`-verified feasible point, `unsat` only from a
//!   complete search whose every leaf was settled on the exact rim, anything
//!   the budget cut short is `unknown` — never a guess.
//! - At least one 0/1 disjunction is required: a purely conjunctive QF_LRA
//!   script is ordinary LP feasibility, which the LRA lane already decides
//!   efficiently and exactly — routing those would change competition
//!   behavior for no need.
//!
//! `AY_MILP_FASTPATH=0` disables the route entirely.

use ay_frontend::{Command, CommandStream, CommandStreamItem, Constant, Term};
use ay_milp::{BabSession, Model, Outcome, SolveOpts};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Signed;
use std::collections::HashMap;
use std::io::Write;
use std::time::Duration;

/// Mirror of the executor's per-`check-sat` safety net: when the caller passed
/// no `-t`, the fast-path solve still self-limits rather than running forever
/// (the downstream optimization consumer's harness kills the process from outside and would otherwise see the
/// runaway the 2026-07-15 status doc complained about).
const DEFAULT_NET_SECS: u64 = 300;

/// One parsed linear constraint: `lb <= Σ coeff·var <= ub` over column indices.
struct RowCon {
    coeffs: Vec<(u32, f64)>,
    lb: f64,
    ub: f64,
}

struct Script {
    /// Column names in declaration order.
    vars: Vec<String>,
    /// Which columns carry a 0/1 disjunction.
    binary: Vec<bool>,
    /// Per-column bound intersection accumulated from single-variable asserts.
    lo: Vec<f64>,
    up: Vec<f64>,
    rows: Vec<RowCon>,
    /// `(assert false)` seen: the conjunction is trivially unsat.
    trivially_unsat: bool,
    /// The `(get-value …)` request, if any: original key text per column index.
    get_value: Option<Vec<(String, u32)>>,
}

/// Try the fast path. `true` means the script was recognised, solved and ALL
/// output printed; `false` means "not ours" and the caller must proceed with
/// the standard lane as if this was never called.
pub(crate) fn try_milp_fastpath(content: &str) -> bool {
    let debug = std::env::var_os("AY_MILP_FASTPATH_DEBUG").is_some();
    if debug {
        eprintln!("fastpath: entry ({} bytes)", content.len());
    }
    if std::env::var("AY_MILP_FASTPATH").as_deref() == Ok("0") {
        return false;
    }
    // Cheap pre-screen before any real parsing.
    if !content.contains("QF_LRA") || !content.contains("check-sat") {
        return false;
    }
    let Some(script) = parse_script(content) else {
        if debug {
            eprintln!("fastpath: parse declined");
        }
        return false;
    };
    // Require a genuine MILP: at least one 0/1 disjunction (see module doc).
    if !script.binary.iter().any(|&b| b) {
        return false;
    }
    solve_and_print(&script);
    true
}

fn parse_script(content: &str) -> Option<Script> {
    let mut vars: Vec<String> = Vec::new();
    let mut index: HashMap<String, u32> = HashMap::new();
    let mut binary: Vec<bool> = Vec::new();
    let mut lo: Vec<f64> = Vec::new();
    let mut up: Vec<f64> = Vec::new();
    let mut rows: Vec<RowCon> = Vec::new();
    let mut trivially_unsat = false;
    let mut saw_logic = false;
    let mut saw_check_sat = false;
    let mut get_value: Option<Vec<(String, u32)>> = None;

    let mut stream = CommandStream::new(content);
    loop {
        let item = match stream.next_command() {
            Some(i) => i,
            None => break,
        };
        let cmd = match item {
            CommandStreamItem::Command(c) => *c,
            // A parse error means the standard lane's `(error …)` recovery
            // behavior must be preserved — not ours.
            _ => return None,
        };
        match cmd {
            Command::SetLogic(l) => {
                if l != "QF_LRA" {
                    return None;
                }
                saw_logic = true;
            }
            // Informational; the standard lane ignores these for solving too.
            Command::SetInfo(..) => {}
            Command::DeclareConst(name, sort) => {
                if !sort_is_real(&sort) || index.contains_key(&name) {
                    return None;
                }
                index.insert(name.clone(), vars.len() as u32);
                vars.push(name);
                binary.push(false);
                lo.push(f64::NEG_INFINITY);
                up.push(f64::INFINITY);
            }
            Command::DeclareFun(name, args, sort) => {
                // A nullary Real function is a constant; anything else is not ours.
                if !args.is_empty() || !sort_is_real(&sort) || index.contains_key(&name) {
                    return None;
                }
                index.insert(name.clone(), vars.len() as u32);
                vars.push(name);
                binary.push(false);
                lo.push(f64::NEG_INFINITY);
                up.push(f64::INFINITY);
            }
            Command::Assert(term) => {
                if saw_check_sat {
                    return None; // incremental use: not ours
                }
                let Some(cls) = classify_assert(&term, &index) else {
                    if std::env::var_os("AY_MILP_FASTPATH_DEBUG").is_some() {
                        eprintln!("fastpath decline on assert: {term:?}");
                    }
                    return None;
                };
                match cls {
                    Classified::Binary(j) => binary[j as usize] = true,
                    Classified::Bound(j, l, u) => {
                        let j = j as usize;
                        lo[j] = lo[j].max(l);
                        up[j] = up[j].min(u);
                    }
                    Classified::Row(r) => rows.push(r),
                    Classified::False => trivially_unsat = true,
                    Classified::True => {}
                }
            }
            Command::CheckSat => {
                if saw_check_sat || !saw_logic {
                    return None; // exactly one check-sat, after set-logic
                }
                saw_check_sat = true;
            }
            Command::GetValue(pairs) => {
                if !saw_check_sat || get_value.is_some() {
                    return None;
                }
                let mut req = Vec::with_capacity(pairs.len());
                for (text, term) in pairs {
                    let Term::Symbol(name) = &term else {
                        return None;
                    };
                    let j = *index.get(name)?;
                    req.push((text, j));
                }
                get_value = Some(req);
            }
            Command::Exit => break,
            // Anything else (push/pop, define-fun, options, optimization…):
            // not the shape this path serves.
            other => {
                if std::env::var_os("AY_MILP_FASTPATH_DEBUG").is_some() {
                    eprintln!("fastpath decline on command: {other:?}");
                }
                return None;
            }
        }
    }
    if !saw_check_sat {
        return None;
    }
    Some(Script {
        vars,
        binary,
        lo,
        up,
        rows,
        trivially_unsat,
        get_value,
    })
}

fn sort_is_real(sort: &ay_frontend::Sort) -> bool {
    matches!(sort, ay_frontend::Sort::Simple(s) if s == "Real")
}

enum Classified {
    Binary(u32),
    Bound(u32, f64, f64),
    Row(RowCon),
    False,
    True,
}

fn classify_assert(term: &Term, index: &HashMap<String, u32>) -> Option<Classified> {
    match term {
        Term::Const(Constant::False) => Some(Classified::False),
        Term::Const(Constant::True) => Some(Classified::True),
        Term::App(op, args) if op == "or" => {
            // Exactly the binary disjunction `(or (= v 0) (= v 1))`.
            if args.len() != 2 {
                return None;
            }
            let (v0, c0) = eq_var_lit(&args[0], index)?;
            let (v1, c1) = eq_var_lit(&args[1], index)?;
            if v0 != v1 {
                return None;
            }
            let (a, b) = (c0.min(c1), c0.max(c1));
            if a == 0.0 && b == 1.0 {
                Some(Classified::Binary(v0))
            } else {
                None
            }
        }
        Term::App(op, args) if matches!(op.as_str(), "<=" | ">=" | "=") && args.len() == 2 => {
            // Linear comparison: sum on the left, literal on the right — or a
            // bare variable on the left (the downstream optimization consumer's bound shape).
            let rhs = lit_f64(&args[1])?;
            if let Term::Symbol(name) = &args[0] {
                let j = *index.get(name)?;
                return Some(match op.as_str() {
                    "<=" => Classified::Bound(j, f64::NEG_INFINITY, rhs),
                    ">=" => Classified::Bound(j, rhs, f64::INFINITY),
                    _ => Classified::Bound(j, rhs, rhs),
                });
            }
            let coeffs = linear_sum(&args[0], index)?;
            let (lb, ub) = match op.as_str() {
                "<=" => (f64::NEG_INFINITY, rhs),
                ">=" => (rhs, f64::INFINITY),
                _ => (rhs, rhs),
            };
            Some(Classified::Row(RowCon { coeffs, lb, ub }))
        }
        _ => None,
    }
}

/// `(= v LIT)` in either order → (column, literal).
fn eq_var_lit(term: &Term, index: &HashMap<String, u32>) -> Option<(u32, f64)> {
    let Term::App(op, args) = term else {
        return None;
    };
    if op != "=" || args.len() != 2 {
        return None;
    }
    match (&args[0], &args[1]) {
        (Term::Symbol(v), lit) => Some((*index.get(v)?, lit_f64(lit)?)),
        (lit, Term::Symbol(v)) => Some((*index.get(v)?, lit_f64(lit)?)),
        _ => None,
    }
}

/// `(+ term …)` | single term, each term `(* LIT var)` or a bare `var`.
fn linear_sum(term: &Term, index: &HashMap<String, u32>) -> Option<Vec<(u32, f64)>> {
    let terms: &[Term] = match term {
        Term::App(op, args) if op == "+" => args,
        other => std::slice::from_ref(other),
    };
    let mut out = Vec::with_capacity(terms.len());
    for t in terms {
        match t {
            Term::Symbol(v) => out.push((*index.get(v)?, 1.0)),
            Term::App(op, args) if op == "*" && args.len() == 2 => {
                let (coef, var) = match (&args[0], &args[1]) {
                    (c, Term::Symbol(v)) => (lit_f64(c)?, v),
                    (Term::Symbol(v), c) => (lit_f64(c)?, v),
                    _ => return None,
                };
                out.push((*index.get(var)?, coef));
            }
            _ => return None,
        }
    }
    Some(out)
}

/// Parse a numeric literal into the EXACT `f64` it denotes, or decline.
///
/// The recognised forms are the ones the downstream optimization consumer's `real_literal` emits — integers
/// (`123`, `123.0`, negatives via unary `-`) and dyadic fractions
/// `(/ mant.0 2^k.0)`. Exactness is enforced, never assumed: the integer path
/// requires magnitude ≤ 2^53, and the division result is verified by
/// re-multiplication (exact for power-of-two denominators, so a rounded
/// quotient cannot pass).
fn lit_f64(term: &Term) -> Option<f64> {
    match term {
        Term::Const(Constant::Numeral(s)) => int_str_f64(s),
        Term::Const(Constant::Decimal(s)) => dec_str_f64(s),
        Term::App(op, args) if op == "-" && args.len() == 1 => Some(-lit_f64(&args[0])?),
        Term::App(op, args) if op == "/" && args.len() == 2 => {
            let a = lit_f64(&args[0])?;
            let b = lit_f64(&args[1])?;
            // Only power-of-two denominators (the dialect's shape): division by
            // 2^k is a pure exponent shift, so with the re-multiplication check
            // below the quotient is provably exact. A non-power-of-two divisor
            // could round in BOTH the divide and the verify multiply and pass by
            // coincidence (1/3 does), so it is declined outright.
            // `!(b > 0.0)` is deliberate: it also rejects NaN, which `b <= 0.0` would pass.
            #[allow(clippy::neg_cmp_op_on_partial_ord)]
            if !(b > 0.0) || b.fract() != 0.0 || !(b as u128).is_power_of_two() {
                return None;
            }
            let r = a / b;
            (r.is_finite() && r * b == a).then_some(r)
        }
        _ => None,
    }
}

fn int_str_f64(s: &str) -> Option<f64> {
    let v: i128 = s.parse().ok()?;
    // Exactness by ROUNDTRIP, not a magnitude cap: `v as f64` rounds to the
    // nearest float, and casting that back is exact for integral floats — so
    // the pair agrees iff `v` is exactly representable. This admits the
    // dialect's large power-of-two denominators (2^55 and up), which a naive
    // ≤2^53 cap wrongly declined (that miss sent the real w2 script down the
    // generic lane).
    let f = v as f64;
    (f.is_finite() && f as i128 == v).then_some(f)
}

fn dec_str_f64(s: &str) -> Option<f64> {
    let (int, frac) = s.split_once('.')?;
    if !frac.bytes().all(|b| b == b'0') {
        return None; // fractional decimals are not in the dialect; decline
    }
    int_str_f64(int)
}

fn solve_and_print(script: &Script) {
    let verdict = if script.trivially_unsat {
        Verdict::Unsat
    } else {
        solve(script)
    };
    match &verdict {
        Verdict::Sat(_) => print_verdict("sat"),
        Verdict::Unsat => print_verdict("unsat"),
        Verdict::Unknown(reason) => {
            print_verdict("unknown");
            let _ = writeln!(std::io::stderr(), "(:reason-unknown \"{reason}\")");
        }
    }
    if let Some(req) = &script.get_value {
        match &verdict {
            Verdict::Sat(values) => {
                let mut pairs = Vec::with_capacity(req.len());
                for (text, j) in req {
                    pairs.push(format!("({text} {})", smt_real(&values[*j as usize])));
                }
                println!("({})", pairs.join(" "));
            }
            // SMT-LIB: a model query without a sat answer has no model.
            _ => println!("(error \"model is not available\")"),
        }
    }
    let _ = std::io::stdout().flush();
}

enum Verdict {
    Sat(Vec<BigRational>),
    Unsat,
    Unknown(&'static str),
}

fn solve(script: &Script) -> Verdict {
    let mut model = Model::new();
    let mut cols = Vec::with_capacity(script.vars.len());
    for j in 0..script.vars.len() {
        let (l, u) = (script.lo[j], script.up[j]);
        if l > u {
            return Verdict::Unsat; // an empty box is an exact contradiction
        }
        let col = if script.binary[j] {
            let c = model.add_binary_col();
            // Extra bounds on a binary (the downstream optimization consumer's pinned `(= c 0.0)` form) ride as a
            // single-variable row: `set_col_bounds` is crate-internal and a row
            // is semantically identical.
            if l > f64::NEG_INFINITY || u < f64::INFINITY {
                model.add_row(l, u, &[(c, 1.0)]);
            }
            c
        } else {
            model.add_col(l, u)
        };
        cols.push(col);
    }
    for row in &script.rows {
        let coeffs: Vec<_> = row
            .coeffs
            .iter()
            .map(|&(j, a)| (cols[j as usize], a))
            .collect();
        model.add_row(row.lb, row.ub, &coeffs);
    }

    // Budget: the remaining share of `-t` when one was given, else the same
    // per-check safety net the executor lane applies.
    let remaining = remaining_budget().unwrap_or(Duration::from_secs(DEFAULT_NET_SECS));
    let opts = SolveOpts::new().with_time_limit(remaining);
    let mut session = match BabSession::new(model.clone(), &opts) {
        Ok(s) => s,
        Err(_) => return Verdict::Unknown("incomplete"),
    };
    match session.check() {
        Ok(Outcome::Optimal { model_values, .. }) | Ok(Outcome::Feasible { model_values, .. }) => {
            Verdict::Sat(model_values)
        }
        Ok(Outcome::Infeasible { .. }) => Verdict::Unsat,
        Ok(_) | Err(_) => Verdict::Unknown("timeout"),
    }
}

/// What is left of the global `-t` budget, if one was set.
fn remaining_budget() -> Option<Duration> {
    let ms = crate::GLOBAL_TIMEOUT_MS.load(std::sync::atomic::Ordering::SeqCst);
    if ms == 0 {
        return None;
    }
    let start = crate::START_TIME.get()?;
    let total = Duration::from_millis(ms);
    Some(
        total
            .saturating_sub(start.elapsed())
            .max(Duration::from_millis(1)),
    )
}

fn print_verdict(v: &str) {
    println!("{v}");
    crate::mark_verdict_printed();
}

/// Render an exact rational in the grammar the consumers parse:
/// `N.0`, `(- N.0)`, `(/ P.0 Q.0)`, `(- (/ P.0 Q.0))`.
fn smt_real(v: &BigRational) -> String {
    let neg = v.is_negative();
    let a = if neg { -v.clone() } else { v.clone() };
    let core = if a.denom() == &BigInt::from(1) {
        format!("{}.0", a.numer())
    } else {
        format!("(/ {}.0 {}.0)", a.numer(), a.denom())
    };
    if neg {
        format!("(- {core})")
    } else {
        core
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Debug probe: `FP_DEBUG_FILE=/path cargo test … debug_real_file -- --nocapture`
    /// parses a real script and reports where the fast path declines.
    #[test]
    fn debug_real_file() {
        let Ok(path) = std::env::var("FP_DEBUG_FILE") else {
            return;
        };
        let content = std::fs::read_to_string(path).expect("readable");
        let s = parse_script(&content);
        eprintln!(
            "parse_script => {}",
            if s.is_some() {
                "RECOGNISED"
            } else {
                "DECLINED"
            }
        );
        if let Some(s) = &s {
            eprintln!(
                "vars={} binaries={} rows={}",
                s.vars.len(),
                s.binary.iter().filter(|&&b| b).count(),
                s.rows.len()
            );
        }
    }

    fn run(content: &str) -> Option<Script> {
        parse_script(content)
    }

    #[test]
    fn parses_ny_shape() {
        let s = run(r#"
(set-logic QF_LRA)
(declare-const c0 Real)
(declare-const c1 Real)
(declare-const c2 Real)
(assert (>= c0 (/ 1.0 4.0)))
(assert (<= c0 (/ 3.0 4.0)))
(assert (or (= c1 0.0) (= c1 1.0)))
(assert (<= (+ (* 2.0 c0) (* (- 1.0) c1) (* 1.0 c2)) 5.0))
(assert (= (+ (* 1.0 c2) (* (- (/ 1.0 2.0)) c0)) 0.0))
(check-sat)
(get-value (c0 c1 c2))
"#)
        .expect("recognised");
        assert_eq!(s.vars.len(), 3);
        assert!(s.binary[1] && !s.binary[0] && !s.binary[2]);
        assert_eq!(s.lo[0], 0.25);
        assert_eq!(s.up[0], 0.75);
        assert_eq!(s.rows.len(), 2);
        assert_eq!(s.get_value.as_ref().unwrap().len(), 3);
    }

    #[test]
    fn declines_out_of_fragment() {
        // Strict inequality: not representable, must decline.
        assert!(
            run("(set-logic QF_LRA)(declare-const x Real)(assert (< x 1.0))(check-sat)").is_none()
        );
        // Non-linear product.
        assert!(run(
            "(set-logic QF_LRA)(declare-const x Real)(assert (<= (* x x) 1.0))(check-sat)"
        )
        .is_none());
        // Wrong logic.
        assert!(
            run("(set-logic QF_LIA)(declare-const x Int)(assert (<= x 1))(check-sat)").is_none()
        );
        // push/pop incremental.
        assert!(run(
            "(set-logic QF_LRA)(declare-const x Real)(push 1)(assert (<= x 1.0))(check-sat)"
        )
        .is_none());
        // Inexact decimal literal.
        assert!(
            run("(set-logic QF_LRA)(declare-const x Real)(assert (<= x 0.1))(check-sat)").is_none()
        );
        // Non-0/1 disjunction.
        let s = run(
            "(set-logic QF_LRA)(declare-const x Real)(assert (or (= x 0.0) (= x 2.0)))(check-sat)",
        );
        assert!(s.is_none());
    }

    #[test]
    fn exact_literals() {
        // (/ 3.0 4.0) is exactly 0.75.
        assert_eq!(
            lit_f64(&Term::App("/".into(), vec![dec("3.0"), dec("4.0")])),
            Some(0.75)
        );
        // A non-dyadic quotient that is not exactly representable declines.
        assert_eq!(
            lit_f64(&Term::App("/".into(), vec![dec("1.0"), dec("3.0")])),
            None
        );
        // A non-representable integer declines (2^54 + 1)…
        assert_eq!(int_str_f64("18014398509481985"), None);
        // …but an exactly-representable large power of two passes (2^55).
        assert_eq!(int_str_f64("36028797018963968"), Some(36028797018963968.0));
        // Negation nests.
        assert_eq!(
            lit_f64(&Term::App(
                "-".into(),
                vec![Term::App("/".into(), vec![dec("1.0"), dec("2.0")])]
            )),
            Some(-0.5)
        );
    }

    fn dec(s: &str) -> Term {
        Term::Const(Constant::Decimal(s.into()))
    }

    #[test]
    fn smt_real_grammar() {
        use num_bigint::BigInt;
        let r = |n: i64, d: i64| BigRational::new(BigInt::from(n), BigInt::from(d));
        assert_eq!(smt_real(&r(5, 1)), "5.0");
        assert_eq!(smt_real(&r(-5, 1)), "(- 5.0)");
        assert_eq!(smt_real(&r(1, 2)), "(/ 1.0 2.0)");
        assert_eq!(smt_real(&r(-1, 2)), "(- (/ 1.0 2.0))");
    }
}
