// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential fuzzer for single-shot QF_LIA soundness (seed-236 family).
//!
//! Found by differential fuzzing during the push/pop clause-leak work: a
//! single-shot (non-incremental) QF_LIA solve returned a false UNSAT on a
//! 6-assertion Bool+Int script, while the incremental (push/pop) path and z3
//! both answered SAT. Root cause: the LIA Diophantine joint case split built
//! conflict clauses that omitted the bound reason literals (`a*x OP c` atoms
//! and LRA tableau bounds), learning a theory-invalid clause.
//!
//! This fuzzer generates random instances from the same family (3 Int vars,
//! 3 Bool vars, ~6 assertions mixing Bool structure with small-coefficient
//! linear atoms, including duplicate-monomial sums) and checks:
//!
//! 1. single-shot verdict == push/pop incremental verdict;
//! 2. every UNSAT verdict is refuted-or-confirmed by an independent
//!    brute-force witness search over a small integer box (a witness in the
//!    box proves SAT, so any `unsat` answer is a definite soundness bug);
//! 3. (heavy run only) agreement with a z3 binary when one is on PATH.
//!
//! The brute-force oracle is one-sided by design: it can prove SAT but never
//! UNSAT. That is exactly the direction that matters — a false UNSAT from the
//! single-shot pipeline confirms spurious k-induction/IC3 SAFE verdicts in
//! downstream model checkers.

use crate::Executor;
use ay_frontend::parse;
use std::fmt::Write as _;

// --- Deterministic RNG (same scheme as pushpop_leak_fuzz.rs) ---

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(2685821657736338717).max(1))
    }
    fn next(&mut self) -> u64 {
        // xorshift64*
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(2685821657736338717)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.below((hi - lo + 1) as u64) as i64
    }
}

// --- Instance AST: printable to SMT-LIB and independently evaluable ---

const NUM_INT_VARS: usize = 3;
const NUM_BOOL_VARS: usize = 3;
/// Witness search box: every int var ranges over [-BOX, BOX].
const BOX: i64 = 6;

#[derive(Clone, Copy, PartialEq)]
enum CmpOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
}

impl CmpOp {
    fn smt(self) -> &'static str {
        match self {
            CmpOp::Lt => "<",
            CmpOp::Le => "<=",
            CmpOp::Gt => ">",
            CmpOp::Ge => ">=",
            CmpOp::Eq => "=",
        }
    }
    fn eval(self, lhs: i64, rhs: i64) -> bool {
        match self {
            CmpOp::Lt => lhs < rhs,
            CmpOp::Le => lhs <= rhs,
            CmpOp::Gt => lhs > rhs,
            CmpOp::Ge => lhs >= rhs,
            CmpOp::Eq => lhs == rhs,
        }
    }
}

/// Linear atom: `(op (+ (* c_i x_{v_i}) ...) k)`. Duplicate vars allowed,
/// mirroring the seed-236 repro (`(+ (* -2 x2) (* -3 x2))`).
struct Atom {
    op: CmpOp,
    terms: Vec<(i64, usize)>,
    constant: i64,
}

enum Form {
    BoolVar(usize),
    Atom(Atom),
    Not(Box<Form>),
    Or(Vec<Form>),
    And(Vec<Form>),
    Imp(Box<Form>, Box<Form>),
}

fn gen_atom(rng: &mut Rng) -> Atom {
    let op = match rng.below(5) {
        0 => CmpOp::Lt,
        1 => CmpOp::Le,
        2 => CmpOp::Gt,
        3 => CmpOp::Ge,
        _ => CmpOp::Eq,
    };
    let n_terms = 1 + rng.below(3) as usize;
    let mut terms = Vec::with_capacity(n_terms);
    for _ in 0..n_terms {
        let mut coeff = rng.range_i64(-3, 3);
        if coeff == 0 {
            coeff = 1;
        }
        terms.push((coeff, rng.below(NUM_INT_VARS as u64) as usize));
    }
    Atom {
        op,
        terms,
        constant: rng.range_i64(-5, 5),
    }
}

fn gen_form(rng: &mut Rng, depth: u32) -> Form {
    let leaf = |rng: &mut Rng| -> Form {
        if rng.below(2) == 0 {
            Form::Atom(gen_atom(rng))
        } else {
            let v = Form::BoolVar(rng.below(NUM_BOOL_VARS as u64) as usize);
            if rng.below(2) == 0 {
                Form::Not(Box::new(v))
            } else {
                v
            }
        }
    };
    if depth == 0 {
        return leaf(rng);
    }
    match rng.below(6) {
        0 => leaf(rng),
        1 => Form::Not(Box::new(gen_form(rng, depth - 1))),
        2 | 3 => {
            let n = 2 + rng.below(2) as usize;
            Form::Or((0..n).map(|_| gen_form(rng, depth - 1)).collect())
        }
        4 => Form::And((0..2).map(|_| gen_form(rng, depth - 1)).collect()),
        _ => Form::Imp(
            Box::new(gen_form(rng, depth - 1)),
            Box::new(gen_form(rng, depth - 1)),
        ),
    }
}

fn gen_instance(seed: u64) -> Vec<Form> {
    let mut rng = Rng::new(seed);
    let n_assertions = 4 + rng.below(4) as usize;
    (0..n_assertions).map(|_| gen_form(&mut rng, 2)).collect()
}

// --- SMT-LIB printing ---

fn print_atom(atom: &Atom, out: &mut String) {
    out.push('(');
    out.push_str(atom.op.smt());
    out.push(' ');
    if atom.terms.len() == 1 {
        let (c, v) = atom.terms[0];
        let _ = write!(out, "(* {c} x{v})");
    } else {
        out.push_str("(+");
        for &(c, v) in &atom.terms {
            let _ = write!(out, " (* {c} x{v})");
        }
        out.push(')');
    }
    let _ = write!(out, " {})", atom.constant);
}

fn print_form(form: &Form, out: &mut String) {
    match form {
        Form::BoolVar(v) => {
            let _ = write!(out, "b{v}");
        }
        Form::Atom(atom) => print_atom(atom, out),
        Form::Not(inner) => {
            out.push_str("(not ");
            print_form(inner, out);
            out.push(')');
        }
        Form::Or(children) => {
            out.push_str("(or");
            for child in children {
                out.push(' ');
                print_form(child, out);
            }
            out.push(')');
        }
        Form::And(children) => {
            out.push_str("(and");
            for child in children {
                out.push(' ');
                print_form(child, out);
            }
            out.push(')');
        }
        Form::Imp(lhs, rhs) => {
            out.push_str("(=> ");
            print_form(lhs, out);
            out.push(' ');
            print_form(rhs, out);
            out.push(')');
        }
    }
}

fn instance_script(assertions: &[Form], incremental: bool) -> String {
    let mut s = String::from("(set-logic QF_LIA)\n");
    for v in 0..NUM_INT_VARS {
        let _ = writeln!(s, "(declare-const x{v} Int)");
    }
    for v in 0..NUM_BOOL_VARS {
        let _ = writeln!(s, "(declare-const b{v} Bool)");
    }
    if incremental {
        s.push_str("(push 1)\n");
    }
    for form in assertions {
        s.push_str("(assert ");
        print_form(form, &mut s);
        s.push_str(")\n");
    }
    s.push_str("(check-sat)\n");
    if incremental {
        s.push_str("(pop 1)\n");
    }
    s
}

// --- Independent evaluation (brute-force witness oracle) ---

fn eval_form(form: &Form, ints: &[i64; NUM_INT_VARS], bools: &[bool; NUM_BOOL_VARS]) -> bool {
    match form {
        Form::BoolVar(v) => bools[*v],
        Form::Atom(atom) => {
            let lhs: i64 = atom.terms.iter().map(|&(c, v)| c * ints[v]).sum();
            atom.op.eval(lhs, atom.constant)
        }
        Form::Not(inner) => !eval_form(inner, ints, bools),
        Form::Or(children) => children.iter().any(|c| eval_form(c, ints, bools)),
        Form::And(children) => children.iter().all(|c| eval_form(c, ints, bools)),
        Form::Imp(lhs, rhs) => !eval_form(lhs, ints, bools) || eval_form(rhs, ints, bools),
    }
}

/// Search the box [-BOX, BOX]^3 x Bool^3 for a satisfying assignment.
/// `Some(witness)` proves the instance SAT; `None` proves nothing.
fn box_witness(assertions: &[Form]) -> Option<([i64; NUM_INT_VARS], [bool; NUM_BOOL_VARS])> {
    for x0 in -BOX..=BOX {
        for x1 in -BOX..=BOX {
            for x2 in -BOX..=BOX {
                let ints = [x0, x1, x2];
                for mask in 0..(1u32 << NUM_BOOL_VARS) {
                    let bools = [mask & 1 != 0, mask & 2 != 0, mask & 4 != 0];
                    if assertions.iter().all(|a| eval_form(a, &ints, &bools)) {
                        return Some((ints, bools));
                    }
                }
            }
        }
    }
    None
}

// --- Solver driving ---

fn solve_script(script: &str) -> String {
    let commands =
        parse(script).unwrap_or_else(|e| panic!("generated script failed to parse: {e}\n{script}"));
    let mut exec = Executor::new();
    // Per-solve timeout: virtually every instance in this family solves in
    // milliseconds; the guard exists because a few seeds hit a PRE-EXISTING
    // LIA nontermination (e.g. seed 2634: satisfiable per z3, but both the
    // fixed and the fce6a666fe baseline builds spin in LiaSolver::check_inner
    // indefinitely). Timeouts surface as "unknown" and are soft-skipped but
    // counted; the unknown-rate assertion in the callers catches systematic
    // degradation.
    exec.set_timeout(Some(std::time::Duration::from_secs(10)));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|e| panic!("executor error: {e}\n{script}"));
    outputs
        .iter()
        .rev()
        .find(|o| matches!(o.as_str(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_else(|| panic!("no verdict in outputs {outputs:?}\n{script}"))
}

struct FuzzStats {
    sat: usize,
    unsat: usize,
    unknown: usize,
}

/// Run an explicitly requested extended campaign.
///
/// The `qflia_differential_campaign` example is the non-test entry point; unit
/// tests below keep their fixed, bounded seed sets.
#[allow(dead_code)]
pub(crate) fn run_campaign(
    seeds: u64,
    z3: Option<&std::path::Path>,
    check_incremental: bool,
) -> (usize, usize, usize) {
    let mut stats = FuzzStats {
        sat: 0,
        unsat: 0,
        unknown: 0,
    };
    for seed in 0..seeds {
        run_seed(seed, z3, check_incremental, &mut stats);
    }
    (stats.sat, stats.unsat, stats.unknown)
}

fn run_seed(
    seed: u64,
    z3: Option<&std::path::Path>,
    check_incremental: bool,
    stats: &mut FuzzStats,
) {
    // Progress/diagnosis aid for the heavy runs: identifies the active seed
    // when an instance is pathologically slow. Off by default.
    if ay_core::misc_cli_flags().fuzz_verbose {
        eprintln!("[qflia-fuzz] seed={seed}");
    }
    let assertions = gen_instance(seed);
    let single_script = instance_script(&assertions, false);

    let single = solve_script(&single_script);
    let incr = if check_incremental {
        Some(solve_script(&instance_script(&assertions, true)))
    } else {
        None
    };

    // Single-shot and incremental must agree on definite verdicts.
    if let Some(incr) = incr.as_deref() {
        if single != "unknown" && incr != "unknown" {
            assert_eq!(
                single, incr,
                "single-shot vs incremental divergence (seed={seed}):\n{single_script}"
            );
        }
    }

    match single.as_str() {
        "sat" => stats.sat += 1,
        "unsat" => stats.unsat += 1,
        _ => stats.unknown += 1,
    }

    // CRITICAL DIRECTION: any unsat verdict must survive the independent
    // witness search. A witness in the box is a definite false UNSAT.
    if single == "unsat" || incr.as_deref() == Some("unsat") {
        if let Some((ints, bools)) = box_witness(&assertions) {
            panic!(
                "FALSE UNSAT (seed={seed}): witness ints={ints:?} bools={bools:?}\n{single_script}"
            );
        }
    }

    // Optional z3 cross-check (heavy run only; z3 resolved by caller).
    if let Some(z3_bin) = z3 {
        let dir = std::env::temp_dir();
        let path = dir.join(format!("ay-qflia-fuzz-{seed}.smt2"));
        std::fs::write(&path, &single_script).unwrap();
        let out = std::process::Command::new(z3_bin)
            .arg(&path)
            .output()
            .expect("failed to run z3");
        let _ = std::fs::remove_file(&path);
        let z3_verdict = String::from_utf8_lossy(&out.stdout);
        let z3_verdict = z3_verdict.lines().next().unwrap_or("").trim().to_string();
        if matches!(z3_verdict.as_str(), "sat" | "unsat") && single != "unknown" {
            assert_eq!(
                single, z3_verdict,
                "ay vs z3 divergence (seed={seed}):\n{single_script}"
            );
        }
    }
}

/// Default differential run: single-shot vs incremental vs brute-force
/// witness oracle. Hermetic (no z3 dependency).
#[test]
fn fuzz_qflia_single_shot_differential() {
    let mut stats = FuzzStats {
        sat: 0,
        unsat: 0,
        unknown: 0,
    };
    // Debug-build executor solves are ~0.2s each; keep the default run
    // bounded.  Additional deterministic strata below cover the historical
    // failures outside this prefix.
    let seeds = 128u64;
    for seed in 0..seeds {
        run_seed(seed, None, true, &mut stats);
    }
    // The QF_LIA pipeline is complete on this family; systematic unknowns
    // would mean the soundness fix degraded it to giving up.
    assert!(
        stats.unknown * 100 <= seeds as usize,
        "excessive unknown verdicts: {} of {seeds} (sat={}, unsat={})",
        stats.unknown,
        stats.sat,
        stats.unsat
    );
    // Sanity: the family must exercise both verdicts.
    assert!(
        stats.sat > 0 && stats.unsat > 0,
        "degenerate family: sat={} unsat={}",
        stats.sat,
        stats.unsat
    );
}

/// A second, disjoint deterministic stratum for the single-shot pipeline.
///
/// Large randomized campaigns are useful performance/fuzzing jobs, but a unit
/// test must be bounded and hermetic.  This range is always exercised and
/// retains the independent brute-force witness oracle.
#[test]
fn fuzz_qflia_single_shot_bounded_stratum() {
    let mut stats = FuzzStats {
        sat: 0,
        unsat: 0,
        unknown: 0,
    };
    let seeds = 32usize;
    for seed in 128..128 + seeds as u64 {
        run_seed(seed, None, false, &mut stats);
    }
    assert!(
        stats.unknown * 100 <= seeds,
        "excessive unknown verdicts: {} of {seeds} (sat={}, unsat={})",
        stats.unknown,
        stats.sat,
        stats.unsat
    );
}

/// Bounded strict strata requiring single-shot/incremental agreement.
///
/// The seed-981 divergence this test was built to keep visible is FIXED:
/// the push/pop incremental path returned a false UNSAT on a satisfiable
/// instance (single-shot: sat, z3: sat, witness x0=8 x1=-1 x2=-3 b0=T b1=F
/// b2=T). Root cause: `LraSolver::mk_bound_axiom_terms` emitted an integer
/// "trichotomy" axiom `(x <= k) ∨ (x >= k+1)` whenever the two bound values
/// were exactly 1 apart — unsound for FRACTIONAL bounds (x <= -5/3 ∨
/// x >= -2/3 excludes the integer -1 in the gap). The single-shot path
/// filtered the unsound axiom through the #6242/#6564 validation gate in
/// `extension/construction.rs`; the incremental injection macro
/// (`pipeline_inject_bound_axioms!`) had no such gate and pushed the axiom
/// straight into the SAT solver. Fixed at the generator (exact
/// no-integer-in-the-gap test) AND at the incremental injection
/// (same tautology validation as single-shot). See
/// `regression_seed981_incremental_false_unsat` for the pinned script.
///
/// The same strict run then exposed a SECOND false UNSAT at seed 3167 (LIA
/// tableau GCD conflict dropping fixed-slack equality reasons — see
/// `regression_seed3167_tableau_gcd_unit_conflict`), also fixed.
///
/// Rather than parking a thousands-seed campaign outside the default run, the
/// always-on strata bracket both historical failures.  The exact failing
/// seeds also remain as named witness regressions below.
#[test]
fn fuzz_qflia_single_shot_incremental_bounded_strata() {
    let mut stats = FuzzStats {
        sat: 0,
        unsat: 0,
        unknown: 0,
    };
    let strata = [976..986, 3162..3172];
    let mut seeds = 0usize;
    for range in strata {
        for seed in range {
            run_seed(seed, None, true, &mut stats);
            seeds += 1;
        }
    }
    assert!(
        stats.unknown * 100 <= seeds,
        "excessive unknown verdicts: {} of {seeds} (sat={}, unsat={})",
        stats.unknown,
        stats.sat,
        stats.unsat
    );
}

/// The generator itself is pinned: its current seed-236 script must remain
/// stable, parse, and retain its explicit Boolean contradiction. The generated
/// instance is NOT the minimized historical seed-236 SAT repro below: it
/// contains both `b0` and `not b0`, so it is provably UNSAT and correctly has
/// no box witness. Keeping that distinction explicit prevents the diagnostic
/// seed label from being mistaken for a satisfiability contract.
#[test]
fn generated_qflia_seed_236_is_stable_parseable_and_unsat() {
    const EXPECTED_SCRIPT: &str = concat!(
        "(set-logic QF_LIA)\n",
        "(declare-const x0 Int)\n",
        "(declare-const x1 Int)\n",
        "(declare-const x2 Int)\n",
        "(declare-const b0 Bool)\n",
        "(declare-const b1 Bool)\n",
        "(declare-const b2 Bool)\n",
        "(assert (not (or (<= (+ (* -2 x0) (* 3 x1) (* 2 x0)) -1) ",
        "(> (* -2 x1) -4) (not b1))))\n",
        "(assert b1)\n",
        "(assert (or (or (< (* 2 x2) 0) (> (* 1 x0) 2)) ",
        "(and (not b1) (<= (* 2 x2) 5)) ",
        "(or (< (+ (* 1 x2) (* -3 x1)) -1) b2 b0)))\n",
        "(assert (not b0))\n",
        "(assert b0)\n",
        "(check-sat)\n",
    );
    let seed = 236;
    let assertions = gen_instance(seed);
    let script = instance_script(&assertions, false);
    parse(&script).expect("seed-236 generated script must parse");
    assert_eq!(
        script, EXPECTED_SCRIPT,
        "seed-236 generator output changed; review the pinned regression"
    );
    assert!(
        script.contains("(assert b0)\n") && script.contains("(assert (not b0))\n"),
        "generated seed-236 must retain its explicit b0 contradiction:\n{script}"
    );
    assert!(
        box_witness(&assertions).is_none(),
        "a syntactically contradictory instance cannot have a box witness"
    );
    assert_eq!(
        solve_script(&script),
        "unsat",
        "generated seed-236 contradiction must be UNSAT"
    );
    assert!(
        script.ends_with("(check-sat)\n"),
        "generated single-shot script must issue check-sat"
    );
}

/// A representative satisfiable generator output must parse and retain an
/// independently checked satisfying witness.
#[test]
fn generated_qflia_seed_238_is_parseable_and_has_witness() {
    let seed = 238;
    let assertions = gen_instance(seed);
    let script = instance_script(&assertions, false);
    parse(&script).expect("seed-238 generated script must parse");
    let (ints, bools) = ([-6, 1, -6], [false, false, false]);
    assert!(
        assertions
            .iter()
            .all(|assertion| eval_form(assertion, &ints, &bools)),
        "seed-238 must retain its pinned satisfying witness"
    );
    assert!(
        script.ends_with("(check-sat)\n"),
        "generated single-shot script must issue check-sat"
    );
}

/// Pinned regression: the exact seed-981 script whose PUSH/POP-WRAPPED solve
/// returned a false UNSAT while the single-shot solve answered sat
/// (witness: x0=8, x1=-1, x2=-3, b0=true, b1=false, b2=true).
///
/// Mechanism: `mk_bound_axiom_terms` generated the unsound integer
/// trichotomy axiom `(-3*x1 >= 5) ∨ (-3*x1 <= 2)` — the bound values
/// normalize to x1 <= -5/3 and x1 >= -2/3, exactly 1 apart but fractional,
/// so the integer x1 = -1 in the open gap is wrongly excluded. Only the
/// incremental path injected it (no #6242 validation gate), flipping the
/// verdict to unsat. Both the generator and the injection gate are fixed;
/// this test pins the incremental AND single-shot verdicts.
#[test]
fn regression_seed981_incremental_false_unsat() {
    let assertions = gen_instance(981);
    // Pin the generated instance to the documented witness so RNG drift
    // cannot silently change what this regression covers.
    let (ints, bools) = ([8, -1, -3], [true, false, true]);
    assert!(
        assertions.iter().all(|a| eval_form(a, &ints, &bools)),
        "seed-981 witness no longer satisfies the generated instance — \
         RNG or generator drift; update the pinned witness"
    );
    assert_eq!(
        solve_script(&instance_script(&assertions, true)),
        "sat",
        "seed-981 incremental (push/pop) false UNSAT regression"
    );
    assert_eq!(
        solve_script(&instance_script(&assertions, false)),
        "sat",
        "seed-981 single-shot verdict"
    );
}

/// Pinned regression: seed 3167, the SECOND incremental false UNSAT exposed
/// by the strict heavy run after the seed-981 trichotomy fix (single-shot:
/// sat, z3: sat; witness x0=0, x1=0, x2=1, b0=b1=b2=false).
///
/// Mechanism (distinct from both seed-236 and seed-981): the LIA tableau GCD
/// test (`gcd_test_tableau`) correctly derived an infeasible row (3*x2 = 2
/// from pivoting the two equality rows), but
/// `collect_tableau_gcd_conflict_literals` walked the row participants
/// TERM-keyed via `var_term_id`. The fixed SLACK variables created for the
/// compound equality sums have no var→term mapping, so the equality reason
/// atoms that fixed them were silently dropped, leaving a unit conflict
/// clause that permanently excluded satisfiable space. Fixed by collecting
/// bound reasons VAR-keyed (`LraSolver::var_bounds_with_reasons`).
#[test]
fn regression_seed3167_tableau_gcd_unit_conflict() {
    let assertions = gen_instance(3167);
    let (ints, bools) = ([0, 0, 1], [false, false, false]);
    assert!(
        assertions.iter().all(|a| eval_form(a, &ints, &bools)),
        "seed-3167 witness no longer satisfies the generated instance — \
         RNG or generator drift; update the pinned witness"
    );
    assert_eq!(
        solve_script(&instance_script(&assertions, true)),
        "sat",
        "seed-3167 incremental (push/pop) false UNSAT regression"
    );
    assert_eq!(
        solve_script(&instance_script(&assertions, false)),
        "sat",
        "seed-3167 single-shot verdict"
    );
}

/// Pinned regression: the exact minimized seed-236 script that returned a
/// false UNSAT (model: x0=-1, x1=-1, x2=0, b0=true, b1=false, b2=false).
#[test]
fn regression_seed236_false_unsat() {
    let script = r#"
(set-logic QF_LIA)
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const b0 Bool)
(declare-const b1 Bool)
(declare-const b2 Bool)
(assert (or b2 (not b1)))
(assert (or (or (> (* 2 x0) -5) (< (+ (* -1 x0) (* -2 x2) (* -3 x1)) 0)) (=> (> (* -2 x0) -3) b1)))
(assert (or (not b0) (or (= (+ (* -3 x0) (* 3 x1) (* 1 x2)) 0) (= (+ (* -2 x2) (* -3 x2)) 3))))
(assert (and (=> (not b0) b1) (or (not b2) (not b1))))
(assert (=> (>= (* 3 x1) -2) (> (* -3 x1) -2)))
(assert (and (=> b2 (>= (+ (* 3 x1) (* 1 x0) (* -1 x1)) 2)) (or (= (+ (* 1 x2) (* 3 x0)) -3) b1)))
(check-sat)
"#;
    assert_eq!(
        solve_script(script),
        "sat",
        "seed-236 false UNSAT regression"
    );
}
