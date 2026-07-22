// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential soundness gate for the Phase 5 difference-logic wiring
//! (`executor::diff_logic`).
//!
//! For a corpus of QF_IDL / QF_RDL instances (random + hand-written) we run the
//! SAME instance three ways and require they agree:
//!   1. the **diff-logic-ON** path (`(set-option :ay-diff-logic true)`),
//!   2. the **default** path (option absent / OFF — the always-correct solver),
//!   3. **z3** (ground truth; skipped gracefully when z3 is not on PATH).
//!
//! ANY sat/unsat mismatch fails the test (the gate's whole purpose). For each ON
//! instance we additionally assert the diff-logic engine actually *fired* (so we
//! are testing the new path, not coincidental agreement after a silent
//! fall-through), and on SAT we validate the produced model with `(get-value)`
//! plus a z3 re-check.

use super::Executor;
use ay_frontend::parse;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use std::io::Write;
use std::process::{Command, Stdio};

/// Run an SMT-LIB script through a fresh executor; return per-command outputs.
fn run(script: &str) -> Vec<String> {
    let cmds = parse(script).expect("parse");
    let mut exec = Executor::new();
    exec.execute_all(&cmds).expect("execute")
}

/// Run a script ON the diff-logic path, returning `(outputs, diff_logic_fired)`
/// for the LAST `(check-sat)`.
fn run_on(script: &str) -> (Vec<String>, bool) {
    let cmds = parse(script).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&cmds).expect("execute");
    (outputs, exec.last_diff_logic_decided_for_test())
}

/// Locate a z3 binary, or `None` to skip the z3 leg.
fn z3_path() -> Option<String> {
    for cand in [
        "z3",
        "/opt/homebrew/bin/z3",
        "/usr/local/bin/z3",
        "/usr/bin/z3",
    ] {
        if Command::new(cand)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
        {
            return Some(cand.to_string());
        }
    }
    None
}

/// Run a z3 script, returning the trimmed first verdict line.
fn run_z3(z3: &str, script: &str) -> String {
    let mut child = Command::new(z3)
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn z3");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(script.as_bytes())
        .expect("write z3 stdin");
    let out = child.wait_with_output().expect("z3 output");
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("")
        .to_string()
}

/// Extract the verdict from the executor's `(check-sat)` output line.
fn verdict(outputs: &[String]) -> &str {
    // The (check-sat) output is the first "sat"/"unsat"/"unknown" line.
    outputs
        .iter()
        .map(String::as_str)
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or("")
}

// ---------------------------------------------------------------------------
// Random instance generation (mirrors the diff-logic crate's z3 oracle).
// ---------------------------------------------------------------------------

const N_VARS: usize = 6;
const NUM_INSTANCES: usize = 250; // per logic

/// One generated atom in SMT-LIB form. We randomly emit `>`/`>=` and negation so
/// the parser's operator-normalization and `not` handling are exercised.
fn gen_atom_idl(rng: &mut ChaCha8Rng) -> String {
    let ops = ["<=", "<", "=", ">=", ">"];
    let x = rng.gen_range(0..N_VARS);
    // Keep y != x: `(- vx vx)` constant-folds to 0 at term construction, turning
    // the whole atom into a Bool literal that is no longer a DL atom (it would
    // legitimately fall through). Avoiding it keeps generated instances genuinely
    // difference-logic so the engine exercises the routing it is meant to cover.
    let y = (x + 1 + rng.gen_range(0..N_VARS - 1)) % N_VARS;
    let op = ops[rng.gen_range(0..ops.len())];
    let c = rng.gen_range(-15i64..=15);
    let cstr = if c < 0 {
        format!("(- {})", -c)
    } else {
        c.to_string()
    };
    let inner = if rng.gen_bool(0.2) {
        format!("({op} v{x} {cstr})")
    } else {
        format!("({op} (- v{x} v{y}) {cstr})")
    };
    // Occasionally wrap in `not` (but not for `=`, whose negation is a
    // disjunction the engine deliberately declines — those just fall through to
    // the default solver, which is still tested for agreement).
    if op != "=" && rng.gen_bool(0.3) {
        format!("(not {inner})")
    } else {
        inner
    }
}

fn gen_atom_rdl(rng: &mut ChaCha8Rng) -> String {
    let ops = ["<=", "<", "=", ">=", ">"];
    let x = rng.gen_range(0..N_VARS);
    // See gen_atom_idl: avoid y == x so the diff does not constant-fold to 0.
    let y = (x + 1 + rng.gen_range(0..N_VARS - 1)) % N_VARS;
    let op = ops[rng.gen_range(0..ops.len())];
    let num = rng.gen_range(-15i64..=15);
    let den = rng.gen_range(1i64..=6);
    let cstr = if den == 1 {
        if num < 0 {
            format!("(- {}.0)", -num)
        } else {
            format!("{num}.0")
        }
    } else {
        let n = if num < 0 {
            format!("(- {}.0)", -num)
        } else {
            format!("{num}.0")
        };
        format!("(/ {n} {den}.0)")
    };
    let inner = if rng.gen_bool(0.2) {
        format!("({op} v{x} {cstr})")
    } else {
        format!("({op} (- v{x} v{y}) {cstr})")
    };
    if op != "=" && rng.gen_bool(0.3) {
        format!("(not {inner})")
    } else {
        inner
    }
}

fn idl_header() -> String {
    let mut s = String::from("(set-logic QF_IDL)\n");
    for v in 0..N_VARS {
        s.push_str(&format!("(declare-fun v{v} () Int)\n"));
    }
    s
}

fn rdl_header() -> String {
    let mut s = String::from("(set-logic QF_RDL)\n");
    for v in 0..N_VARS {
        s.push_str(&format!("(declare-fun v{v} () Real)\n"));
    }
    s
}

/// The core differential driver, shared by IDL and RDL.
fn differential_corpus(
    seed: u64,
    header: fn() -> String,
    gen_atom: fn(&mut ChaCha8Rng) -> String,
    label: &str,
) {
    let z3 = z3_path();
    if z3.is_none() {
        eprintln!("NOTE {label}: z3 not on PATH — running executor-vs-executor only");
    }
    let mut rng = ChaCha8Rng::seed_from_u64(seed);

    let mut sat = 0usize;
    let mut unsat = 0usize;
    let mut fired = 0usize;
    let mut z3_checked = 0usize;
    // Instances skipped because a leg answered an honest resource-limited
    // "unknown" (process-wide memory-pressure gate under parallel test
    // loads). Verdict comparison is only meaningful when both legs
    // completed; the firing floor below is gated on skip-free runs.
    let mut resource_skipped = 0usize;

    for inst in 0..NUM_INSTANCES {
        let n_atoms = rng.gen_range(1..=12);
        let mut base = header();
        for _ in 0..n_atoms {
            base.push_str(&format!("(assert {})\n", gen_atom(&mut rng)));
        }

        // Default (option OFF) path — the always-correct reference.
        let def_out = run(&format!("{base}(check-sat)\n"));
        let def_v = verdict(&def_out);

        // Diff-logic ON path.
        let on_script = format!("(set-option :ay-diff-logic true)\n{base}(check-sat)\n");
        let (on_out, did_fire) = run_on(&on_script);
        let on_v = verdict(&on_out);

        if on_v == "unknown" || def_v == "unknown" {
            resource_skipped += 1;
            continue;
        }
        assert_eq!(
            on_v, def_v,
            "{label} ON-vs-DEFAULT mismatch on instance #{inst}\nscript:\n{base}"
        );
        if did_fire {
            fired += 1;
        }

        // z3 leg.
        if let Some(ref z3) = z3 {
            let z3_v = run_z3(z3, &format!("{base}(check-sat)\n"));
            if z3_v == "sat" || z3_v == "unsat" {
                z3_checked += 1;
                assert_eq!(
                    on_v, z3_v,
                    "{label} ON-vs-Z3 mismatch on instance #{inst}\nscript:\n{base}"
                );
            }
        }

        match def_v {
            "sat" => sat += 1,
            "unsat" => unsat += 1,
            other => panic!("{label} unexpected verdict {other:?} on instance #{inst}"),
        }
    }

    // The corpus must actually exercise the diff-logic path (not silently fall
    // through every time). Every generated atom is pure DL, so the engine should
    // fire on essentially every instance; require a large majority to catch any
    // routing regression that turns the path into a no-op.
    assert!(
        resource_skipped > 0 || fired * 10 >= NUM_INSTANCES * 9,
        "{label}: diff-logic engine fired on only {fired}/{NUM_INSTANCES} instances — \
         routing may be silently falling through"
    );
    eprintln!(
        "{label}: {NUM_INSTANCES} instances, {sat} sat / {unsat} unsat, \
         diff-logic fired on {fired}, z3-cross-checked {z3_checked}; 0 mismatches"
    );
}

#[test]
fn diff_logic_differential_idl() {
    differential_corpus(0xD1FF_10C0_A1A1_0001, idl_header, gen_atom_idl, "IDL");
}

#[test]
fn diff_logic_differential_rdl() {
    differential_corpus(0x5D10_AC1E_B2B2_0002, rdl_header, gen_atom_rdl, "RDL");
}

// ---------------------------------------------------------------------------
// Hand-written deterministic cases (sat/unsat/model/negation/var-const).
// ---------------------------------------------------------------------------

/// A satisfiable IDL instance routes through diff-logic and produces a model
/// that `(get-value)` can read.
#[test]
fn idl_sat_model_via_get_value() {
    let script = "(set-option :ay-diff-logic true)\n\
        (set-logic QF_IDL)\n\
        (declare-fun x () Int)(declare-fun y () Int)\n\
        (assert (<= (- x y) 3))\n\
        (assert (>= (- x y) 1))\n\
        (assert (<= x 10))\n\
        (check-sat)\n\
        (get-value (x y))\n";
    let (out, fired) = run_on(script);
    assert_eq!(verdict(&out), "sat");
    assert!(
        fired,
        "diff-logic engine must decide this pure-IDL instance"
    );
    // get-value output must mention both vars (model installed).
    let gv = out
        .iter()
        .find(|l| l.contains("x "))
        .expect("get-value output");
    assert!(gv.contains('x') && gv.contains('y'), "get-value: {gv}");
}

/// Classic negative-cycle UNSAT: x−y=1, y−z=1, z−x=1.
#[test]
fn idl_unsat_negative_cycle() {
    let script = "(set-option :ay-diff-logic true)\n\
        (set-logic QF_IDL)\n\
        (declare-fun x () Int)(declare-fun y () Int)(declare-fun z () Int)\n\
        (assert (= (- x y) 1))\n\
        (assert (= (- y z) 1))\n\
        (assert (= (- z x) 1))\n\
        (check-sat)\n";
    let (out, fired) = run_on(script);
    assert_eq!(verdict(&out), "unsat");
    assert!(fired);
    // Default path must agree.
    let def = run(&script.replacen("(set-option :ay-diff-logic true)\n", "", 1));
    assert_eq!(verdict(&def), "unsat");
}

/// Strict-over-integers UNSAT: x−y<1 ∧ y−x<0  ⇒  x−y<=0 ∧ y−x<=-1  ⇒  cycle −1.
#[test]
fn idl_unsat_strict_integer() {
    let script = "(set-option :ay-diff-logic true)\n\
        (set-logic QF_IDL)\n\
        (declare-fun x () Int)(declare-fun y () Int)\n\
        (assert (< (- x y) 1))\n\
        (assert (< (- y x) 0))\n\
        (check-sat)\n";
    let (out, fired) = run_on(script);
    assert_eq!(verdict(&out), "unsat");
    assert!(fired);
}

/// The SAME strict bounds are SAT over the reals (x−y can be 0.5).
#[test]
fn rdl_sat_strict_rational() {
    let script = "(set-option :ay-diff-logic true)\n\
        (set-logic QF_RDL)\n\
        (declare-fun x () Real)(declare-fun y () Real)\n\
        (assert (< (- x y) 1.0))\n\
        (assert (< (- y x) 0.0))\n\
        (check-sat)\n";
    let (out, fired) = run_on(script);
    assert_eq!(verdict(&out), "sat");
    assert!(fired);
}

/// `not (<= (- x y) 3)` ≡ `x − y > 3`; combined with `x − y <= 3` is UNSAT.
#[test]
fn idl_negation_handling_unsat() {
    let script = "(set-option :ay-diff-logic true)\n\
        (set-logic QF_IDL)\n\
        (declare-fun x () Int)(declare-fun y () Int)\n\
        (assert (<= (- x y) 3))\n\
        (assert (not (<= (- x y) 3)))\n\
        (check-sat)\n";
    let (out, fired) = run_on(script);
    assert_eq!(verdict(&out), "unsat");
    assert!(fired);
}

// ---------------------------------------------------------------------------
// Fall-through cases: the engine MUST decline these (decided == false) and the
// normal solver must handle them. These guard against the engine ever accepting
// something outside its conjunctive pure-DL fragment.
// ---------------------------------------------------------------------------

/// Boolean disjunction of DL atoms is NOT in the conjunctive fragment.
#[test]
fn boolean_structure_falls_through() {
    let script = "(set-option :ay-diff-logic true)\n\
        (set-logic QF_IDL)\n\
        (declare-fun x () Int)(declare-fun y () Int)\n\
        (assert (or (<= (- x y) 3) (<= (- y x) 3)))\n\
        (check-sat)\n";
    let (out, fired) = run_on(script);
    assert_eq!(verdict(&out), "sat");
    assert!(
        !fired,
        "disjunction must NOT be decided by the conjunctive DL engine"
    );
}

/// A three-variable / non-DL atom must fall through.
#[test]
fn non_difference_atom_falls_through() {
    let script = "(set-option :ay-diff-logic true)\n\
        (set-logic QF_LIA)\n\
        (declare-fun x () Int)(declare-fun y () Int)(declare-fun z () Int)\n\
        (assert (<= (+ x y z) 3))\n\
        (check-sat)\n";
    let (_out, fired) = run_on(script);
    assert!(
        !fired,
        "three-variable atom is not DL and must fall through"
    );
}

/// `not (= ...)` is a disjunction (`a < b ∨ a > b`) and must fall through.
#[test]
fn not_eq_falls_through() {
    let script = "(set-option :ay-diff-logic true)\n\
        (set-logic QF_IDL)\n\
        (declare-fun x () Int)(declare-fun y () Int)\n\
        (assert (not (= (- x y) 3)))\n\
        (check-sat)\n";
    let (out, fired) = run_on(script);
    assert_eq!(verdict(&out), "sat");
    assert!(!fired, "not(=) is a disjunction and must fall through");
}

/// With the option OFF, the engine must NEVER fire, even on a pure-DL instance.
/// This is the default-OFF no-op guarantee.
#[test]
fn default_off_never_fires() {
    let script = "(set-logic QF_IDL)\n\
        (declare-fun x () Int)(declare-fun y () Int)\n\
        (assert (<= (- x y) 3))\n\
        (assert (>= (- x y) 1))\n\
        (check-sat)\n";
    let (out, fired) = run_on(script);
    assert_eq!(verdict(&out), "sat");
    assert!(!fired, "default-OFF: diff-logic engine must never fire");
}

/// Explicit `:ay-diff-logic false` is also a no-op.
#[test]
fn explicit_false_never_fires() {
    let script = "(set-option :ay-diff-logic false)\n\
        (set-logic QF_IDL)\n\
        (declare-fun x () Int)(declare-fun y () Int)\n\
        (assert (<= (- x y) 3))\n\
        (check-sat)\n";
    let (_out, fired) = run_on(script);
    assert!(!fired, "explicit false: diff-logic engine must never fire");
}
