// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #7892: incremental BV-family false UNSAT after pop.
//!
//! All three scripts were minimized from ay/z3 differential mismatches found
//! on the shared incremental BV solve path.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

/// Parse every `#x..` bitvector literal on a `(get-value ...)` output line,
/// in binding order.
fn hex_values(line: &str) -> Vec<u64> {
    let mut values = Vec::new();
    let mut rest = line;
    while let Some(pos) = rest.find("#x") {
        let hex = &rest[pos + 2..];
        let end = hex
            .find(|c: char| !c.is_ascii_hexdigit())
            .unwrap_or(hex.len());
        values.push(u64::from_str_radix(&hex[..end], 16).expect("valid hex literal"));
        rest = &hex[end..];
    }
    values
}

#[test]
#[timeout(10_000)]
fn qf_bv_incremental_false_unsat_7892() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (declare-const z (_ BitVec 4))
        (assert (= (ite (= y x) y x) #x8))
        (check-sat)
        (push 1)
        (assert (= y #x8))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (bvule y #x3))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(
        results(&crate::common::solve(smt)),
        vec!["sat", "sat", "sat", "sat"]
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_incremental_false_unsat_7892() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 4) (_ BitVec 4)))
        (declare-const i (_ BitVec 4))
        (declare-const j (_ BitVec 4))
        (declare-const k (_ BitVec 4))
        (declare-const v (_ BitVec 4))
        (assert (distinct (select (store a j v) i) v))
        (check-sat)
        (push 1)
        (assert (distinct k i))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (select (store a k v) j) #xf))
        (assert (= (select a i) #xb))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(
        results(&crate::common::solve(smt)),
        vec!["sat", "sat", "sat", "sat"]
    );
}

#[test]
#[timeout(10_000)]
fn qf_aufbv_incremental_false_unsat_7892() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 4) (_ BitVec 4)))
        (declare-fun f ((_ BitVec 4)) (_ BitVec 4))
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (declare-const z (_ BitVec 4))
        (declare-const i (_ BitVec 4))
        (declare-const j (_ BitVec 4))
        (declare-const k (_ BitVec 4))
        (declare-const v (_ BitVec 4))
        (assert (distinct (select (store a k v) i) (select a i)))
        (check-sat)
        (push 1)
        (assert (= (bvmul x y) #xa))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (xor (= z #x6) (= (f z) #x6)))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (bvand z y) #x6))
        (assert (xor (= y #x5) (= (f y) #x5)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(
        results(&crate::common::solve(smt)),
        vec!["sat", "sat", "sat", "sat", "sat"]
    );
}

/// Contradiction in a pushed scope must not leak to outer scope.
/// Inner scope asserts x = #x0 AND x = #xf (contradiction -> UNSAT).
/// After pop, the outer scope with x = #x0 must be SAT.
#[test]
#[timeout(10_000)]
fn qf_bv_incremental_contradiction_isolation_7892() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x00))
        (check-sat)
        (push 1)
        (assert (= x #xff))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(
        results(&crate::common::solve(smt)),
        vec!["sat", "unsat", "sat"]
    );
}

/// Nested push/pop: two levels deep, check-sat at each level and after each pop.
/// Tests that scope tracking survives nested rebuild-on-pop.
#[test]
#[timeout(10_000)]
fn qf_bv_incremental_nested_scopes_7892() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (bvugt x #x10))
        (check-sat)
        (push 1)
        (assert (bvult x #x80))
        (check-sat)
        (push 1)
        (assert (= x y))
        (assert (= y #xff))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    // x > 0x10: SAT
    // x > 0x10 AND x < 0x80: SAT
    // x > 0x10 AND x < 0x80 AND x = y AND y = 0xff: UNSAT (0xff > 0x80)
    // x > 0x10 AND x < 0x80: SAT (inner contradiction gone)
    // x > 0x10: SAT (middle constraint also gone)
    assert_eq!(
        results(&crate::common::solve(smt)),
        vec!["sat", "sat", "unsat", "sat", "sat"]
    );
}

/// Many push/pop cycles: 8 rounds with alternating SAT/UNSAT constraints.
/// Exercises the rebuild-on-pop path repeatedly to stress cache invalidation.
#[test]
#[timeout(15_000)]
fn qf_bv_incremental_many_cycles_7892() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #xab))
        (check-sat)
        (push 1)(assert (= x #xcd))(check-sat)(pop 1)
        (check-sat)
        (push 1)(assert (bvugt x #xf0))(check-sat)(pop 1)
        (check-sat)
        (push 1)(assert (bvult x #x10))(check-sat)(pop 1)
        (check-sat)
        (push 1)(assert (= (bvand x #x0f) #x0f))(check-sat)(pop 1)
        (check-sat)
        (push 1)(assert (= x #x00))(check-sat)(pop 1)
        (check-sat)
        (push 1)(assert (= (bvor x #xff) #x00))(check-sat)(pop 1)
        (check-sat)
        (push 1)(assert (= (bvadd x #x55) #x00))(check-sat)(pop 1)
        (check-sat)
        (push 1)(assert (distinct x #xab))(check-sat)(pop 1)
        (check-sat)
    "#;

    let output = crate::common::solve(smt);
    let r = results(&output);
    // x = 0xab: SAT
    // x = 0xab AND x = 0xcd: UNSAT
    // x = 0xab: SAT
    // x = 0xab AND x > 0xf0: UNSAT
    // x = 0xab: SAT
    // x = 0xab AND x < 0x10: UNSAT
    // x = 0xab: SAT
    // x = 0xab AND (x & 0x0f) = 0x0f: UNSAT (0xab & 0x0f = 0x0b != 0x0f)
    // x = 0xab: SAT
    // x = 0xab AND x = 0x00: UNSAT
    // x = 0xab: SAT
    // x = 0xab AND (x | 0xff) = 0x00: UNSAT (0xff != 0x00)
    // x = 0xab: SAT
    // x = 0xab AND (x + 0x55) = 0x00: SAT (0xab + 0x55 = 0x00 mod 256)
    // x = 0xab: SAT
    // x = 0xab AND x != 0xab: UNSAT
    // x = 0xab: SAT
    assert_eq!(
        r,
        vec![
            "sat", "unsat", "sat", "unsat", "sat", "unsat", "sat", "unsat", "sat", "unsat", "sat",
            "unsat", "sat", "sat", "sat", "unsat", "sat"
        ]
    );
}

/// QF_ABV with array contradiction isolation: inner scope creates array
/// constraints that conflict, outer scope must remain satisfiable.
#[test]
#[timeout(10_000)]
fn qf_abv_incremental_array_contradiction_isolation_7892() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 4) (_ BitVec 4)))
        (declare-const i (_ BitVec 4))
        (declare-const v (_ BitVec 4))
        (assert (= (select a i) v))
        (check-sat)
        (push 1)
        (assert (= (select a i) #x0))
        (assert (= (select a i) #xf))
        (check-sat)
        (pop 1)
        (check-sat)
        (push 1)
        (assert (= v #x5))
        (assert (= (select a i) #x5))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    // (select a i) = v: SAT
    // (select a i) = v AND (select a i) = 0 AND (select a i) = 0xf: UNSAT (0 != 0xf)
    // (select a i) = v: SAT (contradiction gone)
    // (select a i) = v AND v = 5 AND (select a i) = 5: SAT (consistent)
    // (select a i) = v: SAT
    assert_eq!(
        results(&crate::common::solve(smt)),
        vec!["sat", "unsat", "sat", "sat", "sat"]
    );
}

/// QF_AUFBV: UF congruence axioms from a popped scope must not constrain
/// the outer scope. Tests that f(x) = f(y) learned from x = y inside a
/// pushed scope does not persist after pop.
#[test]
#[timeout(10_000)]
fn qf_aufbv_incremental_uf_congruence_isolation_7892() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (distinct (f x) (f y)))
        (check-sat)
        (push 1)
        (assert (= x y))
        (check-sat)
        (pop 1)
        (check-sat)
        (push 1)
        (assert (= x #xaa))
        (assert (= y #xbb))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    // f(x) != f(y): SAT (any x != y works via UF)
    // f(x) != f(y) AND x = y: UNSAT (congruence: x = y -> f(x) = f(y))
    // f(x) != f(y): SAT (congruence from x = y must not persist)
    // f(x) != f(y) AND x = 0xaa AND y = 0xbb: SAT (x != y, so f(x) != f(y) is possible)
    // f(x) != f(y): SAT
    assert_eq!(
        results(&crate::common::solve(smt)),
        vec!["sat", "unsat", "sat", "sat", "sat"]
    );
}

/// UF congruence axioms must use the stable BV variable offset, not the
/// growing Tseitin variable count (#7881). After pop-rebuild-checksat, the
/// Tseitin frontier advances past the BV offset. Congruence axioms generated
/// on a subsequent push must still reference the correct (stable-offset) SAT
/// variables for BV bits.
///
/// Sequence: check-sat, push+check-sat+pop, check-sat (rebuild), push+check-sat
/// The last check-sat previously returned false SAT because congruence axiom
/// clauses referenced wrong SAT variables (tseitin_num_vars != bv_var_offset).
#[test]
#[timeout(10_000)]
fn qf_ufbv_incremental_congruence_offset_regression_7881() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (distinct (f x) (f y)))
        (check-sat)
        (push 1)
        (assert (= x y))
        (check-sat)
        (pop 1)
        (check-sat)
        (push 1)
        (assert (= x y))
        (check-sat)
        (pop 1)
    "#;

    // distinct(f(x), f(y)): SAT
    // + x = y: UNSAT (congruence: f(x) = f(y))
    // distinct(f(x), f(y)): SAT (rebuild after pop)
    // + x = y: UNSAT (congruence must work after rebuild + intervening check-sat)
    assert_eq!(
        results(&crate::common::solve(smt)),
        vec!["sat", "unsat", "sat", "unsat"]
    );
}

/// Combined UF + array congruence in QF_AUFBV after pop-rebuild-checksat
/// (#7881). Tests that both UF congruence and array axioms use the stable
/// BV offset in the pushed scope following a rebuild.
#[test]
#[timeout(10_000)]
fn qf_aufbv_incremental_combined_congruence_offset_7881() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (distinct (f x) (f y)))
        (check-sat)
        (push 1)
        (assert (= x y))
        (check-sat)
        (pop 1)
        (check-sat)
        (push 1)
        (assert (= (select a (f x)) #xaa))
        (assert (= (select a (f y)) #xbb))
        (assert (= x y))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    // distinct(f(x), f(y)): SAT
    // + x = y: UNSAT
    // distinct(f(x), f(y)): SAT (rebuild)
    // + select(a,f(x))=aa, select(a,f(y))=bb, x=y: UNSAT
    //   (x=y -> f(x)=f(y) -> select(a,f(x))=select(a,f(y)), but aa != bb)
    // distinct(f(x), f(y)): SAT (rebuild)
    assert_eq!(
        results(&crate::common::solve(smt)),
        vec!["sat", "unsat", "sat", "unsat", "sat"]
    );
}

/// SOUNDNESS REGRESSION (#7892 model construction): the model emitted by the
/// pop-rebuild check-sat must satisfy UF congruence, and it must be pinned
/// back into the formula and re-confirmed by z3.
///
/// Root cause fixed: on the incremental BV+UF lane, `state.term_to_bits` was
/// snapshotted BEFORE `materialize_uf_arg_bv_terms` allocated bit variables
/// for UF arguments (`x`, `y` appear only inside `f(x)`, `f(y)`), so model
/// extraction never read the SAT solver's assignment for them and model
/// completion invented `x = y = #x00` — while the same model claimed
/// `f(x) != f(y)`, violating congruence. The independent model gate correctly
/// refuted that witness and degraded the (correct) `sat` to `unknown`.
#[test]
#[timeout(30_000)]
fn qf_ufbv_incremental_rebuild_model_satisfies_congruence_7892() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (distinct (f x) (f y)))
        (check-sat)
        (push 1)
        (assert (= x y))
        (check-sat)
        (pop 1)
        (check-sat)
        (get-value (x y (f x) (f y)))
    "#;

    let output = crate::common::solve(smt);
    assert_eq!(
        results(&output),
        vec!["sat", "unsat", "sat"],
        "verdict sequence changed:\n{output}"
    );

    // Semantic re-evaluation of the EMITTED witness for the rebuild check-sat.
    let value_line = output
        .lines()
        .find(|line| line.trim_start().starts_with("(("))
        .unwrap_or_else(|| panic!("no get-value output in:\n{output}"));
    let values = hex_values(value_line);
    assert_eq!(
        values.len(),
        4,
        "expected values for x, y, (f x), (f y) in: {value_line}"
    );
    let (xv, yv, fxv, fyv) = (values[0], values[1], values[2], values[3]);
    // The asserted disequality must hold in the witness.
    assert_ne!(
        fxv, fyv,
        "witness violates (distinct (f x) (f y)): {value_line}"
    );
    // UF congruence must hold in the witness: x = y implies f(x) = f(y).
    // (Combined with the line above this forces x != y.)
    assert!(
        xv != yv || fxv == fyv,
        "witness violates congruence (x = y but f(x) != f(y)): {value_line}"
    );

    // z3-pin: the emitted witness, asserted back into the original formula,
    // must be consistent (z3 says sat).
    if crate::common::check_z3_or_skip() {
        use std::io::Write;
        let pinned = format!(
            "(set-logic QF_UFBV)\n\
             (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\n\
             (declare-const x (_ BitVec 8))\n\
             (declare-const y (_ BitVec 8))\n\
             (assert (distinct (f x) (f y)))\n\
             (assert (= x #x{xv:02x}))\n\
             (assert (= y #x{yv:02x}))\n\
             (assert (= (f x) #x{fxv:02x}))\n\
             (assert (= (f y) #x{fyv:02x}))\n\
             (check-sat)\n"
        );
        let path = std::env::temp_dir().join(format!(
            "ay_bv_incr_rebuild_model_7892_{}.smt2",
            std::process::id()
        ));
        let mut file = std::fs::File::create(&path).expect("create temp smt2");
        file.write_all(pinned.as_bytes()).expect("write temp smt2");
        drop(file);
        let outcome = crate::common::run_z3_file(&path, 10).expect("run z3");
        let _ = std::fs::remove_file(&path);
        assert_eq!(
            outcome,
            crate::common::SolverOutcome::Sat,
            "z3 refutes the emitted rebuild model:\n{pinned}"
        );
    }
}

/// Nested push/pop with UF congruence after rebuild (#7881).
/// Tests that the offset fix works through multiple nesting levels.
#[test]
#[timeout(10_000)]
fn qf_aufbv_incremental_nested_congruence_offset_7881() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (distinct (f x) (f y)))
        (check-sat)
        (push 1)
        (assert (= x y))
        (check-sat)
        (pop 1)
        (check-sat)
        (push 1)
        (assert (= x #x10))
        (push 1)
        (assert (= y #x10))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    // distinct(f(x), f(y)): SAT
    // + x = y: UNSAT
    // distinct(f(x), f(y)): SAT (rebuild)
    // + x = 0x10, + y = 0x10: UNSAT (x=y=0x10 -> f(x)=f(y), contradicts distinct)
    // + x = 0x10: SAT (y can be anything != 0x10)
    // distinct(f(x), f(y)): SAT (rebuild)
    assert_eq!(
        results(&crate::common::solve(smt)),
        vec!["sat", "unsat", "sat", "unsat", "sat", "sat"]
    );
}
