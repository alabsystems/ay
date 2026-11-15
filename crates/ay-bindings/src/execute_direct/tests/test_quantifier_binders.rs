// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! A quantifier BINDER is not a declared constant, and must never appear in a
//! model.
//!
//! `translate_quantifier` used to mint binders with `Solver::try_declare_const`,
//! which registers the name in `Solver::var_names` — exactly the table
//! `declared_variables()` enumerates and `try_get_model_map` then demands a
//! value for. Popping `bound_var_scopes` does not undo that registration, so
//! EVERY quantified query leaked its binders into the counterexample:
//!
//! * usually as a junk entry with an arbitrary value (`z`, `w` below);
//! * and, when the binder had no interpretation at all, as a LOST VERDICT —
//!   `(error "value of q is not available: no model value available for term of
//!   sort (_ BitVec 8)")` became `SolverError::ModelGenerationFailed`, which
//!   `execute`/`execute_incremental` reported as `model extraction failed: …`
//!   in place of the `sat` the solver had already decided. That is trust's
//!   `ABVFP` shape, whose 256-way finite-domain expansion leaves the binder
//!   with nothing to read.
//!
//! Binders are now minted with `Solver::try_fresh_var`, documented for exactly
//! this ("bound variables should not appear as top-level symbols in models")
//! and excluded from `declared_variables()` by design. This changes only which
//! names are enumerated for model extraction — it has no verdict authority —
//! so each test below pins the VERDICT as well as the model keys.

use super::*;

/// The counterexample model of a SAT result, or a panic naming what came back.
fn counterexample_model(program: &AYProgram) -> ExecuteValueMap<String> {
    match execute(program).expect("program must execute") {
        ExecuteResult::Counterexample { model, .. } => model,
        other => panic!("expected a counterexample (sat), got: {other:?}"),
    }
}

/// `c = 5 AND forall z:Int. z = z` — truth SAT (the universal is a tautology,
/// `c = 5` is satisfiable), and `z` is a BINDER, not a symbol of the problem.
#[test]
fn int_binder_does_not_leak_into_the_counterexample_model() {
    let mut program = AYProgram::new();
    program.set_logic("LIA");
    let c = program.declare_const("c", Sort::int());
    program.assert(c.eq(Expr::int(5)));
    program.assert(Expr::forall(
        vec![("z".to_string(), Sort::int())],
        Expr::var("z", Sort::int()).eq(Expr::var("z", Sort::int())),
    ));
    program.check_sat();

    let model = counterexample_model(&program);
    assert!(
        model.contains_key("c"),
        "the declared constant must be in the model, got keys: {:?}",
        model.keys().collect::<Vec<_>>()
    );
    assert!(
        !model.contains_key("z"),
        "the BINDER `z` must not be a model entry, got keys: {:?}",
        model.keys().collect::<Vec<_>>()
    );
}

/// The same leak over a bitvector binder — the sort family that escalated it
/// from junk to a lost verdict.
#[test]
fn bv_binder_does_not_leak_into_the_counterexample_model() {
    let mut program = AYProgram::new();
    program.set_logic("BV");
    let d = program.declare_const("d", Sort::bitvec(8));
    program.assert(d.eq(Expr::bitvec_const(0u64, 8)));
    program.assert(Expr::forall(
        vec![("w".to_string(), Sort::bitvec(8))],
        Expr::var("w", Sort::bitvec(8)).eq(Expr::var("w", Sort::bitvec(8))),
    ));
    program.check_sat();

    let model = counterexample_model(&program);
    assert!(model.contains_key("d"));
    assert!(
        !model.contains_key("w"),
        "the BINDER `w` must not be a model entry, got keys: {:?}",
        model.keys().collect::<Vec<_>>()
    );
}

/// THE `ABVFP` SHAPE, in the lane trust measures it through: a native
/// `AYProgram` with `:produce-proofs` on.
///
/// `forall q:BV8. fp.isNaN(fromBits(mem[q]))` is SATISFIABLE — `mem` constantly
/// the quiet-NaN bit pattern witnesses it — and ay decides it. The bridge used
/// to throw that verdict away: `Unknown("model extraction failed: model
/// generation failed: (error \"value of q is not available: no model value
/// available for term of sort (_ BitVec 8)\")")`.
///
/// `fromBits` uses the `(fp sign exp sig)` extract spelling, which is what
/// `trust-types::ay_bridge::fp_from_bv_expr` actually lowers to — NOT
/// `((_ to_fp 11 53) q)`, which takes a different path through ay and would
/// stop measuring this shape.
#[test]
fn abvfp_binder_no_longer_costs_the_sat_verdict() {
    let mut program = AYProgram::new();
    program.set_logic("ABVFP");
    program.set_option("produce-proofs", "true");
    let mem = program.declare_const("mem", Sort::array(Sort::bitvec(8), Sort::bitvec(64)));

    let word = mem.select(Expr::var("q", Sort::bitvec(8)));
    let from_bits = Expr::fp_from_bvs(
        word.clone().extract(63, 63),
        word.clone().extract(62, 52),
        word.extract(51, 0),
    );
    program.assert(Expr::forall(
        vec![("q".to_string(), Sort::bitvec(8))],
        from_bits.fp_is_nan(),
    ));
    program.check_sat();

    let result = execute(&program).expect("program must execute");
    let model = match result {
        ExecuteResult::Counterexample { model, .. } => model,
        other => panic!(
            "`ABVFP` is satisfiable and ay decides it; the bridge must not lose \
             the verdict extracting a model. Got: {other:?}"
        ),
    };
    assert!(
        !model.contains_key("q"),
        "the BINDER `q` must not be a model entry, got keys: {:?}",
        model.keys().collect::<Vec<_>>()
    );
    // The DECLARED array must still be there: a model that lost `mem` too would
    // pass the binder check while saying nothing. Its value is the 256-entry
    // `store` chain whose LEXICAL depth the `get-value` preflight refused
    // before `model_parse::get_value::admission::MAX_DEPTH` was raised — the
    // second half of this shape, and the one the binder failure had been
    // masking.
    assert!(
        model.contains_key("mem"),
        "the declared array must be in the model, got keys: {:?}",
        model.keys().collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// The TermId aliasing the old route created, and the error it must keep.
// ---------------------------------------------------------------------------

/// `try_declare_const` RETURNS THE EXISTING TERM for a repeated name+sort, so a
/// binder that shadowed a same-sorted declared constant shared its `TermId`.
/// `mk_forall` binds by NAME, so the two were structurally indistinguishable —
/// the setup for capture. A fresh identity per binder cannot alias anything.
///
/// TRUTH, established independently: `c = 5` fixes `c`, and `forall c:Int.
/// c > 0` is false at `c = -1` whichever reading of the shadowed name is taken,
/// so the conjunction is UNSAT either way. The interesting half is the next
/// test, where the two readings DISAGREE.
#[test]
fn shadowing_binder_over_a_false_universal_is_unsat() {
    let mut program = AYProgram::new();
    program.set_logic("LIA");
    let c = program.declare_const("c", Sort::int());
    program.assert(c.eq(Expr::int(5)));
    program.assert(Expr::forall(
        vec![("c".to_string(), Sort::int())],
        Expr::var("c", Sort::int()).int_gt(Expr::int(0)),
    ));
    program.check_sat();

    assert!(
        matches!(execute(&program).unwrap(), ExecuteResult::Verified),
        "forall c. c > 0 is false at c = -1"
    );
}

/// Where the readings disagree: `c = 5 AND forall c:Int. c = c`. Under correct
/// scoping the universal is a tautology and the outer `c = 5` stands, so the
/// answer is SAT with a model pinning `c` to 5 — and the shadowed BINDER still
/// must not appear.
#[test]
fn shadowing_binder_leaves_the_outer_constant_alone() {
    let mut program = AYProgram::new();
    program.set_logic("LIA");
    let c = program.declare_const("c", Sort::int());
    program.assert(c.eq(Expr::int(5)));
    program.assert(Expr::forall(
        vec![("c".to_string(), Sort::int())],
        Expr::var("c", Sort::int()).eq(Expr::var("c", Sort::int())),
    ));
    program.check_sat();

    let model = counterexample_model(&program);
    assert_eq!(
        model.get("c").map(String::as_str),
        Some("5"),
        "the OUTER `c` keeps its value; got model {model:?}"
    );
    assert_eq!(
        model.len(),
        1,
        "only the declared constant belongs in the model, got {model:?}"
    );
}
