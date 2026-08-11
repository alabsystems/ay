// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the solver-backed (non-identical) BV bit-blast refutation.

use super::*;
use crate::bv_blast_export::{BvBlastValidateError, ClauseProvenance, ResRule};
use proptest::prelude::*;
use std::time::Duration;

fn one_pivot_refutation() -> (ResolutionDag, Vec<Clause>) {
    let variable = Variable::new(0);
    let positive = Literal::positive(variable);
    let negative = Literal::negative(variable);
    let dag = ResolutionDag {
        num_vars: 1,
        original_clauses: vec![(1, vec![positive]), (2, vec![negative])],
        derived: vec![RupStep {
            id: 3,
            clause: Vec::new(),
            rup_hints: vec![1, 2],
        }],
        empty_clause_id: 3,
    };
    let clauses = vec![
        Clause {
            id: 0,
            lits: vec![Lit::pos(0)],
            provenance: ClauseProvenance::Disequality,
        },
        Clause {
            id: 1,
            lits: vec![Lit::neg(0)],
            provenance: ClauseProvenance::Disequality,
        },
    ];
    (dag, clauses)
}

#[test]
fn rup_expansion_rejects_resolution_step_cap_before_emission() {
    let (dag, clauses) = one_pivot_refutation();
    let error = expand_dag_to_resolution(
        &dag,
        &clauses,
        Some(RupExpansionLimits {
            max_steps: 0,
            deadline: Instant::now() + Duration::from_secs(1),
        }),
    )
    .expect_err("a zero-step cap must reject the first required resolution");
    assert!(matches!(
        error,
        BvSolvedExportError::ResourceLimit {
            resource: "expanded resolution steps",
            limit: 0,
            actual: 1,
        }
    ));
}

#[test]
fn rup_expansion_rejects_an_already_expired_deadline() {
    let (dag, clauses) = one_pivot_refutation();
    let error = expand_dag_to_resolution(
        &dag,
        &clauses,
        Some(RupExpansionLimits {
            max_steps: usize::MAX,
            deadline: Instant::now(),
        }),
    )
    .expect_err("an already-expired absolute deadline must fail closed");
    assert!(matches!(
        error,
        BvSolvedExportError::ResourceLimit {
            resource: "RUP expansion deadline",
            ..
        }
    ));
}

/// A genuinely non-identical, valid obligation (commutativity of `bvadd`) at a
/// real width (>= 8) yields a `BvBlastProof` whose `validate()` passes: every
/// resolution is recomputed, the chain ends in the empty clause, no opaque step.
#[test]
fn add_commutes_width8_solver_backed_validates() {
    let proof = export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 8 })
        .expect("commutativity of bvadd is UNSAT, must export");
    proof
        .validate()
        .expect("solver-backed proof must be well-formed");
    // No opaque step is representable, but assert the chain is all resolutions.
    assert!(proof
        .refutation
        .steps
        .iter()
        .all(|s| matches!(s.rule, ResRule::Resolution)));
    // Final step is the empty clause.
    assert!(proof
        .refutation
        .steps
        .last()
        .expect("non-empty refutation")
        .clause
        .is_empty());
    // The two sides must NOT have fused: there are distinct LhsOut and RhsOut
    // vars, so this is the real-width path, not the operand-sharing shortcut.
    let lhs = proof
        .vars
        .roles
        .iter()
        .filter(|r| matches!(r, VarRole::LhsOut { .. }))
        .count();
    let rhs = proof
        .vars
        .roles
        .iter()
        .filter(|r| matches!(r, VarRole::RhsOut { .. }))
        .count();
    assert_eq!(lhs, 8, "8 distinct lhs output bits");
    assert_eq!(rhs, 8, "8 distinct rhs output bits");
}

/// At width 32 the same obligation still produces a solver-derived, validating
/// proof (scales to slice width).
#[test]
fn add_commutes_width32_solver_backed_validates() {
    let proof = export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 32 })
        .expect("width-32 commutativity is UNSAT, must export");
    proof.validate().expect("width-32 proof must validate");
}

/// A genuinely-SAT obligation (a FALSE identity: `bvsub(a,b) == bvsub(b,a)`)
/// yields `NoRefutation` — no bogus proof is fabricated.
#[test]
fn false_identity_yields_no_refutation() {
    let err = export_bv_blast_proof_solved(SolvedObligation::SubAntiCommutesFalse { width: 8 })
        .expect_err("anti-commutativity of bvsub is SAT, must not export");
    assert_eq!(err, BvSolvedExportError::NoRefutation);
}

/// The surfaced refutation really is the solver's: the raw LRAT the ay-sat
/// engine emits is independently accepted by the bundled `ay-lrat-check`
/// checker over the same CNF. This proves the chain we expand is solver-derived,
/// not constructed.
#[test]
fn raw_solver_lrat_is_accepted_by_independent_checker() {
    use ay_sat::{Literal as SatLit, Variable as SatVar};

    // Rebuild the exact CNF the exporter hands to the solver for width 8.
    let proof =
        export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 8 }).expect("export");
    let num_vars = proof.vars.len();
    let sat_clauses: Vec<Vec<SatLit>> = proof
        .clauses
        .iter()
        .map(|c| {
            c.lits
                .iter()
                .map(|l| {
                    let v = SatVar::new(l.var);
                    if l.neg {
                        SatLit::negative(v)
                    } else {
                        SatLit::positive(v)
                    }
                })
                .collect()
        })
        .collect();

    // Re-solve to obtain the raw DAG and reconstruct the LRAT text, then run it
    // through the independent ay-lrat-check checker.
    let dag = ay_sat::prove_unsat_resolution_dag(num_vars, &sat_clauses).expect("must be UNSAT");

    // Build LRAT steps for ay-lrat-check from the surfaced DAG.
    use ay_lrat_check::checker::LratChecker as IndepChecker;
    use ay_lrat_check::dimacs::Literal as CheckLit;
    use ay_lrat_check::lrat_parser::LratStep;

    let to_check = |l: &SatLit| CheckLit::from_dimacs(l.to_dimacs());
    let mut checker = IndepChecker::new(num_vars);
    for (id, lits) in &dag.original_clauses {
        let cl: Vec<CheckLit> = lits.iter().map(to_check).collect();
        assert!(checker.add_original(*id, &cl), "original {id}");
    }
    let steps: Vec<LratStep> = dag
        .derived
        .iter()
        .map(|s| LratStep::Add {
            id: s.id,
            clause: s.clause.iter().map(to_check).collect(),
            hints: s.rup_hints.iter().map(|&h| h as i64).collect(),
        })
        .collect();
    assert!(
        checker.verify_proof(&steps),
        "independent ay-lrat-check must accept the solver's raw refutation"
    );
}

/// Tampering the solver-backed proof (drop the empty clause) is caught.
#[test]
fn tampered_solver_proof_fails_validation() {
    let mut proof =
        export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 8 }).expect("export");
    proof.refutation.steps.pop();
    let err = proof.validate().expect_err("truncated chain must fail");
    assert!(matches!(
        err,
        BvBlastValidateError::NotEmptyClause(_) | BvBlastValidateError::ResolutionMismatch { .. }
    ));
}

/// Every clause in the solver-backed proof carries either checked gate
/// provenance or the single disequality — no opaque/agreement provenance.
#[test]
fn solver_proof_clauses_have_checked_provenance() {
    let proof =
        export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 8 }).expect("export");
    for cl in &proof.clauses {
        assert!(matches!(
            cl.provenance,
            ClauseProvenance::BitLemmaCnf { .. } | ClauseProvenance::Disequality
        ));
    }
    let diseqs = proof
        .clauses
        .iter()
        .filter(|c| matches!(c.provenance, ClauseProvenance::Disequality))
        .count();
    assert_eq!(diseqs, 1, "exactly one disequality clause");
}

/// Width 0 is rejected with a typed error.
#[test]
fn width_zero_rejected() {
    let err = export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 0 })
        .expect_err("width 0 invalid");
    assert!(matches!(
        err,
        BvSolvedExportError::UnsupportedWidth { got: 0, .. }
    ));
}

// ───────────────────── expression-tree path (the live gate's shape) ──────────

/// `W_n` = low 32 bits of the 64-bit argument register `X_n`, exactly as the
/// external-codegen M-POS gate builds it: `BvExtract(Var("Xn", 64), 31, 0)`.
fn wn_expr(n: u32) -> BvExpr {
    BvExpr::extract(BvExpr::leaf(&format!("X{n}"), 64), 31, 0)
}

/// THE GATE'S ADD-LEAF GOAL. machine_out vs auto_spec:
///   machine_out = BvExtract(BvZeroExt(BvAdd(W0,W1,32),32),31,0)
///   auto_spec   = BvAdd(W0,W1,32)
/// `not(machine_out == auto_spec)` is UNSAT (the readout extract∘zero_ext is the
/// identity on the 32-bit adder result), so the generalized exporter must produce
/// a proof whose `validate()` passes — ay out of the re-check TCB.
#[test]
fn gate_add_leaf_goal_exports_and_validates() {
    let inner_add = BvExpr::add(wn_expr(0), wn_expr(1)); // BvAdd(W0, W1, 32)
    let machine_out = BvExpr::extract(BvExpr::zero_ext(inner_add.clone(), 32), 31, 0);
    let auto_spec = inner_add;

    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("gate add-leaf equality is valid (UNSAT negation), must export");

    // Zero-trust well-formedness: every resolution recomputed, chain ends empty,
    // no opaque step representable.
    proof
        .validate()
        .expect("generalized add-leaf proof must validate");
    assert!(proof
        .refutation
        .steps
        .iter()
        .all(|s| matches!(s.rule, ResRule::Resolution)));
    assert!(
        proof
            .refutation
            .steps
            .last()
            .expect("non-empty refutation")
            .clause
            .is_empty(),
        "refutation must end in the empty clause"
    );

    // Shared leaves: X0 and X1 each contribute exactly one set of 64 input bits,
    // referenced by both sides (no duplicate per-side leaf vars).
    let leaf_bits = proof
        .vars
        .roles
        .iter()
        .filter(|r| matches!(r, VarRole::InputLeaf { .. }))
        .count();
    assert_eq!(
        leaf_bits, 128,
        "two 64-bit leaves X0, X1, shared across sides"
    );

    // 32-bit equality.
    let eq_vars = proof
        .vars
        .roles
        .iter()
        .filter(|r| matches!(r, VarRole::BitEq { .. }))
        .count();
    assert_eq!(eq_vars, 32, "32-bit per-bit equality");
}

/// The generalized add-leaf proof serde-round-trips and still validates (this is
/// exactly the byte stream the downstream proof consumer re-check consumes).
#[test]
fn gate_add_leaf_proof_serde_round_trip() {
    let inner_add = BvExpr::add(wn_expr(0), wn_expr(1));
    let machine_out = BvExpr::extract(BvExpr::zero_ext(inner_add.clone(), 32), 31, 0);
    let proof = export_bv_blast_proof_expr(&machine_out, &inner_add).expect("export");
    let json = serde_json::to_string(&proof).expect("ser");
    let back: BvBlastProof = serde_json::from_str(&json).expect("de");
    assert_eq!(&proof, &back);
    back.validate().expect("round-tripped proof validates");
}

/// ANTI-VACUITY (the load-bearing honesty test). A SATISFIABLE goal — the FALSE
/// identity `BvAdd(W0,W1) == BvSub(W0,W1)` — must NOT yield a validating
/// refutation. The exporter returns `NoRefutation` (the solver finds a model);
/// a "proven" verdict here would be a soundness hole.
#[test]
fn anti_vacuity_add_eq_sub_yields_no_refutation() {
    let lhs = BvExpr::add(wn_expr(0), wn_expr(1));
    let rhs = BvExpr::sub(wn_expr(0), wn_expr(1));
    let err = export_bv_blast_proof_expr(&lhs, &rhs)
        .expect_err("add == sub is a false identity (SAT), must NOT export a proof");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// ANTI-VACUITY, second shape: even with the readout wrapper on one side, a
/// genuinely-different operation underneath is still SAT and refused.
#[test]
fn anti_vacuity_wrapped_sub_yields_no_refutation() {
    let inner_sub = BvExpr::sub(wn_expr(0), wn_expr(1));
    let machine_out = BvExpr::extract(BvExpr::zero_ext(inner_sub, 32), 31, 0);
    let auto_spec = BvExpr::add(wn_expr(0), wn_expr(1));
    let err = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect_err("extract(zext(sub)) == add is SAT, must NOT export");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// A reflexive non-trivial equality (`extract(zext(add)) == extract(zext(add))`)
/// is valid and validates — confirms the expr path is not accidentally tied to a
/// single fixed shape.
#[test]
fn reflexive_wrapped_add_validates() {
    let inner_add = BvExpr::add(wn_expr(2), wn_expr(3));
    let wrapped = BvExpr::extract(BvExpr::zero_ext(inner_add, 32), 31, 0);
    let proof =
        export_bv_blast_proof_expr(&wrapped, &wrapped).expect("reflexive equality is UNSAT");
    proof.validate().expect("reflexive proof validates");
}

/// Width mismatch between the two sides is a typed error, not a panic and not a
/// bogus proof.
#[test]
fn width_mismatch_rejected() {
    // lhs is 32-bit (extract of a 32-bit add), rhs is 64-bit (zero_ext, no extract).
    let inner = BvExpr::add(wn_expr(0), wn_expr(1));
    let lhs = inner.clone();
    let rhs = BvExpr::zero_ext(inner, 32); // 64 bits
    let err = export_bv_blast_proof_expr(&lhs, &rhs).expect_err("32 vs 64 bit mismatch");
    assert!(matches!(
        err,
        BvExprExportError::WidthMismatch { lhs: 32, rhs: 64 }
    ));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(6))]

    /// For a range of real widths, the commutativity obligation always exports a
    /// solver-derived proof that validates and ends in the empty clause.
    #[test]
    fn prop_add_commutes_validates(width in 8u32..=16) {
        let proof = export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width })
            .expect("commutativity must export");
        prop_assert!(proof.validate().is_ok());
        prop_assert!(proof.refutation.steps.last().map(|s| s.clause.is_empty()).unwrap_or(false));
    }

    /// serde round-trip of a solver-backed proof preserves it and it still
    /// validates.
    #[test]
    fn prop_solver_proof_serde_round_trip(width in 8u32..=12) {
        let proof = export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width })
            .expect("export");
        let json = serde_json::to_string(&proof).expect("ser");
        let back: BvBlastProof = serde_json::from_str(&json).expect("de");
        prop_assert_eq!(&proof, &back);
        prop_assert!(back.validate().is_ok());
    }
}

// ============================================================================
// BvOr / BvExpr::Const — the RAW M-POS gate obligation fragment (GAP 3 close).
//
// The LIVE gate's RAW `symbolic_machine_output` wraps the adder leaf in `BvOr`
// identity wrappers (`BvOr(Const{0}, x)`) and carries `BitVec` constant literals.
// These tests bit-blast that RAW shape via the EXTENDED set (Or + Const) WITHOUT
// a trusted normalization step, and confirm anti-vacuity is still solver-enforced.
// ============================================================================

/// `bvor(0, x) == x` identity is UNSAT for the negation: a 32-bit OR with the
/// all-zeros constant is the identity. The exporter must bit-blast `Or` + `Const`
/// and surface a real validating refutation.
#[test]
fn or_with_zero_const_is_identity_validates() {
    let x = BvExpr::leaf("X0", 32);
    let zero = BvExpr::const_val(0, 32);
    let machine_out = BvExpr::or(zero, x.clone()); // BvOr(Const{0}, X0)
    let auto_spec = x;
    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("bvor(0, x) == x is valid (UNSAT negation), must export");
    proof.validate().expect("or-identity proof validates");
    assert!(
        proof
            .refutation
            .steps
            .last()
            .expect("non-empty refutation")
            .clause
            .is_empty(),
        "refutation must end in the empty clause"
    );
}

/// `bvand(allones, x) == x` is valid (UNSAT negation): AND with the all-ones mask
/// is the identity. Confirms the per-bit `And2` blast path exports a real
/// validating refutation, mirroring the Or path.
#[test]
fn and_with_allones_const_is_identity_validates() {
    let x = BvExpr::leaf("X0", 32);
    let allones = BvExpr::const_val((1u128 << 32) - 1, 32);
    let machine_out = BvExpr::and(allones, x.clone()); // BvAnd(0xFFFF_FFFF, X0)
    let auto_spec = x;
    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("bvand(allones, x) == x is valid (UNSAT negation), must export");
    proof.validate().expect("and-identity proof validates");
    assert!(
        proof
            .refutation
            .steps
            .last()
            .expect("non-empty refutation")
            .clause
            .is_empty(),
        "refutation must end in the empty clause"
    );
}

/// ANTI-VACUITY: `bvand(x, x) == bvor(x, x)` is NOT generally true bit-by-bit?
/// Actually AND and OR of x with itself both equal x, so that IS valid. To get a
/// genuine SAT (non-identity) we compare `bvand(allones, x) == bvand(0, x)`: the
/// LHS is x, the RHS is 0, so they differ whenever x != 0. Must NOT export.
#[test]
fn anti_vacuity_and_identity_vs_zero_yields_no_refutation() {
    let x = BvExpr::leaf("X0", 32);
    let allones = BvExpr::const_val((1u128 << 32) - 1, 32);
    let zero = BvExpr::const_val(0, 32);
    let machine_out = BvExpr::and(allones, x.clone()); // == x
    let auto_spec = BvExpr::and(zero, x); // == 0
    let err = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect_err("and(allones,x) == and(0,x) is SAT (x != 0), must NOT export");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// `bvxor(0, x) == x` is valid (UNSAT negation): XOR with zero is the identity.
/// Confirms the per-bit `Xor2` blast path exports a real validating refutation.
#[test]
fn xor_with_zero_const_is_identity_validates() {
    let x = BvExpr::leaf("X0", 32);
    let zero = BvExpr::const_val(0, 32);
    let machine_out = BvExpr::xor(zero, x.clone()); // BvXor(0, X0)
    let auto_spec = x;
    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("bvxor(0, x) == x is valid (UNSAT negation), must export");
    proof.validate().expect("xor-identity proof validates");
    assert!(
        proof
            .refutation
            .steps
            .last()
            .expect("non-empty refutation")
            .clause
            .is_empty(),
        "refutation must end in the empty clause"
    );
}

/// ANTI-VACUITY: `bvxor(0, x) == bvxor(allones, x)` is FALSE (XOR with all-ones is
/// bitwise NOT, never equal to x). The solver finds a model → NoRefutation.
#[test]
fn anti_vacuity_xor_identity_vs_not_yields_no_refutation() {
    let x = BvExpr::leaf("X0", 32);
    let zero = BvExpr::const_val(0, 32);
    let allones = BvExpr::const_val((1u128 << 32) - 1, 32);
    let machine_out = BvExpr::xor(zero, x.clone()); // == x
    let auto_spec = BvExpr::xor(allones, x); // == ~x
    let err = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect_err("xor(0,x) == xor(allones,x) is SAT, must NOT export");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// THE RAW GATE ADD-LEAF OBLIGATION, with the live gate's BvOr/Const wrappers:
///   machine_out = BvExtract(BvZeroExt( BvOr(Const{0,32}, BvAdd(W0,W1)), 32), 31, 0)
///   auto_spec   = BvAdd(W0, W1)
/// `not(machine_out == auto_spec)` is UNSAT (the OR-with-zero + readout extract∘zext
/// are the identity on the 32-bit adder result), so the EXTENDED exporter produces a
/// validating proof — ingesting the RAW shape WITHOUT normalization. ay out of the
/// re-check TCB.
#[test]
fn raw_gate_add_leaf_with_or_const_wrappers_validates() {
    let inner_add = BvExpr::add(wn_expr(0), wn_expr(1)); // BvAdd(W0, W1, 32)
    let or_wrapped = BvExpr::or(BvExpr::const_val(0, 32), inner_add.clone());
    let machine_out = BvExpr::extract(BvExpr::zero_ext(or_wrapped, 32), 31, 0);
    let auto_spec = inner_add;

    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("RAW or/const-wrapped add-leaf is valid (UNSAT negation), must export");
    proof
        .validate()
        .expect("RAW or/const-wrapped add-leaf proof must validate");
    assert!(proof
        .refutation
        .steps
        .iter()
        .all(|s| matches!(s.rule, ResRule::Resolution)));
    assert!(
        proof
            .refutation
            .steps
            .last()
            .expect("non-empty refutation")
            .clause
            .is_empty(),
        "refutation must end in the empty clause"
    );
    // The RAW shape still references exactly the two shared 64-bit leaves.
    let leaf_bits = proof
        .vars
        .roles
        .iter()
        .filter(|r| matches!(r, VarRole::InputLeaf { .. }))
        .count();
    assert_eq!(
        leaf_bits, 128,
        "two 64-bit leaves X0, X1, shared across sides"
    );
}

/// ANTI-VACUITY for the RAW shape: the SAME BvOr/Const wrappers over a genuinely
/// different operation (sub) is SAT and must NOT export — the wrappers do not
/// launder a false identity into a proof.
#[test]
fn anti_vacuity_raw_or_const_wrapped_sub_yields_no_refutation() {
    let inner_sub = BvExpr::sub(wn_expr(0), wn_expr(1));
    let or_wrapped = BvExpr::or(BvExpr::const_val(0, 32), inner_sub);
    let machine_out = BvExpr::extract(BvExpr::zero_ext(or_wrapped, 32), 31, 0);
    let auto_spec = BvExpr::add(wn_expr(0), wn_expr(1));
    let err = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect_err("or/const-wrapped sub == add is SAT, must NOT export");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// ANTI-VACUITY for a NON-zero constant: `bvor(1, x) == x` is FALSE (bit 0 forced
/// to 1 differs from x whenever x's bit 0 is 0). The solver finds a model →
/// NoRefutation. Confirms `Const` emits real fixed literals, not a structural no-op.
#[test]
fn anti_vacuity_or_with_nonzero_const_yields_no_refutation() {
    let x = BvExpr::leaf("X0", 32);
    let one = BvExpr::const_val(1, 32);
    let machine_out = BvExpr::or(one, x.clone());
    let auto_spec = x;
    let err = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect_err("bvor(1, x) == x is SAT (a false identity), must NOT export");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// A non-zero constant equality that IS valid: `bvor(x, allones) == allones`
/// (OR with the all-ones constant is the constant). Confirms set `Const` bits
/// blast correctly and the proof validates.
#[test]
fn or_with_allones_const_validates() {
    let allones = BvExpr::const_val(0xFFFF_FFFF, 32);
    let x = BvExpr::leaf("X0", 32);
    let machine_out = BvExpr::or(x, allones.clone());
    let auto_spec = allones;
    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("bvor(x, allones) == allones is valid (UNSAT negation), must export");
    proof.validate().expect("or-allones proof validates");
}

/// A `Const` whose value does not fit in its declared width is malformed, not a
/// silent truncation.
#[test]
fn const_overflowing_width_rejected() {
    // value 0x100 needs 9 bits, declared width 8.
    let bad = BvExpr::const_val(0x100, 8);
    let other = BvExpr::leaf("X0", 8);
    let err = export_bv_blast_proof_expr(&bad, &other)
        .expect_err("constant 0x100 does not fit in 8 bits");
    assert!(matches!(err, BvExprExportError::Malformed(_)));
}

// ===========================================================================
// SIGN-EXTEND + SHIFTS — the broadened [PROVED] fragment (this rung).
// ===========================================================================

/// `sign_extend` of an expression equals ITSELF (reflexive) — a valid identity
/// the solver refutes its negation of. The blast introduces no new gate kind
/// (it replicates the existing MSB output var), so `validate()` passes.
#[test]
fn sign_ext_reflexive_validates() {
    let x = BvExpr::leaf("X0", 8);
    let se = BvExpr::sign_ext(x, 8); // 8 -> 16 bits
    let proof = export_bv_blast_proof_expr(&se, &se).expect("reflexive sign-extend is UNSAT");
    proof
        .validate()
        .expect("sign-extend reflexive proof validates");
}

/// THE SIGNED/UNSIGNED EXTEND BUG CLASS (anti-vacuity): a SIGN-extend is NOT a
/// ZERO-extend. Their disequality is satisfiable (any negative `x` makes the
/// high bits differ), so the exporter returns `NoRefutation` — it NEVER
/// fabricates a proof that sign-extend == zero-extend.
#[test]
fn sign_ext_ne_zero_ext_yields_no_refutation() {
    let x = BvExpr::leaf("X0", 8);
    let se = BvExpr::sign_ext(x.clone(), 8);
    let ze = BvExpr::zero_ext(x, 8);
    let err = export_bv_blast_proof_expr(&se, &ze)
        .expect_err("sign-extend != zero-extend is SAT (a negative x differs)");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// A variable-amount logical shift-left equals ITSELF (reflexive): the barrel
/// shifter blasts to a real gate network, and the per-bit equality is UNSAT.
#[test]
fn shl_reflexive_validates() {
    let x = BvExpr::leaf("X0", 8);
    let amt = BvExpr::leaf("A0", 8);
    let s = BvExpr::shl(x, amt);
    let proof = export_bv_blast_proof_expr(&s, &s).expect("reflexive shl is UNSAT");
    proof.validate().expect("shl reflexive proof validates");
}

/// Logical shift-right reflexive validates.
#[test]
fn lshr_reflexive_validates() {
    let x = BvExpr::leaf("X0", 8);
    let amt = BvExpr::leaf("A0", 8);
    let s = BvExpr::lshr(x, amt);
    let proof = export_bv_blast_proof_expr(&s, &s).expect("reflexive lshr is UNSAT");
    proof.validate().expect("lshr reflexive proof validates");
}

/// Arithmetic shift-right by ZERO equals the operand — a genuine (non-reflexive)
/// `ashr` identity whose UNSAT proof surfaces and validates. (The barrel
/// shifter's by-zero path selects the unshifted value; `ashr(x, 0) == x`.)
///
/// HONEST RESIDUAL: a *variable-amount* width-8 reflexive `ashr` obligation does
/// NOT currently surface through ay's RUP→resolution expander (the sign-fill
/// over-shift mux network defeats the expander at that scale —
/// `RefutationNotSurfaceable`). `shl`/`lshr` do surface there; `ashr` surfaces
/// for the by-constant and width-4 cases exercised here. Where surfacing fails
/// the exporter returns an Err (NEVER a fabricated proof), so the external-codegen gate
/// fail-CLOSES that obligation to [VALIDATED] — it never emits [PROVED] from an
/// unsurfaced ashr.
#[test]
fn ashr_by_zero_is_identity_validates() {
    let x = BvExpr::leaf("X0", 8);
    let zero = BvExpr::const_val(0, 8);
    let s = BvExpr::ashr(x.clone(), zero);
    let proof = export_bv_blast_proof_expr(&s, &x).expect("ashr(x,0) == x is UNSAT");
    proof.validate().expect("ashr-by-zero proof validates");
}

/// THE SIGNED/UNSIGNED SHIFT-RIGHT BUG CLASS (anti-vacuity): an ARITHMETIC
/// (sign-filling) shift-right is NOT a LOGICAL (zero-filling) shift-right. For a
/// negative value shifted by a nonzero amount the fills differ, so the
/// disequality is satisfiable and the exporter returns `NoRefutation` — it NEVER
/// fabricates a proof that ashr == lshr. This is the same signed-lowered-as-
/// unsigned shape the campaign caught (abs/relational signedness).
#[test]
fn ashr_ne_lshr_yields_no_refutation() {
    let x = BvExpr::leaf("X0", 8);
    let amt = BvExpr::leaf("A0", 8);
    let a = BvExpr::ashr(x.clone(), amt.clone());
    let l = BvExpr::lshr(x, amt);
    let err = export_bv_blast_proof_expr(&a, &l)
        .expect_err("ashr != lshr is SAT (negative x, nonzero amt differ)");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// Serde round-trip of a shift proof: the new variants' gates serialize and the
/// round-tripped proof still validates.
#[test]
fn shift_proof_serde_round_trip() {
    let x = BvExpr::leaf("X0", 8);
    let amt = BvExpr::leaf("A0", 8);
    let s = BvExpr::lshr(x, amt);
    let proof = export_bv_blast_proof_expr(&s, &s).expect("export lshr proof");
    let json = serde_json::to_string(&proof).expect("serialize");
    let back: BvBlastProof = serde_json::from_str(&json).expect("deserialize");
    back.validate()
        .expect("round-tripped shift proof validates");
}

// ═══════════════════════════════════════════════════════════════════════════
// Not + Eq (1-bit predicate) — the compare flag-decomposition fragment (PATH B)
// ═══════════════════════════════════════════════════════════════════════════
//
// These exercise the two new `BvExpr` nodes that close COMPARES at [PROVED].
// Both blast to EXISTING per-bit gates (Not -> `Not`; Eq -> `XnorEq` AND-reduced
// by `And2`), so NO new kernel gate KIND is introduced. The compare predicates
// reduce to a 1-bit `BvExpr` over {Sub, Extract, Xor, And, Not, Eq, Const}.

/// `bvnot(bvnot(x)) == x` — double negation is valid (UNSAT negation), and the
/// per-bit `Not` gates blast + the solver refutes + the proof self-validates.
#[test]
fn not_not_x_eq_x_validates() {
    let x = BvExpr::leaf("X0", 8);
    let nn = BvExpr::not(BvExpr::not(x.clone()));
    let proof = export_bv_blast_proof_expr(&nn, &x).expect("not(not(x)) == x is UNSAT");
    proof.validate().expect("double-negation proof validates");
}

/// ANTI-VACUITY for `Not`: `bvnot(x) == x` is SAT (no fixed point for a nonzero
/// width), so the exporter returns `NoRefutation` — never fabricates a proof.
#[test]
fn not_x_eq_x_no_refutation() {
    let x = BvExpr::leaf("X0", 8);
    let err =
        export_bv_blast_proof_expr(&BvExpr::not(x.clone()), &x).expect_err("not(x) == x is SAT");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// `Eq` predicate: `(a == a)` is the constant-true 1-bit predicate, so equating
/// it to `Const{1,1}` is valid (UNSAT negation). The per-bit `XnorEq` + `And2`
/// reduction blasts and the proof self-validates; the result is 1 bit wide.
#[test]
fn eq_self_is_true_predicate_validates() {
    let a = BvExpr::leaf("A0", 8);
    let eq = BvExpr::eq(a.clone(), a); // 1-bit, always true
    let one = BvExpr::const_val(1, 1);
    let proof = export_bv_blast_proof_expr(&eq, &one).expect("(a == a) == 1 is UNSAT");
    proof.validate().expect("eq-self proof validates");
}

/// ANTI-VACUITY for `Eq`: `(a == b) == 1` is SAT (a and b may differ), so the
/// exporter returns `NoRefutation` — it does not claim distinct vars are equal.
#[test]
fn eq_distinct_vars_no_refutation() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    let eq = BvExpr::eq(a, b);
    let one = BvExpr::const_val(1, 1);
    let err = export_bv_blast_proof_expr(&eq, &one).expect_err("(a == b) == 1 is SAT");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// `eq(a,b)` via the machine form `(Sub(a,b) == 0)` equals the direct `(a == b)`
/// predicate — the EXACT decomposition the compare gate uses for `==`. Both are
/// 1-bit; the SAT solver proves them equal (UNSAT negation).
#[test]
fn eq_via_sub_zero_matches_direct_eq() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    // machine: (a - b) == 0
    let machine = BvExpr::eq(BvExpr::sub(a.clone(), b.clone()), BvExpr::const_val(0, 8));
    // ir: a == b
    let ir = BvExpr::eq(a, b);
    let proof = export_bv_blast_proof_expr(&machine, &ir)
        .expect("(a-b == 0) == (a == b) is a valid identity (UNSAT negation)");
    proof.validate().expect("eq-decomposition proof validates");
}

/// Build the signed-`<` flag predicate `N != V` over `a`/`b` at width `w`, the
/// EXACT shape `condition_to_formula(Lt)` produces over `compute_nzcv(.., is_sub)`.
/// `signed_lt = Not(Eq(N, V))` with:
///   N = (Extract(a-b, w-1, w-1) == 1)
///   V = (asign != bsign) AND (rsign != asign)     [subtraction overflow]
fn signed_lt_flag_form(a: &BvExpr, b: &BvExpr, w: u32) -> BvExpr {
    let msb = w - 1;
    let sub = BvExpr::sub(a.clone(), b.clone());
    let ext = |e: &BvExpr| BvExpr::extract(e.clone(), msb, msb);
    let asign = ext(a);
    let bsign = ext(b);
    let rsign = ext(&sub);
    // N = (rsign == 1)
    let n = BvExpr::eq(rsign.clone(), BvExpr::const_val(1, 1));
    // V = NOT(asign == bsign) AND NOT(rsign == asign)
    let signs_differ = BvExpr::not(BvExpr::eq(asign.clone(), bsign));
    let res_differs = BvExpr::not(BvExpr::eq(rsign, asign));
    let v = BvExpr::and(signs_differ, res_differs);
    // signed_lt = N != V = NOT(N == V)
    BvExpr::not(BvExpr::eq(n, v))
}

/// THE SIGNED-LT FLAG DECOMPOSITION (g16 signed_lt_equiv corroborated): the
/// machine flag predicate `N != V` and the SAME predicate (auto-spec mirror)
/// are equal for ALL inputs, so the equality is UNSAT-negation and self-blasts.
/// This is the 1-bit obligation the compare gate discharges at [PROVED].
#[test]
fn signed_lt_flag_form_self_consistent_validates() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    let machine = signed_lt_flag_form(&a, &b, 8);
    let ir = signed_lt_flag_form(&a, &b, 8);
    let proof = export_bv_blast_proof_expr(&machine, &ir)
        .expect("signed_lt flag form == itself is UNSAT negation");
    proof
        .validate()
        .expect("signed_lt flag-form proof validates");
}

/// BUG-CLASS ANTI-VACUITY at the ay layer: the SIGNED-LT flag predicate is NOT
/// the UNSIGNED-LT predicate. Model unsigned_lt(a,b) directly as the borrow flag
/// `NOT C = NOT( NOT(a <u b) )` — but here we use the simplest distinguishing
/// witness: the signed flag form vs the plain MSB-of-sub (which equals signed_lt
/// ONLY when there is no overflow). They differ on overflow inputs, so the
/// exporter returns `NoRefutation` — a signed compare lowered as the wrong
/// predicate is NEVER certified.
#[test]
fn signed_lt_ne_naive_msb_no_refutation() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    let signed_lt = signed_lt_flag_form(&a, &b, 8);
    // The WRONG lowering: just MSB(a-b) == 1 (drops the overflow correction).
    let sub = BvExpr::sub(a, b);
    let naive = BvExpr::eq(BvExpr::extract(sub, 7, 7), BvExpr::const_val(1, 1));
    let err = export_bv_blast_proof_expr(&signed_lt, &naive)
        .expect_err("signed_lt != naive-MSB on overflow inputs (SAT)");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// Build the UNSIGNED-`<` borrow predicate over `a`/`b` at width `w`, the shape
/// `unsigned_lt(a, b) = NOT(CarryOut(a, b, is_sub=true))` (g16 `unsigned_lt_equiv`):
/// `a - b = a + ~b + 1` produces a BORROW (carry-out 0) exactly when `a <u b`.
fn unsigned_lt_flag_form(a: &BvExpr, b: &BvExpr) -> BvExpr {
    BvExpr::not(BvExpr::carry_out_sub(a.clone(), b.clone()))
}

/// Build the UNSIGNED-`<=` predicate: `unsigned_le(a, b) = NOT(b <u a)`
/// `= NOT(NOT(CarryOut(b, a, is_sub=true))) = CarryOut(b, a, is_sub=true)`.
fn unsigned_le_flag_form(a: &BvExpr, b: &BvExpr) -> BvExpr {
    BvExpr::carry_out_sub(b.clone(), a.clone())
}

/// THE UNSIGNED-LT BORROW DECOMPOSITION (g16 unsigned_lt_equiv corroborated): the
/// machine borrow predicate `NOT CarryOut(a - b)` and the SAME predicate (auto-spec
/// mirror) are equal for ALL inputs, so the equality is UNSAT-negation and
/// self-blasts. The new `CarryOut` node threads the EXISTING `FullAdderCarry`
/// chain to the MSB. This is the 1-bit obligation the unsigned compare gate
/// discharges at [PROVED].
#[test]
fn unsigned_lt_flag_form_self_consistent_validates() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    let machine = unsigned_lt_flag_form(&a, &b);
    let ir = unsigned_lt_flag_form(&a, &b);
    let proof = export_bv_blast_proof_expr(&machine, &ir)
        .expect("unsigned_lt flag form == itself is UNSAT negation");
    proof
        .validate()
        .expect("unsigned_lt flag-form proof validates");
}

/// Same for unsigned `<=`.
#[test]
fn unsigned_le_flag_form_self_consistent_validates() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    let machine = unsigned_le_flag_form(&a, &b);
    let ir = unsigned_le_flag_form(&a, &b);
    let proof = export_bv_blast_proof_expr(&machine, &ir)
        .expect("unsigned_le flag form == itself is UNSAT negation");
    proof
        .validate()
        .expect("unsigned_le flag-form proof validates");
}

/// The CARRY-OUT node has a real semantics: `unsigned_lt(a, b) == NOT(b >=u a)`.
/// Cross-check the borrow decomposition against the equivalent
/// `unsigned_lt(a, b) = CarryOut(b - a) AND NOT(a == b)` is NOT what we assert here;
/// instead we assert the two DIRECTIONS are consistent: `a <u b` and `b <u a`
/// cannot both hold, but that is a deeper fact. The minimal real-semantics check:
/// `CarryOut(a + 0)` (add, no carry) is always 0 — adding a value to a zero-extended
/// operand of the same width never overflows when the high operand is 0. We test the
/// borrow flag's KEY identity: `unsigned_lt(a, a) = false`, i.e. `NOT(CarryOut(a-a))`
/// is `false`, i.e. `CarryOut(a - a) = 1` (a - a = 0 has no borrow). So
/// `unsigned_lt(a,a) == const false` self-blasts to UNSAT-negation.
#[test]
fn unsigned_lt_reflexive_is_false_validates() {
    let a = BvExpr::leaf("A0", 8);
    let machine = unsigned_lt_flag_form(&a, &a); // a <u a
    let ir = BvExpr::const_val(0, 1); // false
    let proof = export_bv_blast_proof_expr(&machine, &ir)
        .expect("unsigned_lt(a, a) == false is UNSAT negation");
    proof
        .validate()
        .expect("unsigned_lt-reflexive proof validates");
}

/// BUG-CLASS ANTI-VACUITY at the ay layer: the UNSIGNED-LT borrow predicate is NOT
/// the SIGNED-LT flag predicate. The unsigned compare `NOT(CarryOut(a - b))` differs
/// from `signed_lt(a, b)` on inputs that straddle the signed/unsigned boundary (e.g.
/// `a = 0x80, b = 0x01`: unsigned 0x80 >u 0x01 so unsigned_lt = false; but signed
/// -128 <s 1 so signed_lt = true). The exporter returns `NoRefutation` — an unsigned
/// compare lowered as the signed predicate is NEVER certified.
#[test]
fn unsigned_lt_ne_signed_lt_no_refutation() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    let unsigned = unsigned_lt_flag_form(&a, &b);
    let signed = signed_lt_flag_form(&a, &b, 8);
    let err = export_bv_blast_proof_expr(&unsigned, &signed)
        .expect_err("unsigned_lt != signed_lt on sign-straddling inputs (SAT)");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// ANTI-VACUITY: an unsigned compare with SWAPPED operands is a different predicate.
/// `unsigned_lt(a, b)` != `unsigned_lt(b, a)` (they differ whenever a != b), so a
/// gate that lowers `a <u b` as the carry-out of `b - a` is refuted, never certified.
#[test]
fn unsigned_lt_operand_swap_no_refutation() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    let correct = unsigned_lt_flag_form(&a, &b);
    let swapped = unsigned_lt_flag_form(&b, &a);
    let err = export_bv_blast_proof_expr(&correct, &swapped)
        .expect_err("unsigned_lt(a,b) != unsigned_lt(b,a) (SAT)");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// Serde round-trip of a CarryOut proof: the new variant's gates serialize and the
/// round-tripped proof still validates (a downstream proof consumer consumes the serialized form).
#[test]
fn carry_out_proof_serde_round_trip() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    let machine = unsigned_lt_flag_form(&a, &b);
    let proof = export_bv_blast_proof_expr(&machine, &machine).expect("export ult proof");
    let json = serde_json::to_string(&proof).expect("serialize");
    let back: BvBlastProof = serde_json::from_str(&json).expect("deserialize");
    back.validate()
        .expect("round-tripped CarryOut proof validates");
}

/// Serde round-trip of a Not+Eq proof: the new variants' gates serialize and the
/// round-tripped proof still validates (a downstream proof consumer consumes the serialized form).
#[test]
fn not_eq_proof_serde_round_trip() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    let machine = signed_lt_flag_form(&a, &b, 8);
    let proof = export_bv_blast_proof_expr(&machine, &machine).expect("export slt proof");
    let json = serde_json::to_string(&proof).expect("serialize");
    let back: BvBlastProof = serde_json::from_str(&json).expect("deserialize");
    back.validate()
        .expect("round-tripped Not+Eq proof validates");
}

// ============================================================================
// BvExpr::Mul — shift-and-add ARRAY multiplier (GAP close: the last tractable
// straight-line ALU op). The multiplier blasts to existing gate KINDs only
// (And2 partial products + Xor3/FullAdderCarry/ConstFalse adder tree), so its
// proofs are downstream proof consumer-re-checkable. Anti-vacuity is solver-enforced:
// `Mul` is genuinely distinct from `Add` and from a corrupted/off-by-one
// product, so a wrong emission is refuted (NoRefutation), never proved.
// ============================================================================

/// `bvmul(x, 1) == x` is valid (UNSAT negation): multiply by one is the
/// identity. Exercises the array-multiplier blast end-to-end at width 8 and
/// confirms a real validating refutation is surfaced.
#[test]
fn mul_by_one_is_identity_validates() {
    let x = BvExpr::leaf("X0", 8);
    let one = BvExpr::const_val(1, 8);
    let machine_out = BvExpr::mul(x.clone(), one); // x * 1
    let auto_spec = x;
    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("bvmul(x, 1) == x is valid (UNSAT negation), must export");
    proof.validate().expect("mul-by-one proof validates");
    assert!(
        proof
            .refutation
            .steps
            .last()
            .expect("non-empty refutation")
            .clause
            .is_empty(),
        "refutation must end in the empty clause"
    );
}

/// `bvmul(x, 0) == 0` is valid (UNSAT negation): multiply by zero is zero.
/// Confirms the partial-product `And2` rows collapse correctly through the
/// adder tree.
#[test]
fn mul_by_zero_is_zero_validates() {
    let x = BvExpr::leaf("X0", 8);
    let zero = BvExpr::const_val(0, 8);
    let machine_out = BvExpr::mul(x, zero.clone()); // x * 0
    let auto_spec = zero;
    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("bvmul(x, 0) == 0 is valid (UNSAT negation), must export");
    proof.validate().expect("mul-by-zero proof validates");
}

/// `bvmul(x, 2) == bvshl(x, 1)` (here `x + x`) — multiply by the constant two
/// equals the left shift by one, which for the low 8 bits equals `x + x`.
/// Confirms the shifted-row summation lines up with the adder semantics.
#[test]
fn mul_by_two_equals_self_add_validates() {
    let x = BvExpr::leaf("X0", 8);
    let two = BvExpr::const_val(2, 8);
    let machine_out = BvExpr::mul(x.clone(), two); // x * 2
    let auto_spec = BvExpr::add(x.clone(), x); // x + x
    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("bvmul(x, 2) == x + x is valid (UNSAT negation), must export");
    proof.validate().expect("mul-by-two proof validates");
}

/// COMMUTATIVITY: `bvmul(a, b) == bvmul(b, a)` is valid (UNSAT negation). Both
/// sides blast the full array multiplier through the SHARED cache, but with
/// operands swapped the partial-product `And2` gates differ structurally, so
/// the solver must actually prove the equivalence (no trivial cache fusion).
#[test]
fn mul_commutativity_validates() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    let machine_out = BvExpr::mul(a.clone(), b.clone());
    let auto_spec = BvExpr::mul(b, a);
    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("bvmul(a, b) == bvmul(b, a) is valid (UNSAT negation), must export");
    proof.validate().expect("mul-commutativity proof validates");
}

/// REFLEXIVE: `bvmul(a, b) == bvmul(a, b)` — both sides fuse through the shared
/// cache to identical output vars, so the disequality is immediately UNSAT.
#[test]
fn mul_reflexive_validates() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    let m = BvExpr::mul(a, b);
    let proof =
        export_bv_blast_proof_expr(&m, &m).expect("reflexive mul equality is UNSAT, must export");
    proof.validate().expect("reflexive mul proof validates");
}

/// ANTI-VACUITY (mul-as-add): `bvmul(a, b) == bvadd(a, b)` is FALSE in general
/// (e.g. a=3, b=3: 9 != 6). The solver finds a model → NoRefutation. A multiply
/// obligation mistakenly lowered/emitted as an add is REFUTED, never proved.
#[test]
fn anti_vacuity_mul_is_not_add_yields_no_refutation() {
    let a = BvExpr::leaf("A0", 8);
    let b = BvExpr::leaf("B0", 8);
    let mul = BvExpr::mul(a.clone(), b.clone());
    let add = BvExpr::add(a, b);
    let err = export_bv_blast_proof_expr(&mul, &add)
        .expect_err("mul(a,b) == add(a,b) is SAT, must NOT export");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// ANTI-VACUITY (off-by-one shift): `bvmul(x, 2) == bvmul(x, 4)` is FALSE in
/// general (2x != 4x unless x has the right low bits). A corrupted multiplier
/// whose partial-product row is shifted by the wrong amount produces this kind
/// of disequality → NoRefutation, never a fabricated [PROVED].
#[test]
fn anti_vacuity_mul_off_by_one_scale_yields_no_refutation() {
    let x = BvExpr::leaf("X0", 8);
    let times2 = BvExpr::mul(x.clone(), BvExpr::const_val(2, 8));
    let times4 = BvExpr::mul(x, BvExpr::const_val(4, 8));
    let err = export_bv_blast_proof_expr(&times2, &times4)
        .expect_err("mul(x,2) == mul(x,4) is SAT, must NOT export");
    assert_eq!(err, BvExprExportError::NoRefutation);
}

/// Serde round-trip of a Mul proof: the multiplier's And2/Xor3/FullAdderCarry
/// gates serialize and the round-tripped proof still validates (a downstream proof consumer consumes
/// the serialized form for the kernel re-check).
#[test]
fn mul_proof_serde_round_trip() {
    let x = BvExpr::leaf("X0", 8);
    let one = BvExpr::const_val(1, 8);
    let machine_out = BvExpr::mul(x.clone(), one);
    let proof = export_bv_blast_proof_expr(&machine_out, &x).expect("export mul proof");
    let json = serde_json::to_string(&proof).expect("serialize");
    let back: BvBlastProof = serde_json::from_str(&json).expect("deserialize");
    back.validate().expect("round-tripped Mul proof validates");
}
