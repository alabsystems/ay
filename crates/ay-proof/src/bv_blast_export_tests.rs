// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the structured BV bit-blast proof export.

use super::*;
use proptest::prelude::*;
use std::collections::BTreeSet;

/// `proof_isub_i32`-shaped: `not(bvsub(a,b) == bvsub(a,b))` is UNSAT and exports a
/// WELL-FORMED proof (every clause derived, chain ends in empty, no opaque trust).
#[test]
fn isub_identical_exports_wellformed_proof() {
    let obl = SliceObligation::identical(BvOp::Sub);
    let proof = export_bv_blast_proof(obl).expect("identical bvsub is UNSAT, must export");
    assert_eq!(proof.format_version, FORMAT_VERSION);
    assert_eq!(proof.obligation.op, BvOp::Sub);
    assert_eq!(proof.obligation.width, SLICE_WIDTH);
    // Contract: validate passes (chain sound, ends in empty clause).
    proof
        .validate()
        .expect("exported proof must be well-formed");
    assert_no_opaque_step(&proof);
    assert_refutation_ends_empty(&proof);
}

/// Same for `bvadd`: `not(bvadd(a,b) == bvadd(a,b))` is UNSAT.
#[test]
fn iadd_identical_exports_wellformed_proof() {
    let obl = SliceObligation::identical(BvOp::Add);
    let proof = export_bv_blast_proof(obl).expect("identical bvadd is UNSAT, must export");
    proof
        .validate()
        .expect("exported proof must be well-formed");
    assert_no_opaque_step(&proof);
    assert_refutation_ends_empty(&proof);
}

/// SAT / false obligation: `not(bvsub(a,b) == bvsub(b,a))` is SAT (b-a != a-b in
/// general), so export must return NoRefutation, NOT a bogus proof.
#[test]
fn sat_obligation_returns_no_refutation() {
    let obl = SliceObligation {
        width: SLICE_WIDTH,
        op: BvOp::Sub,
        lhs_args: [OperandRef::A, OperandRef::B],
        rhs_args: [OperandRef::B, OperandRef::A],
    };
    let err = export_bv_blast_proof(obl).expect_err("non-identical bvsub is SAT, must NOT export");
    assert!(
        matches!(err, BvBlastExportError::NoRefutation { .. }),
        "expected NoRefutation, got {err:?}"
    );
}

/// `bvadd(a,b)` vs `bvadd(b,a)`: also non-identical at the syntactic level, so the
/// producer (which only proves identical-operand) returns NoRefutation. (It does
/// not attempt to prove commutativity — that is outside the slice fragment.)
#[test]
fn add_commuted_returns_no_refutation() {
    let obl = SliceObligation {
        width: SLICE_WIDTH,
        op: BvOp::Add,
        lhs_args: [OperandRef::A, OperandRef::B],
        rhs_args: [OperandRef::B, OperandRef::A],
    };
    let err = export_bv_blast_proof(obl).expect_err("non-identical, producer must not export");
    assert!(matches!(err, BvBlastExportError::NoRefutation { .. }));
}

/// Out-of-range widths (0 and > MAX_WIDTH) are rejected with a typed error.
#[test]
fn wrong_width_rejected() {
    for width in [0, MAX_WIDTH + 1, u32::MAX] {
        let err = export_bv_blast_proof(SliceObligation::identical_at(BvOp::Sub, width))
            .expect_err("width outside 1..=MAX_WIDTH must be rejected");
        assert!(matches!(
            err,
            BvBlastExportError::UnsupportedWidth { got, max: MAX_WIDTH } if got == width
        ));
    }
}

/// The producer is width-parametric across 1..=MAX_WIDTH (the width-32
/// reflexivity slice was the historical shape, not a format limit): every op
/// exports a validating, opaque-step-free proof at boundary and interior
/// widths, including non-power-of-two.
#[test]
fn nonstandard_widths_export_and_validate() {
    for width in [1, 8, 20, SLICE_WIDTH, MAX_WIDTH] {
        for op in ALL_BV_OPS {
            let proof = export_bv_blast_proof(SliceObligation::identical_at(op, width))
                .unwrap_or_else(|e| panic!("{op:?} at width {width} must export: {e:?}"));
            assert_eq!(proof.obligation.width, width);
            proof
                .validate()
                .unwrap_or_else(|e| panic!("{op:?} at width {width} must validate: {e:?}"));
            assert_no_opaque_step(&proof);
            assert_refutation_ends_empty(&proof);
            // The disequality clause covers exactly `width` BitEq vars.
            let diseq = proof
                .clauses
                .iter()
                .find(|c| matches!(c.provenance, ClauseProvenance::Disequality))
                .expect("disequality clause present");
            assert_eq!(diseq.lits.len(), width as usize);
        }
    }
}

/// serde round-trip: a proof survives serialize -> deserialize unchanged and still
/// validates.
#[test]
fn serde_round_trip() {
    let proof = export_bv_blast_proof(SliceObligation::identical(BvOp::Sub)).expect("export ok");
    let json = serde_json::to_string(&proof).expect("serialize");
    let back: BvBlastProof = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(proof, back, "round-trip must be identity");
    back.validate().expect("deserialized proof still validates");
}

fn replay_limits_for(proof: &BvBlastProof) -> BvBlastValidateLimits {
    BvBlastValidateLimits {
        deadline: None,
        max_vars: proof.vars.len(),
        max_bit_lemmas: proof.bit_lemmas.len(),
        max_clauses: proof.clauses.len(),
        max_clause_literals: proof
            .clauses
            .iter()
            .map(|clause| clause.lits.len())
            .max()
            .unwrap_or(0),
        max_original_literals: proof.clauses.iter().map(|clause| clause.lits.len()).sum(),
        max_resolution_steps: proof.refutation.steps.len(),
        max_derived_literals: proof
            .refutation
            .steps
            .iter()
            .map(|step| step.clause.len())
            .sum(),
        max_work: u64::MAX,
    }
}

#[test]
fn bounded_replay_accepts_an_exported_certificate() {
    let proof = export_bv_blast_proof(SliceObligation::identical_at(BvOp::Sub, 8)).expect("export");
    proof
        .validate_with_limits(&replay_limits_for(&proof))
        .expect("a valid certificate must pass finite structural limits");
}

#[test]
fn bounded_replay_rejects_repeated_large_premise_work() {
    let mut proof =
        export_bv_blast_proof(SliceObligation::identical_at(BvOp::Add, 8)).expect("export");
    let repeated = proof
        .clauses
        .iter_mut()
        .find(|clause| matches!(clause.provenance, ClauseProvenance::BitLemmaCnf { .. }))
        .expect("gate clause");
    let original = repeated.lits.clone();
    for _ in 0..128 {
        repeated.lits.extend_from_slice(&original);
    }
    // Clause semantics and resolution are set-based, so repetition does not
    // invalidate the proof. It must nevertheless be charged before replay.
    proof
        .validate()
        .expect("duplicate literals preserve the clause set");

    let mut limits = replay_limits_for(&proof);
    limits.max_work = 64;
    assert!(matches!(
        proof.validate_with_limits(&limits),
        Err(BvBlastValidateError::ResourceLimit {
            resource: "validation work",
            ..
        })
    ));
}

#[test]
fn bounded_replay_rejects_an_already_expired_deadline() {
    let proof = export_bv_blast_proof(SliceObligation::identical_at(BvOp::Xor, 8)).expect("export");
    let mut limits = replay_limits_for(&proof);
    limits.deadline = Some(Instant::now());
    assert_eq!(
        proof.validate_with_limits(&limits),
        Err(BvBlastValidateError::DeadlineExceeded)
    );
}

#[test]
fn malformed_resolution_premise_arity_is_rejected_by_serde() {
    let proof = export_bv_blast_proof(SliceObligation::identical_at(BvOp::Xor, 2)).expect("export");
    let mut json = serde_json::to_value(proof).expect("serialize");
    json["refutation"]["steps"][0]["premises"] = serde_json::json!([0]);
    serde_json::from_value::<BvBlastProof>(json)
        .expect_err("the fixed `[u32; 2]` premise type must reject arity one");
}

#[test]
fn noncanonical_resolution_step_id_is_rejected() {
    let mut proof =
        export_bv_blast_proof(SliceObligation::identical_at(BvOp::Xor, 2)).expect("export");
    proof.refutation.steps[0].id = u32::MAX;
    assert!(matches!(
        proof.validate(),
        Err(BvBlastValidateError::NonCanonicalResolutionStepId { index: 0, .. })
    ));
}

fn small_native_certificate() -> BvBlastProof {
    export_bv_blast_proof(SliceObligation::identical_at(BvOp::Xor, 2)).expect("export")
}

#[test]
fn native_replay_rejects_unknown_version_and_noncanonical_lemma_id() {
    let mut wrong_version = small_native_certificate();
    wrong_version.format_version = FORMAT_VERSION + 1;
    assert!(matches!(
        wrong_version.validate(),
        Err(BvBlastValidateError::UnsupportedFormatVersion { .. })
    ));

    let mut wrong_id = small_native_certificate();
    wrong_id.bit_lemmas[0].id = u32::MAX;
    assert!(matches!(
        wrong_id.validate(),
        Err(BvBlastValidateError::NonCanonicalBitLemmaId { index: 0, .. })
    ));
}

#[test]
fn native_replay_rejects_double_definition_cycle_and_undefined_gate() {
    let mut double_definition = small_native_certificate();
    let mut duplicate = double_definition.bit_lemmas[0].clone();
    duplicate.id = double_definition.bit_lemmas.len() as u32;
    double_definition.bit_lemmas.push(duplicate);
    assert!(matches!(
        double_definition.validate(),
        Err(BvBlastValidateError::DuplicateGateOutput { .. })
    ));

    let mut cycle = small_native_certificate();
    cycle.bit_lemmas[0].ins[0] = cycle.bit_lemmas[0].out;
    assert!(matches!(
        cycle.validate(),
        Err(BvBlastValidateError::GateInputNotDefined { lemma: 0, .. })
    ));

    let mut undefined = small_native_certificate();
    let var = undefined.vars.roles.len() as u32;
    undefined.vars.roles.push(VarRole::Aux { bit: 0 });
    assert_eq!(
        undefined.validate(),
        Err(BvBlastValidateError::MissingGateDefinition { var })
    );
}

#[test]
fn native_replay_rejects_malformed_disequality_provenance() {
    let mut wrong_polarity = small_native_certificate();
    let disequality = wrong_polarity
        .clauses
        .iter_mut()
        .find(|clause| matches!(clause.provenance, ClauseProvenance::Disequality))
        .expect("disequality");
    disequality.lits[0].neg = false;
    assert!(matches!(
        wrong_polarity.validate(),
        Err(BvBlastValidateError::MalformedDisequality { .. })
    ));

    let mut missing = small_native_certificate();
    missing
        .clauses
        .iter_mut()
        .find(|clause| matches!(clause.provenance, ClauseProvenance::Disequality))
        .expect("disequality")
        .lits
        .pop();
    assert!(matches!(
        missing.validate(),
        Err(BvBlastValidateError::MalformedDisequality { .. })
    ));

    let mut extra_clause = small_native_certificate();
    let mut duplicate = extra_clause
        .clauses
        .iter()
        .find(|clause| matches!(clause.provenance, ClauseProvenance::Disequality))
        .expect("disequality")
        .clone();
    duplicate.id = extra_clause.clauses.len() as u32;
    extra_clause.clauses.push(duplicate);
    assert!(matches!(
        extra_clause.validate(),
        Err(BvBlastValidateError::MalformedDisequality { .. })
    ));
}

#[test]
fn native_replay_rejects_missing_extra_or_non_xnor_biteq() {
    let mut missing = small_native_certificate();
    let missing_position = missing
        .vars
        .roles
        .iter()
        .position(|role| matches!(role, VarRole::BitEq { bit: 1 }))
        .expect("BitEq bit 1");
    missing.vars.roles[missing_position] = VarRole::Aux { bit: 1 };
    assert!(matches!(
        missing.validate(),
        Err(BvBlastValidateError::MalformedBitEqLayout { .. })
    ));

    let mut extra = small_native_certificate();
    let extra_var = extra.vars.roles.len() as u32;
    extra.vars.roles.push(VarRole::BitEq { bit: 2 });
    extra.bit_lemmas.push(BitLemma {
        id: extra.bit_lemmas.len() as u32,
        kind: BitLemmaKind::ConstFalse,
        out: extra_var,
        ins: Vec::new(),
    });
    assert!(matches!(
        extra.validate(),
        Err(BvBlastValidateError::MalformedBitEqLayout { .. })
    ));

    let mut wrong_gate = small_native_certificate();
    let bit_eq_var = wrong_gate
        .vars
        .roles
        .iter()
        .position(|role| matches!(role, VarRole::BitEq { bit: 0 }))
        .expect("BitEq bit 0") as u32;
    let lemma = wrong_gate
        .bit_lemmas
        .iter_mut()
        .find(|lemma| lemma.out == bit_eq_var)
        .expect("BitEq definition");
    lemma.kind = BitLemmaKind::And2;
    assert!(matches!(
        wrong_gate.validate(),
        Err(BvBlastValidateError::MalformedBitEqLayout { .. })
    ));
}

/// The disequality clause must be present exactly once and reference one ¬BitEq per
/// output bit.
#[test]
fn disequality_clause_shape() {
    let proof = export_bv_blast_proof(SliceObligation::identical(BvOp::Add)).expect("export");
    let diseqs: Vec<_> = proof
        .clauses
        .iter()
        .filter(|c| matches!(c.provenance, ClauseProvenance::Disequality))
        .collect();
    assert_eq!(diseqs.len(), 1, "exactly one disequality clause");
    let diseq = diseqs[0];
    assert_eq!(diseq.lits.len(), SLICE_WIDTH as usize);
    assert!(
        diseq.lits.iter().all(|l| l.neg),
        "all literals negated BitEq"
    );
    for lit in &diseq.lits {
        assert!(matches!(
            proof.vars.roles[lit.var as usize],
            VarRole::BitEq { .. }
        ));
    }
}

/// Tampering the proof (drop the final empty clause) must be caught by validate.
#[test]
fn tampered_proof_fails_validation() {
    let mut proof = export_bv_blast_proof(SliceObligation::identical(BvOp::Sub)).expect("export");
    // Remove the last (empty-clause) step.
    proof.refutation.steps.pop();
    let err = proof.validate().expect_err("truncated chain must fail");
    assert!(
        matches!(err, BvBlastValidateError::NotEmptyClause(_)),
        "expected NotEmptyClause, got {err:?}"
    );
}

/// Tampering a resolution step's clause must be caught.
#[test]
fn tampered_step_clause_fails_validation() {
    let mut proof = export_bv_blast_proof(SliceObligation::identical(BvOp::Add)).expect("export");
    // Corrupt the first resolution step's clause.
    if let Some(step) = proof.refutation.steps.first_mut() {
        step.clause.push(Lit::pos(0));
    }
    let err = proof.validate().expect_err("corrupt step must fail");
    assert!(
        matches!(err, BvBlastValidateError::ResolutionMismatch { .. }),
        "expected ResolutionMismatch, got {err:?}"
    );
}

/// Finding 5 regression: the `Xor3` gate CNF must be satisfied by *exactly* the 8
/// rows with `o = a⊕b⊕c` and reject all 8 rows with `o = ¬(a⊕b⊕c)`. The earlier
/// implementation emitted the inverted gate (`o = ¬(a⊕b⊕c)`).
#[test]
fn xor3_cnf_encodes_xor_not_its_negation() {
    // Distinct vars o=0, a=1, b=2, c=3.
    let cnf = tseitin_clauses(BitLemmaKind::Xor3, 0, &[1, 2, 3]);
    assert_eq!(cnf.len(), 8, "xor3 has 8 Tseitin clauses");
    let sat = |row: u8, clause: &[Lit]| {
        // bit i of `row` is the value of var i (o,a,b,c).
        clause.iter().any(|l| {
            let v = (row >> l.var) & 1 == 1;
            v != l.neg
        })
    };
    for row in 0u8..16 {
        let o = row & 1 == 1;
        let a = (row >> 1) & 1 == 1;
        let b = (row >> 2) & 1 == 1;
        let c = (row >> 3) & 1 == 1;
        let all_sat = cnf.iter().all(|cl| sat(row, cl));
        assert_eq!(
            all_sat,
            o == (a ^ b ^ c),
            "row o={o} a={a} b={b} c={c}: CNF must accept iff o=a^b^c"
        );
    }
}

/// `FullAdderCarry` gate CNF must encode majority(a,b,c) (verified exhaustively).
#[test]
fn majority_cnf_encodes_majority() {
    let cnf = tseitin_clauses(BitLemmaKind::FullAdderCarry, 0, &[1, 2, 3]);
    let sat = |row: u8, clause: &[Lit]| {
        clause.iter().any(|l| {
            let v = (row >> l.var) & 1 == 1;
            v != l.neg
        })
    };
    for row in 0u8..16 {
        let o = row & 1 == 1;
        let a = (row >> 1) & 1 == 1;
        let b = (row >> 2) & 1 == 1;
        let c = (row >> 3) & 1 == 1;
        let maj = usize::from(a) + usize::from(b) + usize::from(c) >= 2;
        let all_sat = cnf.iter().all(|cl| sat(row, cl));
        assert_eq!(
            all_sat,
            o == maj,
            "row {row}: CNF must accept iff o=maj(a,b,c)"
        );
    }
}

/// `XnorEq(l, l)` (the shared-output equality gate) collapses to the two units
/// `(e ∨ ¬l)` and `(e ∨ l)`; no tautologies survive.
#[test]
fn xnoreq_self_collapses_to_two_units() {
    // e=0, l=1 (input repeated).
    let cnf = tseitin_clauses(BitLemmaKind::XnorEq, 0, &[1, 1]);
    assert_eq!(cnf.len(), 2, "XnorEq(l,l) has 2 non-tautological clauses");
    let has = |lits: &[Lit]| {
        cnf.iter().any(|cl| {
            let a: BTreeSet<_> = cl.iter().copied().collect();
            let b: BTreeSet<_> = lits.iter().copied().collect();
            a == b
        })
    };
    assert!(has(&[Lit::pos(0), Lit::neg(1)]), "(e ∨ ¬l)");
    assert!(has(&[Lit::pos(0), Lit::pos(1)]), "(e ∨ l)");
}

/// The shared-output property: both sides bit-blast to the SAME output vars, so the
/// proof carries NO `BitAgreement` provenance and `L_i = R_i` is variable identity.
#[test]
fn no_agreement_axiom_and_outputs_shared() {
    for op in [BvOp::Add, BvOp::Sub] {
        let proof = export_bv_blast_proof(SliceObligation::identical(op)).expect("export");
        // Every clause is either a checked gate CNF clause or the lone disequality.
        for cl in &proof.clauses {
            assert!(
                matches!(
                    cl.provenance,
                    ClauseProvenance::BitLemmaCnf { .. } | ClauseProvenance::Disequality
                ),
                "no provenance category other than BitLemmaCnf/Disequality may exist"
            );
        }
        // There is exactly one output role per bit (shared L_i ≡ R_i), never a
        // separate LhsOut/RhsOut pair.
        let outs = proof
            .vars
            .roles
            .iter()
            .filter(|r| matches!(r, VarRole::Out { .. }))
            .count();
        assert_eq!(
            outs, SLICE_WIDTH as usize,
            "exactly one shared output var per bit"
        );
    }
}

/// Finding 2/3 adversarial: a `BitLemmaCnf` clause whose literals do NOT match the
/// cited lemma's gate semantics must be REJECTED by `validate()`, even though it
/// cites an in-range lemma. (Previously validate only range-checked the index.)
#[test]
fn fabricated_leaf_clause_with_valid_provenance_tag_is_rejected() {
    let mut proof = export_bv_blast_proof(SliceObligation::identical(BvOp::Add)).expect("export");
    // Find a BitLemmaCnf clause and corrupt one of its literals while keeping the
    // (in-range, real) provenance tag.
    let idx = proof
        .clauses
        .iter()
        .position(|c| matches!(c.provenance, ClauseProvenance::BitLemmaCnf { .. }))
        .expect("at least one gate clause");
    // Flip the polarity of the first literal: this is no longer a Tseitin clause of
    // the gate, but the provenance still names a valid lemma.
    proof.clauses[idx].lits[0] = proof.clauses[idx].lits[0].negated();
    let err = proof
        .validate()
        .expect_err("a clause that contradicts its cited gate must be rejected");
    assert!(
        matches!(err, BvBlastValidateError::ClauseNotEntailed { .. }),
        "expected ClauseNotEntailed, got {err:?}"
    );
}

/// Finding 2/3 adversarial: re-pointing a clause's provenance at a DIFFERENT (wrong)
/// lemma must be rejected, because the clause is not a Tseitin clause of that lemma.
#[test]
fn mis_cited_provenance_is_rejected() {
    let mut proof = export_bv_blast_proof(SliceObligation::identical(BvOp::Sub)).expect("export");
    // Take a clause from some gate and re-point it at a structurally different lemma
    // (a ConstTrue/ConstFalse unit clause cannot match a 3-input Xor3 clause).
    let const_lemma = proof
        .bit_lemmas
        .iter()
        .position(|l| matches!(l.kind, BitLemmaKind::ConstTrue | BitLemmaKind::ConstFalse))
        .expect("subtraction injects a ConstTrue carry-in") as u32;
    let xor_clause_idx = proof
        .clauses
        .iter()
        .position(|c| {
            matches!(c.provenance, ClauseProvenance::BitLemmaCnf { lemma }
                if matches!(proof.bit_lemmas[lemma as usize].kind, BitLemmaKind::Xor3))
        })
        .expect("an Xor3 clause exists");
    proof.clauses[xor_clause_idx].provenance = ClauseProvenance::BitLemmaCnf { lemma: const_lemma };
    let err = proof
        .validate()
        .expect_err("mis-cited provenance must be rejected");
    assert!(
        matches!(err, BvBlastValidateError::ClauseNotEntailed { .. }),
        "expected ClauseNotEntailed, got {err:?}"
    );
}

/// Every emitted `BitLemmaCnf` clause must genuinely be a Tseitin clause of its
/// cited gate — i.e. the honest producer's output passes the strict validator.
#[test]
fn all_emitted_leaf_clauses_match_their_gate() {
    for op in [BvOp::Add, BvOp::Sub] {
        let proof = export_bv_blast_proof(SliceObligation::identical(op)).expect("export");
        for cl in &proof.clauses {
            if let ClauseProvenance::BitLemmaCnf { lemma } = cl.provenance {
                let lem = &proof.bit_lemmas[lemma as usize];
                let generated = tseitin_clauses(lem.kind, lem.out, &lem.ins);
                let lit_set: BTreeSet<_> = cl.lits.iter().copied().collect();
                assert!(
                    generated.iter().any(|g| {
                        let gs: BTreeSet<_> = g.iter().copied().collect();
                        gs == lit_set
                    }),
                    "clause {} not entailed by its {:?} gate",
                    cl.id,
                    lem.kind
                );
            }
        }
    }
}

proptest! {
    /// For both ops, the identical-operand obligation always exports and validates.
    #[test]
    fn prop_identical_always_validates(op_is_sub in any::<bool>()) {
        let op = if op_is_sub { BvOp::Sub } else { BvOp::Add };
        let proof = export_bv_blast_proof(SliceObligation::identical(op))
            .expect("identical obligation must export");
        prop_assert!(proof.validate().is_ok());
        prop_assert!(no_opaque_step(&proof));
        prop_assert!(proof.refutation.steps.last().map(|s| s.clause.is_empty()).unwrap_or(false));
    }

    /// Any non-identical operand combination (for either op) is rejected with
    /// NoRefutation — never a bogus proof.
    #[test]
    fn prop_non_identical_never_exports(
        op_is_sub in any::<bool>(),
        l0 in any::<bool>(), l1 in any::<bool>(),
        r0 in any::<bool>(), r1 in any::<bool>(),
    ) {
        let to_ref = |b| if b { OperandRef::A } else { OperandRef::B };
        let lhs = [to_ref(l0), to_ref(l1)];
        let rhs = [to_ref(r0), to_ref(r1)];
        prop_assume!(lhs != rhs);
        let op = if op_is_sub { BvOp::Sub } else { BvOp::Add };
        let obl = SliceObligation { width: SLICE_WIDTH, op, lhs_args: lhs, rhs_args: rhs };
        let res = export_bv_blast_proof(obl);
        let is_no_ref = matches!(res, Err(BvBlastExportError::NoRefutation { .. }));
        prop_assert!(is_no_ref, "non-identical operands must yield NoRefutation");
    }

    /// serde round-trip holds for both ops.
    #[test]
    fn prop_serde_round_trip(op_is_sub in any::<bool>()) {
        let op = if op_is_sub { BvOp::Sub } else { BvOp::Add };
        let proof = export_bv_blast_proof(SliceObligation::identical(op)).expect("export");
        let json = serde_json::to_string(&proof).expect("ser");
        let back: BvBlastProof = serde_json::from_str(&json).expect("de");
        prop_assert_eq!(proof, back);
    }
}

// ---- helpers -------------------------------------------------------------------

fn no_opaque_step(proof: &BvBlastProof) -> bool {
    // The ResRule enum has only Resolution; this is a belt-and-suspenders check that
    // every recorded step is a resolution step (no trust can be represented at all).
    proof
        .refutation
        .steps
        .iter()
        .all(|s| matches!(s.rule, ResRule::Resolution))
}

fn assert_no_opaque_step(proof: &BvBlastProof) {
    assert!(no_opaque_step(proof), "no step may be opaque/trust");
}

fn assert_refutation_ends_empty(proof: &BvBlastProof) {
    let last = proof.refutation.steps.last().expect("non-empty refutation");
    assert!(
        last.clause.is_empty(),
        "refutation must end in the empty clause"
    );
}

// ---- shift fragment (barrel shifter) -------------------------------------------

const ALL_BV_OPS: [BvOp; 8] = [
    BvOp::Add,
    BvOp::Sub,
    BvOp::Xor,
    BvOp::And,
    BvOp::Or,
    BvOp::Shl,
    BvOp::Lshr,
    BvOp::Ashr,
];

/// Every op (including the barrel-shifter shifts) exports an identical-operand
/// proof that validates, ends in the empty clause, has no opaque step, and whose
/// every emitted leaf clause genuinely matches its gate's Tseitin CNF.
#[test]
fn all_ops_identical_export_validate_and_match_gates() {
    for op in ALL_BV_OPS {
        let proof = export_bv_blast_proof(SliceObligation::identical(op))
            .unwrap_or_else(|e| panic!("{op:?} identical must export: {e:?}"));
        proof
            .validate()
            .unwrap_or_else(|e| panic!("{op:?} proof must validate: {e:?}"));
        assert_no_opaque_step(&proof);
        assert_refutation_ends_empty(&proof);
        for cl in &proof.clauses {
            if let ClauseProvenance::BitLemmaCnf { lemma } = cl.provenance {
                let lem = &proof.bit_lemmas[lemma as usize];
                let generated = tseitin_clauses(lem.kind, lem.out, &lem.ins);
                let lit_set: BTreeSet<_> = cl.lits.iter().copied().collect();
                assert!(
                    generated
                        .iter()
                        .any(|g| g.iter().copied().collect::<BTreeSet<_>>() == lit_set),
                    "{op:?}: clause {} not entailed by its {:?} gate",
                    cl.id,
                    lem.kind
                );
            }
        }
    }
}

/// SMT-LIB reference shift semantics at width 32 (over-shift saturates).
fn ref_shift(op: BvOp, a: u32, b: u32) -> u32 {
    match op {
        BvOp::Shl => {
            if b >= 32 {
                0
            } else {
                a << b
            }
        }
        BvOp::Lshr => {
            if b >= 32 {
                0
            } else {
                a >> b
            }
        }
        BvOp::Ashr => {
            if b >= 32 {
                if a >> 31 == 1 {
                    u32::MAX
                } else {
                    0
                }
            } else {
                ((a as i32) >> b) as u32
            }
        }
        _ => unreachable!("ref_shift only for shift ops"),
    }
}

/// Simulate the proof's gate network on concrete inputs `a`, `b` and read back the
/// 32-bit result from the `Out` bits. Inputs are driven from `InputA`/`InputB`
/// roles; gates are evaluated in build order (topological) via [`gate_eval`].
fn simulate(proof: &BvBlastProof, a: u32, b: u32) -> u32 {
    let mut val = vec![false; proof.vars.len()];
    for (i, role) in proof.vars.roles.iter().enumerate() {
        match *role {
            VarRole::InputA { bit } => val[i] = (a >> bit) & 1 == 1,
            VarRole::InputB { bit } => val[i] = (b >> bit) & 1 == 1,
            _ => {}
        }
    }
    for lem in &proof.bit_lemmas {
        let ins: Vec<bool> = lem.ins.iter().map(|&x| val[x as usize]).collect();
        val[lem.out as usize] = gate_eval(lem.kind, &ins).expect("arity matches gate");
    }
    let mut out = 0u32;
    for (i, role) in proof.vars.roles.iter().enumerate() {
        if let VarRole::Out { bit } = *role {
            if val[i] {
                out |= 1u32 << bit;
            }
        }
    }
    out
}

/// Width-parametric SMT-LIB reference semantics (values masked to `w` bits;
/// over-shift saturates; ashr fills with the width-`w` sign bit).
fn ref_op_at(op: BvOp, a: u64, b: u64, w: u32) -> u64 {
    let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
    let (a, b) = (a & mask, b & mask);
    let sign = (a >> (w - 1)) & 1 == 1;
    let r = match op {
        BvOp::Add => a.wrapping_add(b),
        BvOp::Sub => a.wrapping_sub(b),
        BvOp::Xor => a ^ b,
        BvOp::And => a & b,
        BvOp::Or => a | b,
        BvOp::Shl => {
            if b >= u64::from(w) {
                0
            } else {
                a << b
            }
        }
        BvOp::Lshr => {
            if b >= u64::from(w) {
                0
            } else {
                a >> b
            }
        }
        BvOp::Ashr => {
            if b >= u64::from(w) {
                if sign {
                    mask
                } else {
                    0
                }
            } else if sign {
                // Sign-extend within w bits, then shift arithmetically.
                (a >> b) | (mask & !(mask >> b))
            } else {
                a >> b
            }
        }
    };
    r & mask
}

/// Width-parametric gate-network simulation (width comes from the proof's
/// obligation; result read back from the `Out` bits, LSB-first).
fn simulate_at(proof: &BvBlastProof, a: u64, b: u64) -> u64 {
    let mut val = vec![false; proof.vars.len()];
    for (i, role) in proof.vars.roles.iter().enumerate() {
        match *role {
            VarRole::InputA { bit } => val[i] = (a >> bit) & 1 == 1,
            VarRole::InputB { bit } => val[i] = (b >> bit) & 1 == 1,
            _ => {}
        }
    }
    for lem in &proof.bit_lemmas {
        let ins: Vec<bool> = lem.ins.iter().map(|&x| val[x as usize]).collect();
        val[lem.out as usize] = gate_eval(lem.kind, &ins).expect("arity matches gate");
    }
    let mut out = 0u64;
    for (i, role) in proof.vars.roles.iter().enumerate() {
        if let VarRole::Out { bit } = *role {
            if val[i] {
                out |= 1u64 << bit;
            }
        }
    }
    out
}

/// At non-power-of-two and maximum widths, every op's gate network computes the
/// correct masked SMT-LIB semantics — including barrel-shifter over-shift
/// saturation for amounts in `[w, 2^ceil(log2(w)))`, which at non-power-of-two
/// widths carry no dedicated overflow bit and must saturate through the layered
/// rewires alone.
#[test]
fn width_parametric_gate_networks_match_reference_semantics() {
    for width in [20u32, 64u32] {
        let mask = if width == 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        let values = [
            0u64,
            1,
            2,
            3,
            mask,
            mask >> 1,
            1u64 << (width - 1),
            0x1234_5678_9ABC_DEF0 & mask,
        ];
        // Includes in-range amounts, w-1/w/w+1 boundary, and the tricky
        // no-high-bit over-shift band for width 20 (e.g. 21..31).
        let shifts = [
            0u64,
            1,
            7,
            u64::from(width) - 1,
            u64::from(width),
            u64::from(width) + 1,
            27,
            63,
            mask,
        ];
        for op in ALL_BV_OPS {
            let proof = export_bv_blast_proof(SliceObligation::identical_at(op, width))
                .expect("export at parametric width");
            let is_shift = matches!(op, BvOp::Shl | BvOp::Lshr | BvOp::Ashr);
            let bs: &[u64] = if is_shift { &shifts } else { &values };
            for &a in &values {
                for &b in bs {
                    let got = simulate_at(&proof, a, b);
                    let want = ref_op_at(op, a, b, width);
                    assert_eq!(
                        got, want,
                        "{op:?} width {width}: a={a:#x} b={b:#x} -> got {got:#x} want {want:#x}"
                    );
                }
            }
        }
    }
}

/// The barrel shifter is not just deterministic — it computes the correct SMT-LIB
/// shift, including over-shift saturation (>= width) and the ashr sign-fill. This
/// is the semantic guarantee the identical-operand obligation alone cannot give.
#[test]
fn barrel_shifter_matches_reference_semantics() {
    let values = [
        0u32,
        1,
        2,
        3,
        0x8000_0000,
        0xFFFF_FFFF,
        0x7FFF_FFFF,
        0x1234_5678,
        0xDEAD_BEEF,
    ];
    let shifts = [0u32, 1, 2, 7, 15, 16, 31, 32, 33, 63, u32::MAX];
    for op in [BvOp::Shl, BvOp::Lshr, BvOp::Ashr] {
        let proof = export_bv_blast_proof(SliceObligation::identical(op)).expect("export");
        for &a in &values {
            for &b in &shifts {
                let got = simulate(&proof, a, b);
                let want = ref_shift(op, a, b);
                assert_eq!(
                    got, want,
                    "{op:?}: a={a:#010x} b={b} -> got {got:#010x} want {want:#010x}"
                );
            }
        }
    }
}
