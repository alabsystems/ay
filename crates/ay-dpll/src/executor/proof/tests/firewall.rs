// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// End-to-end (#8419 / trust_count→0): a datatype constructor-distinctness
/// UNSAT emits a checker-validated `DatatypeDistinct` lemma, NOT a bare
/// `trust` step. The native checker accepts the retained proof. The pinned
/// external Alethe calculus still has no rule for this lemma, so the separate
/// strict-wire publication policy is covered by the wire-gap tests and must
/// decline rather than confuse native replay with external surfaceability.
/// Regression guard for the finalize-time `promote_datatype_distinct_lemmas`
/// promotion + registry-backed strict validation.
#[test]
fn test_datatype_distinct_lemma_validated_not_trust_end_to_end() {
    // REPINNED after c141d3b80 (fix(proof): harden arithmetic proof
    // publication) — verified by running the direct-pigeonhole sibling at
    // c141d3b80 (fails) and its parent b5e2523b2 (passes); this test fails by
    // the identical mechanism. That commit's `unsat_proof_has_known_wire_gap`
    // screen makes `:check-proofs-strict true` refuse any verdict whose
    // Alethe rendering needs an honest `hole` (dt_distinct has no external
    // rule), BY DESIGN. The surviving contract — the lemma is natively
    // VALIDATED, not trust — is pinned here without the strict-wire option
    // and proven with the datatype-aware strict checker itself; the
    // strict-wire decline is pinned in
    // `test_datatype_distinct_lemma_strict_wire_policy_fail_closes`.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_DT)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (= c red))
        (assert (= c green))
        (check-sat)
    "#;

    let commands = parse(input).expect("datatype script parses");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("datatype script executes");

    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced");
    exec.check_proof_strict_with_datatypes(proof)
        .expect("datatype-distinctness proof must replay in the native strict checker");

    // The constructor-distinctness conflict lemma must carry the
    // strict-checkable `DatatypeDistinct` kind (promoted from `Generic` at
    // finalization), not a trust fallback.
    let has_dt_distinct = proof.steps.iter().any(|s| {
        matches!(
            s,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::DatatypeDistinct,
                ..
            }
        )
    });
    assert!(
        has_dt_distinct,
        "expected a DatatypeDistinct theory lemma in the datatype proof"
    );

    // The native strict checker must see no terminal trust.
    let report = ay_proof::terminal_trust_report(proof);
    assert!(
        !report.has_terminal_trust(),
        "datatype-distinctness proof must have no terminal trust, got {report:?}"
    );

    // "Validated, not trust", proven by the validator itself: the
    // datatype-aware strict checker accepts the retained native proof.
    exec.check_proof_strict_with_datatypes(proof)
        .expect("the DatatypeDistinct lemma must validate strictly");
}

/// The post-c141d3b80 strict-wire contract, proven with the publication
/// funnel itself: `:check-proofs-strict true` refuses the same natively
/// validated refutation because its Alethe rendering requires an honest
/// `hole`, and the artifact is revoked rather than half-disclosed.
#[test]
fn test_datatype_distinct_lemma_strict_wire_policy_fail_closes() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_DT)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (= c red))
        (assert (= c green))
        (check-sat)
    "#;

    let commands = parse(input).expect("datatype script parses");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("datatype script executes");

    assert_eq!(outputs, vec!["unknown"]);
    assert!(
        exec.last_proof().is_none(),
        "a strict-wire-declined verdict must not expose the rejected artifact"
    );
}

/// End-to-end (formal-verification half (1), datatype theory): the runtime
/// automatically emits a verified-firewall Lean proof for the datatype
/// distinctness lemma — the import-the-verified-theorem shape, generated (not
/// hand-written). The generator's output is separately confirmed to `lake build`
/// and kernel-check (axioms ⊆ {propext, Quot.sound}); this guards the runtime
/// wiring + emitted structure.
#[test]
fn test_runtime_emits_datatype_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_DT)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (= c red))
        (assert (= c green))
        (check-sat)
    "#;
    let commands = parse(input).expect("datatype script parses");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("datatype script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        !emitted.is_empty(),
        "runtime must emit a firewall Lean proof for the dt_distinct lemma"
    );
    let lean = &emitted[0];
    for needle in [
        "import AySoundness.Firewall",
        "firewall_combined_unsat",
        "inductive T where",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "emitted Lean missing: {needle}");
    }
}

/// End-to-end (formal-verification half (1), LINEAR ARITHMETIC theory): the
/// runtime emits a verified-firewall Lean proof for an `la_generic` bound
/// conflict (`x ≤ 1 ∧ x ≥ 2 ⊢ ⊥`). The generator's output is separately
/// confirmed to `lake build` and kernel-check (`omega`-discharged validity,
/// axioms ⊆ {propext, Quot.sound}).
#[test]
fn test_runtime_emits_lia_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (<= x 1))
        (assert (>= x 2))
        (check-sat)
    "#;
    let commands = parse(input).expect("LIA script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("LIA script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        !emitted.is_empty(),
        "runtime must emit a firewall Lean proof for the la_generic lemma"
    );
    let lean = &emitted[0];
    for needle in [
        "abbrev Val := Nat → Int",
        "omega",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "emitted LIA Lean missing: {needle}");
    }
}

/// End-to-end (formal-verification half (1), EUF theory): the runtime emits a
/// verified-firewall Lean proof for an `eq_transitive` conflict
/// (`a=b ∧ b=c ∧ a≠c ⊢ ⊥`). Generator output separately confirmed to `lake
/// build` + kernel-check (`omega` validity, axioms ⊆ {propext, Quot.sound}).
#[test]
fn test_runtime_emits_euf_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
        (check-sat)
    "#;
    let commands = parse(input).expect("EUF script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("EUF script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        !emitted.is_empty(),
        "runtime must emit a firewall Lean proof for the eq_transitive lemma"
    );
    let lean = &emitted[0];
    for needle in [
        "abbrev Val := Nat → Nat",
        "omega",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(lean.contains(needle), "emitted EUF Lean missing: {needle}");
    }
}

/// End-to-end (formal-verification half (1), EUF CONGRUENCE — first
/// function-model theory): the runtime emits a verified-firewall Lean proof for
/// an `eq_congruent` conflict (`a=b ∧ f a ≠ f b ⊢ ⊥`). Generator output
/// separately confirmed to `lake build` + kernel-check (`simp`-congruence
/// validity over a `(valuation × function)` model, axioms ⊆ {propext,
/// Quot.sound}).
#[test]
fn test_runtime_emits_euf_congruence_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
    "#;
    let commands = parse(input).expect("EUF congruence script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        !emitted.is_empty(),
        "runtime must emit a firewall Lean proof for the eq_congruent lemma"
    );
    let lean = &emitted[0];
    for needle in [
        "abbrev Val := (Nat → Nat) × (Nat → Nat)",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(
            lean.contains(needle),
            "emitted congruence Lean missing: {needle}"
        );
    }
}

/// End-to-end (formal-verification half (1), EUF PREDICATE-CONGRUENCE — fifth
/// theory): the runtime emits a verified-firewall Lean proof for an
/// `eq_congruent_pred` conflict (`a=b ∧ P a ∧ ¬P b ⊢ ⊥`). Generator output
/// separately confirmed to `lake build` + kernel-check (axioms ⊆ {propext,
/// Quot.sound}).
#[test]
fn test_runtime_emits_euf_pred_congruence_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (assert (P a))
        (assert (not (P b)))
        (check-sat)
    "#;
    let commands = parse(input).expect("pred-congruence script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        !emitted.is_empty(),
        "runtime must emit a firewall Lean proof for the eq_congruent_pred lemma"
    );
    let lean = &emitted[0];
    for needle in [
        "abbrev Val := (Nat → Nat) × (Nat → Bool)",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(
            lean.contains(needle),
            "emitted pred-cong Lean missing: {needle}"
        );
    }
}

/// End-to-end (formal-verification half (1), ARRAY read-over-write-neg — sixth
/// theory): the runtime emits a verified-firewall Lean proof for a
/// `read_over_write_neg` conflict (`i≠j ∧ select(store a i v) j ≠ select a j ⊢
/// ⊥`). The emitter reconstructs the tautological `(i=j) ∨ (…)` lemma from the
/// unit's select/store structure. Generator output separately confirmed to
/// `lake build` + kernel-check (axioms ⊆ {propext, Quot.sound}).
#[test]
fn test_runtime_emits_array_row2_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-sort Idx 0)
        (declare-sort Elem 0)
        (declare-const a (Array Idx Elem))
        (declare-const i Idx)
        (declare-const j Idx)
        (declare-const v Elem)
        (assert (not (= i j)))
        (assert (not (= (select (store a i v) j) (select a j))))
        (check-sat)
    "#;
    let commands = parse(input).expect("array script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        !emitted.is_empty(),
        "runtime must emit a firewall Lean proof for the read_over_write_neg lemma"
    );
    let lean = &emitted[0];
    for needle in [
        "abbrev Val := (Nat → Nat) × (Nat → Nat)",
        "firewall_combined_unsat",
        "theorem no_model",
    ] {
        assert!(
            lean.contains(needle),
            "emitted array Lean missing: {needle}"
        );
    }
}

/// End-to-end (formal-verification half (1), STRING length — seventh theory):
/// the runtime emits a verified-firewall Lean proof for a string length-vs-
/// literal conflict (`s = "" ∧ str.len s = 3 ⊢ ⊥`). The conflict lemma and the
/// `TermId` assertions are surface-rewrite-trivialized, so the emitter
/// reconstructs from the FRONTEND PARSED assertions. Generator output separately
/// confirmed to `lake build` + kernel-check.
#[test]
fn test_runtime_emits_string_length_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_S)
        (declare-const s String)
        (assert (= s ""))
        (assert (= (str.len s) 3))
        (check-sat)
    "#;
    let commands = parse(input).expect("string script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        emitted
            .iter()
            .any(|l| l.contains("abbrev Val := String") && l.contains("firewall_combined_unsat")),
        "runtime must emit a string-length firewall Lean proof from the parsed assertions"
    );
}

/// End-to-end (formal-verification half (1), BIT-VECTOR small-width — eighth
/// theory): the runtime emits a verified-firewall Lean proof for a small-width
/// BV conflict (`bvand x y = 0xF ∧ x ≠ 0xF ⊢ ⊥` over BitVec 4). ay bit-blasts BV
/// eagerly (bare-trust), so the emitter reconstructs from the FRONTEND PARSED
/// assertions and refutes by curried `decide`. Generator output separately
/// confirmed to `lake build` + kernel-check.
#[test]
fn test_runtime_emits_bv_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (assert (= (bvand x y) #xF))
        (assert (not (= x #xF)))
        (check-sat)
    "#;
    let commands = parse(input).expect("BV script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        emitted
            .iter()
            .any(|l| l.contains("abbrev Val := BitVec 4") && l.contains("firewall_combined_unsat")),
        "runtime must emit a BV firewall Lean proof from the parsed assertions"
    );
}
