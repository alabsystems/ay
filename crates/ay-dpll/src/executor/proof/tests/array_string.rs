// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// End-to-end (formal-verification half (1), array read-over-write-SAME — ninth
/// theory): the runtime emits a verified-firewall Lean proof for a direct ROW-same
/// conflict (`select (store a i v) i ≠ v ⊢ ⊥`). ay refutes arrays eagerly
/// (bare-trust), so the emitter reconstructs from the FRONTEND PARSED assertions
/// and grounds the generic McCarthy ROW-same theorem. Generator output separately
/// confirmed to `lake build` + kernel-check.
#[test]
fn test_runtime_emits_array_row1_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-sort Idx 0)
        (declare-sort Elem 0)
        (declare-const a (Array Idx Elem))
        (declare-const i Idx)
        (declare-const v Elem)
        (assert (not (= (select (store a i v) i) v)))
        (check-sat)
    "#;
    let commands = parse(input).expect("ROW1 script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        emitted
            .iter()
            .any(|l| l.contains("ArrRow1_") && l.contains("firewall_combined_unsat")),
        "runtime must emit a ROW-same firewall Lean proof from the parsed assertions"
    );
}

/// End-to-end: the runtime emits a verified-firewall Lean proof for a BINARY
/// EUF-congruence conflict (`a=c ∧ b=d ∧ f(a,b)≠f(c,d) ⊢ ⊥`), exercising the
/// n-ary generalization of the congruence emitter (model carries a binary
/// `Nat → Nat → Nat` function). Generator output separately lake-verified.
#[test]
fn test_runtime_emits_binary_euf_congruence_firewall_lean() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U U) U)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-const d U)
        (assert (= a c))
        (assert (= b d))
        (assert (not (= (f a b) (f c d))))
        (check-sat)
    "#;
    let commands = parse(input).expect("binary congruence script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(outputs, vec!["unsat"]);

    let proof = exec.last_proof().expect("a proof was produced").clone();
    let emitted = emit_firewall_lean(&exec, &proof);

    assert!(
        emitted
            .iter()
            .any(|l| l.contains("(Nat → Nat) × (Nat → Nat → Nat)")
                && l.contains("firewall_combined_unsat")),
        "runtime must emit a binary-congruence firewall Lean proof"
    );
}

/// Verify that the strict option is correctly enabled via `set-option` (#4420).
#[test]
fn test_strict_proofs_option_enabled_via_set_option() {
    let input = r#"
        (set-option :check-proofs-strict true)
        (set-logic QF_LRA)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();
    assert!(
        exec.strict_proofs_enabled(),
        "strict proofs should be enabled after set-option"
    );
}

/// #6719 + #6722: QF_AX UNSAT proof with indirect store (ROW2 axiom).
///
/// Verifies trust-free proof for the indirect store pattern
/// `b = store(a, i, v)` with `i != j, select(b, j) != select(a, j)`.
/// - #6719: dpll_snapshot var_to_term capture for dynamic theory atoms
/// - #6722: eager array axiom proof annotations via record_eager_array_axiom_proofs
#[test]
fn test_array_row2_indirect_store_proof_structure() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (assert (= b (store a i v)))
        (assert (not (= i j)))
        (assert (not (= (select b j) (select a j))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");

    let proof = exec
        .last_proof
        .as_ref()
        .expect("proof should exist after UNSAT with produce-proofs");
    let quality =
        ay_proof::check_proof_with_quality(proof, &exec.ctx.terms).expect("proof should validate");
    assert!(
        quality.resolution_count + quality.th_resolution_count >= 1,
        "proof should contain resolution or theory resolution steps: {quality}"
    );
    // Input assertions may be compressed into axioms, theory lemmas, or
    // th_resolution steps by the proof engine. Check the proof has at least
    // some input facts rather than asserting a specific assume count.
    assert!(
        quality.assume_count >= 1 || quality.theory_lemma_count >= 1,
        "proof should have at least one input fact (assume or theory lemma): {quality}"
    );
    assert!(
        Executor::proof_derives_empty_clause(proof),
        "proof must derive the empty clause"
    );
    assert!(
        quality.theory_lemma_count >= 1,
        "ROW2 eager axiom should be recorded as theory lemma (#6722): {quality}"
    );
    // Array axioms now export as `read_over_write_pos`/`read_over_write_neg`/
    // `extensionality` in Alethe format (#8073), no longer falling back to `trust`.
    // The improvement from #6722 is that the axiom is *categorized* as a
    // TheoryLemma(ArraySelectStore) instead of being an anonymous original clause.
}

/// A QF_AX model that satisfies every AUTHORED assertion must self-certify as
/// `sat`, even though `--self-check` forces proof production on and the eager
/// array lane then leaves its injected ROW/extensionality axioms — over fresh
/// `__ay_*` symbols that carry no model value — inside the
/// validation window. Those axioms are solver-generated, not part of the user's
/// claim; before #selfcert-authored they counted as "unverified" and degraded
/// EVERY QF_AX sat to `unknown` (0/60 self-certified on the SMT-LIB sample).
#[cfg(feature = "proof-checker")]
#[test]
fn self_check_certifies_qf_ax_sat_against_authored_assertions() {
    let commands = parse(
        "(set-logic QF_AX)\n\
         (declare-sort Index 0)\n\
         (declare-sort Element 0)\n\
         (declare-fun a () (Array Index Element))\n\
         (declare-fun i () Index)\n\
         (declare-fun j () Index)\n\
         (declare-fun u () Element)\n\
         (declare-fun v () Element)\n\
         (assert (not (= i j)))\n\
         (assert (= (select (store a i u) j) (select a j)))\n\
         (assert (not (= u v)))\n\
         (check-sat)",
    )
    .unwrap();
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_produce_proofs(true);

    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

/// Companion of the test above for the store-FLATTENED shape (`*_sf_*` in the
/// SMT-LIB QF_AX families): proof-mode preprocessing CONSUMES the defining
/// equalities `(= a_k (store a_{k-1} i e))`, so the eliminated array variables
/// have no model value and the authored definitions evaluate to `Unknown`. The
/// gate closes the authored window under those definitions (a model extension)
/// and certifies the substituted window.
#[cfg(feature = "proof-checker")]
#[test]
fn self_check_certifies_store_flattened_sat_via_definitional_closure() {
    let commands = parse(
        "(set-logic QF_AX)\n\
         (declare-sort Index 0)\n\
         (declare-sort Element 0)\n\
         (declare-fun a () (Array Index Element))\n\
         (declare-fun i1 () Index)\n\
         (declare-fun i2 () Index)\n\
         (declare-fun e1 () Element)\n\
         (declare-fun e2 () Element)\n\
         (declare-fun a_1 () (Array Index Element))\n\
         (declare-fun a_2 () (Array Index Element))\n\
         (declare-fun b_1 () (Array Index Element))\n\
         (declare-fun b_2 () (Array Index Element))\n\
         (assert (= a_1 (store a i1 e1)))\n\
         (assert (= a_2 (store a_1 i2 e2)))\n\
         (assert (= b_1 (store a i2 e2)))\n\
         (assert (= b_2 (store b_1 i1 e1)))\n\
         (assert (not (= a_2 b_2)))\n\
         (check-sat)",
    )
    .unwrap();
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_produce_proofs(true);

    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

/// The authored-window rescue must stay FAIL-CLOSED: an UNSAT problem can never
/// be turned into a `sat` by it (there is no model at all), and the `unsat` it
/// does report still has to clear the refutation-proof gate. The store-permuted
/// chains below are provably equal under pairwise-distinct indices, and AY's
/// array lemmas for that shape are still emitted as `trust`, so `--self-check`
/// must degrade to `unknown` rather than emit an uncertified `unsat`.
#[cfg(feature = "proof-checker")]
#[test]
fn self_check_authored_rescue_never_manufactures_sat() {
    let commands = parse(
        "(set-logic QF_AX)\n\
         (declare-sort Index 0)\n\
         (declare-sort Element 0)\n\
         (declare-fun a () (Array Index Element))\n\
         (declare-fun i1 () Index)\n\
         (declare-fun i2 () Index)\n\
         (declare-fun e1 () Element)\n\
         (declare-fun e2 () Element)\n\
         (declare-fun a_1 () (Array Index Element))\n\
         (declare-fun a_2 () (Array Index Element))\n\
         (declare-fun b_1 () (Array Index Element))\n\
         (declare-fun b_2 () (Array Index Element))\n\
         (assert (not (= i1 i2)))\n\
         (assert (= a_1 (store a i1 e1)))\n\
         (assert (= a_2 (store a_1 i2 e2)))\n\
         (assert (= b_1 (store a i2 e2)))\n\
         (assert (= b_2 (store b_1 i1 e1)))\n\
         (assert (not (= a_2 b_2)))\n\
         (check-sat)",
    )
    .unwrap();
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_produce_proofs(true);

    let outputs = exec.execute_all(&commands).unwrap();

    assert_ne!(
        outputs,
        vec!["sat"],
        "unsatisfiable input must never self-certify as sat"
    );
}

#[test]
fn qf_s_ground_regex_refutation_self_certifies_from_authored_assertions() {
    // The QF_S `slog_stranger` "sink" family, verbatim in shape: a string
    // constant is pinned by an authored equality and then asserted to be in a
    // ground regex language it does not belong to.
    //
    // Before the ground string/regex checker and the substitution bridge this
    // exported as `assume (str.in_re "/mod/forum/" R)` (a preprocessing
    // artifact, NOT a problem premise) plus a `:rule trust` lemma, so
    // `--self-check` degraded the UNSAT to `unknown`. Now the leaf is DERIVED
    // from the authored assertion by congruence/equivalence steps and the
    // refutation is a `string_ground_eval` lemma the checker decides outright.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_S)
        (declare-fun literal_5 () String)
        (assert (= literal_5 "/mod/forum/"))
        (assert (str.in_re literal_5
                  (re.++ (re.* re.allchar)
                         (re.++ (str.to_re "\u{5c}\u{3c}SCRIPT") (re.* re.allchar)))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);

    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    let text = exec.get_proof();
    match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("ground-regex refutation must pass strict check, got {e:?}"),
    }
    assert!(
        proof.steps.iter().any(|s| matches!(
            s,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::StringGroundEval,
                ..
            }
        )),
        "the refuting lemma must carry the strict-checkable ground-eval kind"
    );
    assert!(
        proof.steps.iter().any(|s| matches!(
            s,
            ProofStep::Step {
                rule: AletheRule::Cong,
                ..
            }
        )),
        "the substituted leaf must be bridged, not assumed; got:\n{text}\n{:#?}",
        proof.steps
    );

    // Every `assume` must be an AUTHORED assertion.
    let authored = exec.proof_original_problem_assertions();
    for step in &proof.steps {
        if let ProofStep::Assume(term) = step {
            assert!(
                authored.contains(term),
                "proof assumes a non-authored term {term:?}; authored = {authored:?}"
            );
        }
    }

    assert!(
        !text.contains(":rule trust"),
        "ground-regex refutation must not fall back to trust; got:\n{text}"
    );
    // The ground-eval lemma's identity lives in the proof IR (asserted above
    // as `TheoryLemmaKind::StringGroundEval`), not in the printed rule name:
    // `string_ground_eval` is not an Alethe rule, and emitting it made carcara
    // reject the whole document as `invalid`. On the wire it is an honest
    // `hole`; the congruence bridge is a real rule and still prints as one.
    assert!(
        text.contains(":rule hole") && text.contains(":rule cong"),
        "expected the ground-eval lemma as an honest hole and the congruence bridge; got:\n{text}"
    );
    assert!(
        !text.contains(":rule string_ground_eval"),
        "must not emit a rule name no Alethe checker implements; got:\n{text}"
    );
    assert!(
        exec.unsat_proof_self_certified(),
        "the refutation must now self-certify"
    );
}

#[test]
fn qf_s_ground_regex_membership_that_holds_is_sat() {
    // The soundness twin of the test above: when the pinned constant IS in the
    // language, the ground evaluator must NOT manufacture a refutation.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_S)
        (declare-fun literal_5 () String)
        (assert (= literal_5 "xx\u{5c}\u{3c}SCRIPTyy"))
        (assert (str.in_re literal_5
                  (re.++ (re.* re.allchar)
                         (re.++ (str.to_re "\u{5c}\u{3c}SCRIPT") (re.* re.allchar)))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands).unwrap(),
        vec!["sat"],
        "a membership that genuinely holds must stay SAT"
    );
}

#[test]
fn qf_s_symbolic_regex_intersection_refutation_self_certifies() {
    // The QF_S `automatark` family, verbatim in shape: a SYMBOLIC string
    // variable is asserted to be in two ground regex languages whose
    // intersection is empty. The ground evaluator cannot touch this — the fact
    // is not ground — so before the regex-emptiness certificate the refuting
    // lemma exported as `:rule trust` and `--self-check` degraded the UNSAT to
    // `unknown`. Now the lemma carries `RegexIntersectEmpty` and the checker
    // re-derives the whole derivative-product reachability argument itself.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_S)
        (declare-const X String)
        (assert (str.in_re X (re.++ (str.to_re "/f") (re.* (re.range "0" "9"))
                                    (str.to_re "/end"))))
        (assert (str.in_re X (re.++ (str.to_re "/f") (re.* (re.range "a" "z"))
                                    (str.to_re "/x"))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);

    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    assert!(
        proof.steps.iter().any(|s| matches!(
            s,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::RegexIntersectEmpty,
                ..
            }
        )),
        "the refuting lemma must carry the strict-checkable regex-emptiness kind"
    );
    match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("symbolic regex refutation must pass strict check, got {e:?}"),
    }
    let text = exec.get_proof();
    assert!(
        !text.contains(":rule trust"),
        "symbolic regex refutation must not fall back to trust; got:\n{text}"
    );
    // `regex_intersect_empty` is AY's kind name, not an Alethe rule; on the
    // wire the lemma is an honest `hole` (the kind itself is asserted on the
    // proof IR below).
    assert!(
        text.contains(":rule hole"),
        "expected the regex-emptiness lemma as an honest hole; got:\n{text}"
    );
    assert!(
        !text.contains(":rule regex_intersect_empty"),
        "must not emit a rule name no Alethe checker implements; got:\n{text}"
    );
    assert!(
        exec.unsat_proof_self_certified(),
        "the refutation must now self-certify"
    );
}

#[test]
fn qf_s_symbolic_regex_intersection_that_is_non_empty_stays_sat() {
    // The soundness twin: overlapping languages must NOT manufacture a
    // refutation. `X` = "007" satisfies both memberships.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_S)
        (declare-const X String)
        (assert (str.in_re X (re.++ (re.range "0" "9") (re.range "0" "9") (re.range "0" "9"))))
        (assert (str.in_re X (re.* (re.range "0" "9"))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands).unwrap(),
        vec!["sat"],
        "an intersection with a member must stay SAT"
    );
}
