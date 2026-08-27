// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn qf_slia_str_len_axiom_refutation_self_certifies() {
    // A QF_SLIA length contradiction: len(a)=2, len(b)=3, but
    // len(a ++ b)=4. The solver injects the concat-length axiom
    // `len(a ++ b) = len(a) + len(b)` (a universally valid str.len theorem, no
    // authored premise), which drives the `2 + 3 != 4` refutation. Before
    // #selfcert-strlen that axiom surfaced as a foreign `assume` the #8821 gate
    // rejected, degrading the (correct) UNSAT to `unknown` under `--self-check`.
    // Now the leaf carries `StringLengthLemma` and the checker re-derives the
    // exact identity itself.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_SLIA)
        (declare-const a String)
        (declare-const b String)
        (assert (= (str.len a) 2))
        (assert (= (str.len b) 3))
        (assert (= (str.len (str.++ a b)) 4))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);

    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    let text = exec.get_proof();
    assert!(
        proof.steps.iter().any(|s| matches!(
            s,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::StringLengthLemma,
                ..
            }
        )),
        "the injected concat-length axiom must carry the strict-checkable \
         StringLengthLemma kind, not a foreign assume; got:\n{text}\n{:#?}",
        proof.steps
    );
    match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("str.len length refutation must pass strict check, got {e:?}"),
    }
    // `string_length_lemma` is AY's kind name, not an Alethe rule; on the wire
    // the certified length lemma is an honest `hole`.
    assert!(
        text.contains(":rule hole"),
        "expected the certified length lemma as an honest hole; got:\n{text}"
    );
    assert!(
        !text.contains(":rule string_length_lemma"),
        "must not emit a rule name no Alethe checker implements; got:\n{text}"
    );
    assert!(
        exec.unsat_proof_self_certified(),
        "the str.len length refutation must now self-certify"
    );
}

#[test]
fn qf_slia_consistent_str_len_stays_sat() {
    // Soundness twin: promoting the injected length axioms must never
    // manufacture a wrong UNSAT. len(a)=2, len(b)=3, len(a ++ b)=5 is
    // SATISFIABLE (2 + 3 = 5), and must stay SAT.
    let input = r#"
        (set-logic QF_SLIA)
        (declare-const a String)
        (declare-const b String)
        (assert (= (str.len a) 2))
        (assert (= (str.len b) 3))
        (assert (= (str.len (str.++ a b)) 5))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands).unwrap(),
        vec!["sat"],
        "a consistent length constraint must stay SAT"
    );
}

#[test]
fn qf_ax_store_flat_refutation_self_certifies_from_authored_assertions() {
    // The QF_AX `storecomm_*_sf_*` family, verbatim in shape: two store chains
    // build the same array by permuted writes at pairwise-distinct indices, and
    // the problem asserts the two endpoints differ.
    //
    // `substitute_store_flat_equalities` expands every defined array name into
    // its store chain and then DROPS the defining equalities (they have become
    // `true`), so the exported refutation assumed the fully expanded
    // `(not (= (store (store a1 i1 e1) i2 e2) (store (store a1 i2 e2) i1 e1)))`
    // — a preprocessing artifact, not a problem premise. The #8821 authority
    // gate refused to publish that proof and `--self-check` degraded the UNSAT
    // to `unknown`. The substitution bridge now walks back down the chain with
    // `trans` through each authored defining equality plus congruence on the
    // store's array argument, so every leaf is an authored assertion again.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a1 () (Array Index Element))
        (declare-fun b1 () (Array Index Element))
        (declare-fun b2 () (Array Index Element))
        (declare-fun c1 () (Array Index Element))
        (declare-fun c2 () (Array Index Element))
        (declare-fun i1 () Index)
        (declare-fun i2 () Index)
        (declare-fun e1 () Element)
        (declare-fun e2 () Element)
        (assert (= b1 (store a1 i1 e1)))
        (assert (= b2 (store b1 i2 e2)))
        (assert (= c1 (store a1 i2 e2)))
        (assert (= c2 (store c1 i1 e1)))
        (assert (not (= i1 i2)))
        (assert (not (= b2 c2)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);

    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");

    // Every `assume` must be an AUTHORED assertion — this is exactly what the
    // #8821 gate checks, asserted here directly so a regression fails loudly
    // rather than silently degrading to `unknown`.
    let authored = exec.proof_original_problem_assertions();
    for step in &proof.steps {
        if let ProofStep::Assume(term) = step {
            assert!(
                authored.contains(term),
                "proof assumes a non-authored term {term:?}"
            );
        }
    }
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(proof, &authored).is_ok(),
        "the rebuilt proof must clear the #8821 authority gate"
    );

    let text = exec.get_proof();
    assert!(
        !text.contains(":rule trust"),
        "the store-flat refutation must not fall back to trust; got:\n{text}"
    );
    assert!(
        text.contains(":rule trans"),
        "expected the chain-walking `trans` bridge; got:\n{text}"
    );
    assert!(
        exec.unsat_proof_self_certified(),
        "the store-flat refutation must now self-certify"
    );
}

const NESTED_ROW_AUXILIARY_SCRIPT: &str = r#"
    (set-logic QF_AUFNIA)
    (declare-const m0 (Array Int (Array Int Int)))
    (declare-const m1 (Array Int (Array Int Int)))
    (assert
        (= m1
           (store m0 0
                  (store (select m0 0) 1 7))))
    (assert (= (select (select m1 0) 1) 8))
    (check-sat)
"#;

#[test]
fn nested_row_auxiliary_refutation_self_certifies_without_the_independent_crutch() {
    // HISTORY (#implied-forall-ground-inst). The private nested-row rescue
    // folds the two authored array assertions to the array-free residue
    // `false`, and its native proof used to retain an explicit hole: the
    // fused Generic conflict carried the read-over-write content no EUF
    // promotion could reach, so this test once pinned the fail-closed
    // compensation (publication only through the independent fresh-executor
    // discharge, `unsat_proof_self_certified()` false). The certified-EUF
    // planner's ROW-under-equality bridge (`CcReason::Row` in
    // `proof_euf_lemma`) closes that hole: the native proof now derives both
    // reads through strictly validated `arrays_idx`/`ArraySelectStore`
    // content, so the crutch is no longer consumed. MEASURED via the CLI on
    // the same script: `unproved_steps=0 foreign_assumes=no trust_free=yes
    // ay_self_checkable=yes`. (`unsat_proof_self_certified()` stays false on
    // this best-effort route — it additionally demands the solve-time
    // `proof_check_ok` marker this route never records — so the pin below is
    // the strict quality of the retained artifact itself.)
    let commands = parse(NESTED_ROW_AUXILIARY_SCRIPT).unwrap();
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(1_000_000);
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["unsat"],
        "the nested-row refutation must publish; proof={:#?}",
        exec.last_proof.as_ref().map(|proof| &proof.steps)
    );

    assert_eq!(exec.get_reason_unknown(), None);
    assert!(
        exec.last_proof.is_some(),
        "a certified UNSAT keeps its attributed native proof"
    );
    assert!(
        !exec.last_command_unsat_was_independently_verified(),
        "the independent-discharge crutch must no longer be consumed for \
         this refutation"
    );
    let proof = exec.last_proof.clone().expect("checked above");
    let quality = exec
        .check_proof_strict_with_datatypes(&proof)
        .expect("the row-bridged native proof must pass the strict checker");
    assert!(
        quality.is_complete(),
        "no trust and no hole may survive: {quality:?}"
    );
}

#[test]
fn nested_row_auxiliary_refutation_publishes_under_an_explicit_proof_request() {
    // Companion to the test above: with `:produce-proofs` set, this exact
    // script used to fail CLOSED (`unknown`/`SelfCheckRejected`) because the
    // holey native proof could not satisfy an explicit proof request and
    // independent query authority is not allowed to. With the hole closed by
    // the ROW-under-equality bridge the same gate now has a complete strict
    // artifact to publish, and the printed document must carry no unchecked
    // rule.
    let input = format!("(set-option :produce-proofs true)\n{NESTED_ROW_AUXILIARY_SCRIPT}");
    let commands = parse(&input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
    assert_eq!(exec.get_reason_unknown(), None);
    assert!(
        exec.last_proof.is_some(),
        "an explicit proof request must be answered with the artifact"
    );
    let text = exec.get_proof();
    assert!(
        !text.contains(":rule trust") && !text.contains(":rule hole"),
        "no unchecked rule may survive the explicit-proof path: {text}"
    );
    assert!(
        text.contains(":rule arrays_idx"),
        "the nested reads must be certified through the checked array rule: {text}"
    );
}
