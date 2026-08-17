// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// The last-resort QF_BV `hole` rescue must never overwrite a specialized
/// certificate.
///
/// `rescue_bv_bitblast_collapse` is the fallback for collapses no specific
/// promoter could reconstruct: it re-anchors the refutation on the parsed
/// assertions and marks the bit-blasting gap with an honest `hole`. Its
/// eligibility gate was briefly widened to "any proof deriving the empty
/// clause", which made it fire on the proof `promote_bv_identity_collapse` had
/// built four lines earlier — replacing a strict-checkable `BvBitBlast` lemma
/// with an unchecked hole, and with it the Lean firewall artifact keyed on that
/// lemma kind. Pin the ordering contract directly, not just through the
/// firewall it feeds.
#[test]
fn bv_identity_certificate_survives_the_last_resort_hole_rescue() {
    let input = r#"(set-option :produce-proofs true)(set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (assert (not (= (bvand x x) x)))(check-sat)"#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::BvBitBlast,
                ..
            }
        )),
        "the specialized BvBitBlast certificate must survive the rescue; got {:#?}",
        proof.steps
    );
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Hole,
                ..
            }
        )),
        "no hole may replace a lemma the promoter already certified; got {:#?}",
        proof.steps
    );
}

#[test]
fn qf_bv_wide_bvand_commutativity_under_tst_context_is_fully_checked() {
    // The raw external-codegen TST/NZCV obligation preserves the machine operand order,
    // so its two packed flag expressions differ at nested `(bvand rm rn)` /
    // `(bvand rn rm)` leaves. Prove those leaves with the checked wide-BV
    // producer and lift them through the exact source tree with congruence;
    // never replace the authored assumption by a normalized one.
    for (width, msb) in [(32, 31), (64, 63)] {
        let input = format!(
            r#"
            (set-option :produce-proofs true)
            (set-logic QF_BV)
            (declare-const rn (_ BitVec {width}))
            (declare-const rm (_ BitVec {width}))
            (assert (not (=
              (concat (concat (concat
                (ite (= ((_ extract {msb} {msb}) (bvand rm rn)) (_ bv1 1)) (_ bv1 1) (_ bv0 1))
                (ite (= (bvand rm rn) (_ bv0 {width})) (_ bv1 1) (_ bv0 1)))
                (ite false (_ bv1 1) (_ bv0 1)))
                (ite false (_ bv1 1) (_ bv0 1)))
              (concat (concat (concat
                (ite (= ((_ extract {msb} {msb}) (bvand rn rm)) (_ bv1 1)) (_ bv1 1) (_ bv0 1))
                (ite (= (bvand rn rm) (_ bv0 {width})) (_ bv1 1) (_ bv0 1)))
                (ite false (_ bv1 1) (_ bv0 1)))
                (ite false (_ bv1 1) (_ bv0 1))))))
            (check-sat)
            "#
        );
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        let outputs = exec
            .execute_all(&commands)
            .unwrap_or_else(|error| panic!("width {width}: {error:?}\n{input}"));
        assert_eq!(outputs, ["unsat"], "width {width}: {input}");

        let text = exec.get_proof();
        assert!(text.contains(":rule aci_simp"), "width {width}: {text}");
        assert!(text.contains(":rule cong"), "width {width}: {text}");
        assert!(!text.contains(":rule hole"), "width {width}: {text}");
        assert!(!text.contains(":rule trust"), "width {width}: {text}");

        let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
        let quality = ay_proof::check_proof_strict(proof, &exec.ctx.terms)
            .expect("wide nested bvand-commutativity proof must pass strict replay");
        assert_eq!(quality.trust_count, 0);
        assert_eq!(quality.hole_count, 0);
    }
}

#[test]
fn bvand_commutative_congruence_lane_rejects_near_misses() {
    let mut terms = TermStore::new();
    let bv32 = Sort::bitvec(32);
    let a = terms.mk_var("a", bv32.clone());
    let b = terms.mk_var("b", bv32.clone());
    let c = terms.mk_var("c", bv32.clone());

    let prove = |terms: &mut TermStore, left, right| {
        let mut proof = Proof::new();
        let result = add_bvand_commutative_congruence_proof(terms, &mut proof, left, right);
        assert!(proof.steps.is_empty(), "failed candidates must roll back");
        result
    };

    // A swapped non-commutative operator must never enter the bvand lane.
    let sub_ab = terms.mk_app(Symbol::named("bvsub"), [a, b], bv32.clone());
    let sub_ba = terms.mk_app(Symbol::named("bvsub"), [b, a], bv32.clone());
    assert!(prove(&mut terms, sub_ab, sub_ba).is_none());

    // One wrong operand is not an exact binary swap.
    let and_ab = terms.mk_app(Symbol::named("bvand"), [a, b], bv32.clone());
    let and_bc = terms.mk_app(Symbol::named("bvand"), [b, c], bv32.clone());
    assert!(prove(&mut terms, and_ab, and_bc).is_none());

    // Even with a valid swap in a later branch, different ite conditions stop
    // congruence before any authority is installed.
    let and_ba = terms.mk_app(Symbol::named("bvand"), [b, a], bv32.clone());
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let ite_p = terms.mk_ite_raw(p, and_ab, c);
    let ite_q = terms.mk_ite_raw(q, and_ba, c);
    assert!(prove(&mut terms, ite_p, ite_q).is_none());

    // Dedicated ite and ordinary applications are different congruence heads.
    assert!(prove(&mut terms, ite_p, and_ba).is_none());
}

#[test]
fn qfbv_proof_rebuilder_accepts_structured_decimal_literal() {
    let mut terms = TermStore::new();
    let parsed = FrontendTerm::IndexedApp(
        "bv3".to_string(),
        vec![FrontendIndex::Numeral("4".to_string())],
        Vec::new(),
    );
    let rebuilt = build_qfbv_pterm(&mut terms, &parsed)
        .expect("structured decimal bitvector literal must rebuild");
    let expected = terms.mk_bitvec(BigInt::from(3), 4);
    assert_eq!(rebuilt, expected);
    assert_eq!(terms.sort(rebuilt), &Sort::bitvec(4));
    assert!(build_qfbv_pterm(&mut terms, &FrontendTerm::Symbol("(_ bv3 4)".to_string())).is_none());
}

#[test]
fn test_qf_nia_pin_substitution_is_strict_checkable() {
    // `(= (* x y) 7) ∧ (= x 2)`: pinning x=2 turns the nonlinear `x·y = 7` into the
    // integer-infeasible `2y = 7`. The elaborator folds the substituted product to
    // the canonical `(* y 2)` and emits the residual `(= 7 (* y 2))` as a single
    // `trust` Step (the divisibility lemma `2y≠7` is already strict-checkable).
    // `promote_nia_pin_substitution` reconstructs that trust step from the parsed
    // assertions via eq_reflexive + eq_congruent + a LinearIdentity commutativity
    // bridge + eq_transitive + a resolution chain — all existing strict-validated
    // rules, gated by a whole-proof check_proof_strict revert gate — so it is
    // trust-free.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_NIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (* x y) 7))
        (assert (= x 2))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
    let text = exec.get_proof();
    assert!(
        !text.contains(":rule trust"),
        "NIA pin-substitution must not fall back to trust; got:\n{text}"
    );
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("NIA pin-substitution proof must pass strict check, got {e:?}"),
    }
}

#[test]
fn test_qf_fp_classification_is_strict_checkable() {
    // Small-width FP classification / sign / structural-identity tautology
    // negations are UNSAT; the FP solver emits the identity lemma as a Generic
    // trust theory lemma. `promote_fp_classification_lemmas` re-tags it to the
    // strict-checkable `FpClassification` kind (exhaustive bounded exact-IEEE
    // evaluation) — trust-free.
    for body in [
        "(not (= (fp.abs (fp.abs x)) (fp.abs x)))", // abs idempotence
        "(not (= (fp.neg (fp.neg x)) x))",          // neg involution
        "(and (fp.isNaN x) (fp.isNormal x))",       // mutually exclusive
    ] {
        let input = format!(
            r#"
            (set-option :produce-proofs true)
            (set-logic QF_FP)
            (declare-const x (_ FloatingPoint 3 5))
            (assert {body})
            (check-sat)
        "#
        );
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(outputs, vec!["unsat"], "{body} must be UNSAT");
        let text = exec.get_proof();
        assert!(
            !text.contains(":rule trust"),
            "{body} must not fall back to trust; got:\n{text}"
        );
        let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
        match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
            Ok(quality) => assert_eq!(
                quality.trust_count, 0,
                "strict: zero trust steps for {body}"
            ),
            Err(e) => panic!("{body} proof must pass strict check, got {e:?}"),
        }
    }
}

#[test]
fn test_qf_fplra_forward_error_is_strict_checkable() {
    // A forward-error rounding-claim UNSAT (the geometry_consumer guard-claim shape, one
    // fp.add): the tactic refutes it outside the SAT loop, the proof closes
    // via `derive_empty_via_trust_lemma`, and `promote_fp_forward_error_lemmas`
    // re-tags the Generic lemma to the strict-checkable `FpForwardError` kind
    // (full analytic re-derivation in ay-proof) — trust-free.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_FPLRA)
        (declare-const x Float64)
        (declare-const y Float64)
        (assert (and (fp.isNormal x) (<= (fp.to_real (fp.abs x)) 1.0)))
        (assert (and (fp.isNormal y) (<= (fp.to_real (fp.abs y)) 1.0)))
        (assert (>= (- (fp.to_real (fp.add RNE x y))
                       (+ (fp.to_real x) (fp.to_real y)))
                    0.3))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
    let text = exec.get_proof();
    assert!(
        text.contains(":rule hole") && !text.contains(":rule fp_forward_error"),
        "FpForwardError is an internally certified AY kind, not an Alethe rule; \
         the wire proof must expose the unsupported semantic step as an honest hole:\n{text}"
    );
    assert!(
        !text.contains(":rule trust"),
        "forward-error UNSAT must not fall back to trust; got:\n{text}"
    );
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::FpForwardError,
            ..
        }
    )));
    let report = ay_proof::terminal_trust_report(proof);
    assert!(
        report.is_trust_free(),
        "empty-clause path must be trust-free, got {report:?}"
    );
    match ay_proof::check_proof_strict(proof, &exec.ctx.terms) {
        Ok(quality) => assert_eq!(quality.trust_count, 0, "strict: zero trust steps"),
        Err(e) => panic!("forward-error proof must pass strict check, got {e:?}"),
    }
}

#[test]
fn test_qf_bool_tautology_emits_firewall_lean() {
    let input = r#"(set-option :produce-proofs true)(set-logic QF_UF)(declare-const p Bool)(assert (not (= (not (not p)) p)))(check-sat)"#;
    let cmds = parse(input).unwrap();
    let mut ex = Executor::new();
    assert_eq!(ex.execute_all(&cmds).unwrap(), vec!["unsat"]);
    let proof = ex.last_proof.as_ref().unwrap();
    let fw = emit_firewall_lean(&ex, proof);
    assert_eq!(fw.len(), 1, "expected 1 Boolean firewall file");
    assert!(fw[0].contains("firewall_combined_unsat") && fw[0].contains("abbrev Val := Bool"));
    assert!(
        ex.emit_datatype_firewall_lean_bounded(proof, 0, usize::MAX)
            .is_none(),
        "file-count bound must reject before retaining an artifact"
    );
    assert!(
        ex.emit_datatype_firewall_lean_bounded(proof, 1, fw[0].len() - 1)
            .is_none(),
        "aggregate byte bound must reject an oversized artifact"
    );
    assert_eq!(
        ex.emit_datatype_firewall_lean_bounded(proof, 1, fw[0].len())
            .expect("exact bounds must accept"),
        fw
    );
}

#[test]
fn test_qf_ite_same_emits_firewall_lean() {
    // A real `(not (= (ite p a a) a))` conflict emits one `IteSame` Lean firewall
    // file grounding `(ite c x x) = x` in `firewall_combined_unsat` over
    // `Val = Int × Bool` (verified out-of-band to lake-build, axioms ⊆ kernel-3).
    let input = r#"(set-option :produce-proofs true)(set-logic QF_UF)(declare-const p Bool)(declare-const a Int)(assert (not (= (ite p a a) a)))(check-sat)"#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
    let fw = emit_firewall_lean(&exec, exec.last_proof.as_ref().unwrap());
    let ite = fw
        .iter()
        .find(|f| f.contains("IteSame"))
        .unwrap_or_else(|| {
            panic!(
                "expected an IteSame firewall file; proof={:#?}",
                exec.last_proof.as_ref().unwrap().steps
            )
        });
    assert!(ite.contains("firewall_combined_unsat"));
    assert!(ite.contains("abbrev Val := Int × Bool"));
    assert!(ite.contains("simp [ite_self]"));
}

#[test]
fn test_qf_fp_identity_emits_firewall_lean() {
    // FP sign-bit identities emit an `FpIdent` Lean firewall grounding the
    // identity over the `BitVec 5` carrier (`fp.abs`→clear sign, `fp.neg`→flip),
    // refuted by `decide` (verified out-of-band to lake-build, axioms ⊆ kernel-3).
    for (op, body) in [
        ("absBits", "(not (= (fp.abs (fp.abs x)) (fp.abs x)))"),
        ("negBits", "(not (= (fp.neg (fp.neg x)) x))"),
    ] {
        let input = format!(
            r#"(set-option :produce-proofs true)(set-logic QF_FP)(declare-const x (_ FloatingPoint 3 5))(assert {body})(check-sat)"#
        );
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
        let fw = emit_firewall_lean(&exec, exec.last_proof.as_ref().unwrap());
        let f = fw
            .iter()
            .find(|f| f.contains("FpIdent"))
            .unwrap_or_else(|| panic!("expected an FpIdent firewall for {body}"));
        assert!(f.contains("firewall_combined_unsat"));
        assert!(
            f.contains(op),
            "expected {op} in the FP firewall for {body}"
        );
    }
}

#[test]
fn test_closed_identity_classes_emit_firewall_lean() {
    // Every trust class closed via an all-variable IDENTITY lemma now also emits
    // a half-1 Lean firewall (verified out-of-band to lake-build, axioms ⊆
    // kernel-3): BV identity, NIA linear identity, and DT selector projection —
    // the three that the from-parsed emitters could not reach (no constant to
    // infer the model from), now handled per-lemma-kind with TermStore access.
    let cases = [
        (
            "QF_BV",
            "(declare-const x (_ BitVec 4))",
            "(not (= (bvand x x) x))",
            "Bv_",
        ),
        (
            "QF_NIA",
            "(declare-const x Int)",
            "(not (= (* x 0) 0))",
            "NiaIdent_",
        ),
        (
            "QF_DT",
            "(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))(declare-const a Int)(declare-const b Int)",
            "(not (= (fst (mk a b)) a))",
            "DtSel_",
        ),
    ];
    for (logic, decls, body, tag) in cases {
        let input = format!(
            r#"(set-option :produce-proofs true)(set-logic {logic}){decls}(assert {body})(check-sat)"#
        );
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        assert_eq!(
            exec.execute_all(&commands).unwrap(),
            vec!["unsat"],
            "{body}"
        );
        let fw = emit_firewall_lean(&exec, exec.last_proof.as_ref().unwrap());
        let f = fw.iter().find(|f| f.contains(tag)).unwrap_or_else(|| {
            panic!(
                "expected a {tag} firewall for {body}; proof={:#?}",
                exec.last_proof.as_ref().unwrap().steps
            )
        });
        assert!(f.contains("firewall_combined_unsat"));
    }
}

#[test]
fn test_qf_dt_tester_exclusion_emits_firewall_lean() {
    // bench `soundness_qf_dt_derived_terms/bug1_tester_excl_uf_app.smt2`:
    // two DISTINCT constructor testers on the SAME opaque term `(f x)` — no value
    // is headed by two constructors. End-to-end through the QF_UFDT pipeline.
    let input = r#"(set-option :produce-proofs true)(set-logic QF_UFDT)
        (declare-datatype Enum ((c0) (c1) (c2)))
        (declare-fun f (Enum) Enum)(declare-const x Enum)
        (assert ((_ is c0) (f x)))(assert ((_ is c1) (f x)))(check-sat)"#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
    let fw = emit_firewall_lean(&exec, exec.last_proof.as_ref().unwrap());
    let f = fw
        .iter()
        .find(|f| f.contains("DtTesterExcl_"))
        .expect("expected a DtTesterExcl firewall file");
    assert!(f.contains("firewall_combined_unsat"));
    assert!(f.contains("| k0 | k1 | k2"));
}
