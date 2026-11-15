// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::TestResult;
use super::zero_extend::TemplateKey;
use super::*;

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|s| (*s).to_string()).collect()
}

#[test]
fn canonical_zero_extend_template_keeps_pattern_width_and_argument_order() -> TestResult {
    let (a, args_a) = TemplateKey::from_input(&strings(&["false", "a", "a", "true", "b"]), 3)
        .ok_or("first template")?;
    let (renamed, args_b) = TemplateKey::from_input(&strings(&["false", "y", "y", "true", "x"]), 3)
        .ok_or("renamed template")?;
    assert_eq!(a, renamed);
    assert_eq!(args_a, strings(&["a", "b"]));
    assert_eq!(args_b, strings(&["y", "x"]));
    assert_eq!(
        a.bits(&args_a).ok_or("first substitution")?,
        strings(&["false", "a", "a", "true", "b"])
    );
    assert_eq!(
        renamed.bits(&args_b).ok_or("renamed substitution")?,
        strings(&["false", "y", "y", "true", "x"])
    );
    let (changed, _) = TemplateKey::from_input(&strings(&["false", "y", "x", "true", "x"]), 3)
        .ok_or("different repetition")?;
    assert_ne!(a, changed);
    let (changed, _) = TemplateKey::from_input(&strings(&["true", "a", "a", "true", "b"]), 3)
        .ok_or("different constant")?;
    assert_ne!(a, changed);
    let (changed, _) = TemplateKey::from_input(&strings(&["false", "a", "a", "true", "b"]), 4)
        .ok_or("different extension")?;
    assert_ne!(a, changed);
    let eight = (0..8).map(|i| format!("bit_{i}")).collect::<Vec<_>>();
    let mut repeated = eight.clone();
    repeated.extend(eight.clone());
    repeated.resize(128, "false".into());
    assert_eq!(
        TemplateKey::from_input(&repeated, 0)
            .ok_or("wide small support")?
            .1
            .len(),
        8
    );
    let nine = (0..9).map(|i| format!("bit_{i}")).collect::<Vec<_>>();
    assert!(TemplateKey::from_input(&nine, 0).is_none());
    assert!(TemplateKey::from_input(&[], 0).is_none());
    assert!(TemplateKey::from_input(&eight, usize::MAX).is_none());
    Ok(())
}

fn words() -> (ay_core::TermStore, TermId, TermId, [TermId; 4]) {
    let mut terms = ay_core::TermStore::new();
    let x = terms.mk_var("named_byte_x", Sort::bitvec(8));
    let y = terms.mk_var("named_byte_y", Sort::bitvec(8));
    let zx = terms.mk_app(
        Symbol::indexed("zero_extend", vec![56]),
        [x],
        Sort::bitvec(64),
    );
    let zy = terms.mk_app(
        Symbol::indexed("zero_extend", vec![56]),
        [y],
        Sort::bitvec(64),
    );
    let zero = terms.mk_bitvec(num_bigint::BigInt::from(0), 8);
    let padded = terms.mk_app(Symbol::named("concat"), [zero, x], Sort::bitvec(16));
    let repeated = terms.mk_app(Symbol::named("concat"), [x, x], Sort::bitvec(16));
    let zp = terms.mk_app(
        Symbol::indexed("zero_extend", vec![48]),
        [padded],
        Sort::bitvec(64),
    );
    let zr = terms.mk_app(
        Symbol::indexed("zero_extend", vec![48]),
        [repeated],
        Sort::bitvec(64),
    );
    (terms, x, y, [zx, zy, zp, zr])
}

#[test]
fn actual_named_byte_instances_reuse_only_their_exact_closed_template() -> TestResult {
    let (terms, _, _, words) = words();
    let printer = AlethePrinter::new(&terms);
    let mut proof = PackedProof::new(&printer, ProofId(7)).ok_or("packed proof")?;
    let mut circuit = Circuit::new(&mut proof);
    circuit.word(words[0], 0).ok_or("first actual byte")?;
    assert_eq!(circuit.zero_extend_lemmas.len(), 1);
    let first = circuit
        .zero_extend_lemmas
        .values()
        .next()
        .ok_or("closed fact")?
        .unit
        .clone();
    circuit.word(words[1], 0).ok_or("independent actual byte")?;
    assert_eq!(circuit.zero_extend_lemmas.len(), 1);
    assert_eq!(
        circuit
            .zero_extend_lemmas
            .values()
            .next()
            .ok_or("reused fact")?
            .unit,
        first
    );
    circuit.word(words[2], 0).ok_or("constant padded byte")?;
    assert_eq!(circuit.zero_extend_lemmas.len(), 2);
    circuit.word(words[3], 0).ok_or("repeated byte")?;
    assert_eq!(circuit.zero_extend_lemmas.len(), 3);
    Ok(())
}

#[test]
fn independent_packed_roots_refuse_a_copied_foreign_universal_unit() -> TestResult {
    let (terms, _, y, words) = words();
    let printer = AlethePrinter::new(&terms);
    let mut first_proof = PackedProof::new(&printer, ProofId(7)).ok_or("first root")?;
    let (key, fact) = {
        let mut first = Circuit::new(&mut first_proof);
        first.word(words[0], 0).ok_or("first instance")?;
        let (key, fact) = first.zero_extend_lemmas.iter().next().ok_or("first fact")?;
        (key.clone(), fact.clone())
    };
    let mut second_proof = PackedProof::new(&printer, ProofId(8)).ok_or("second root")?;
    let mut second = Circuit::new(&mut second_proof);
    assert!(second.zero_extend_lemmas.is_empty());
    let y_word = second.word(y, 0).ok_or("actual second-root source")?;
    let source = second.value(y_word).ok_or("source value")?;
    // Even a matching shape cannot turn a first-root step name into evidence
    // in this independent root. No fake proof is accepted by this control.
    second.zero_extend_lemmas.insert(key, fact);
    assert!(second.checked_zero_extend(source, 56).is_none());
    let mut third_proof = PackedProof::new(&printer, ProofId(9)).ok_or("fresh third root")?;
    let mut third = Circuit::new(&mut third_proof);
    third
        .word(words[1], 0)
        .ok_or("genuine third-root theorem")?;
    assert_eq!(third.zero_extend_lemmas.len(), 1);
    Ok(())
}

#[test]
fn shared_work_refusal_leaves_no_open_template_and_never_refunds_work() -> TestResult {
    let (terms, x, _, words) = words();
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(20_000));
    let mut proof = PackedProof::new(&printer, ProofId(7)).ok_or("budgeted root")?;
    {
        let mut circuit = Circuit::new(&mut proof);
        let word = circuit.word(x, 0).ok_or("admitted original word")?;
        let source = circuit.value(word).ok_or("source value")?;
        let before = (circuit.proof.out.len(), circuit.proof.definitions.len());
        let spent_before = printer.work_used();
        assert!(circuit.checked_zero_extend(source, 56).is_none());
        assert!(printer.work_budget_exhausted());
        assert!(printer.work_used() > spent_before);
        assert!(circuit.zero_extend_lemmas.is_empty());
        assert_eq!(
            (circuit.proof.out.len(), circuit.proof.definitions.len()),
            before
        );
    }
    let spent = printer.work_used();
    let mut other = PackedProof::new(&printer, ProofId(8)).ok_or("another root, same printer")?;
    let mut circuit = Circuit::new(&mut other);
    assert!(circuit.word(words[1], 0).is_none());
    assert!(printer.work_used() >= spent);
    assert!(printer.work_budget_exhausted());
    Ok(())
}

#[test]
fn closed_constants_use_identity_or_evaluation_without_an_empty_universal() -> TestResult {
    for extra in [0, 56] {
        let mut terms = ay_core::TermStore::new();
        let value = terms.mk_bitvec(num_bigint::BigInt::from(5), 8);
        let wide = terms.mk_app(
            Symbol::indexed("zero_extend", vec![extra]),
            [value],
            Sort::bitvec(8 + extra),
        );
        for dialect in [
            crate::AletheDialect::Clean,
            crate::AletheDialect::PinnedCarcara,
        ] {
            crate::with_alethe_dialect(dialect, || -> TestResult {
                let printer = AlethePrinter::new(&terms);
                let mut proof = PackedProof::new(&printer, ProofId(7)).ok_or("constant root")?;
                let mut circuit = Circuit::new(&mut proof);
                circuit.word(wide, 0).ok_or("closed extension")?;
                assert!(circuit.zero_extend_lemmas.is_empty());
                assert!(!circuit.proof.out.contains("(forall "));
                if extra == 0 && dialect == crate::AletheDialect::Clean {
                    assert!(circuit.proof.out.contains(":rule refl"));
                    assert!(circuit.proof.out.contains(":rule trans"));
                } else {
                    assert!(circuit.proof.out.contains(":rule evaluate"));
                }
                Ok(())
            })?;
        }
        super::tests::certificate(
            &format!("checked-constant-zero-extend-8-{extra}"),
            &format!(
                "(set-logic QF_BV)(assert (not (= ((_ zero_extend {extra}) (_ bv5 8)) (_ bv5 {}))))(check-sat)",
                8 + extra
            ),
        )?;
    }
    Ok(())
}

#[test]
fn generic_binders_remain_fresh_against_actual_source_names() -> TestResult {
    let hostile = "__ay_packed_7_0!zx0!argument_0";
    let mut terms = ay_core::TermStore::new();
    let byte = terms.mk_var(hostile, Sort::bitvec(8));
    let wide = terms.mk_app(
        Symbol::indexed("zero_extend", vec![56]),
        [byte],
        Sort::bitvec(64),
    );
    let printer = AlethePrinter::new(&terms);
    let mut proof = PackedProof::new(&printer, ProofId(7)).ok_or("fresh root namespace")?;
    assert!(!hostile.starts_with(&proof.definition_prefix));
    let mut circuit = Circuit::new(&mut proof);
    circuit
        .word(wide, 0)
        .ok_or("checked extension despite source-name collision")?;
    let binders = circuit
        .proof
        .out
        .lines()
        .filter(|line| line.starts_with("(anchor ") && line.contains(" :args "))
        .collect::<Vec<_>>();
    assert!(!binders.is_empty());
    assert!(binders.iter().all(|line| !line.contains(hostile)));
    Ok(())
}

fn guarded_zero_extend_document(problem: &str) -> TestResult {
    let (context, root, negative) = super::tests::original(problem)?;
    let printer = AlethePrinter::new(&context.terms);
    let (document, report) = crate::capture_alethe_dialect_report(|| {
        printer.format_bv_circuit_refutation(ProofId(7), &[negative])
    });
    let document = document.ok_or("complete generic wire theorem")?;
    let proof = format!(
        "(assume a {})\n{document}(step done (cl) :rule resolution :premises (a t7))\n",
        printer.format_term(root)
    );
    assert!(report.is_pinned_spelling(), "{report:?}");
    assert!(proof.contains(":rule bind") && proof.contains(":rule forall_inst"));
    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
    let judged = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, &proof);
    assert!(
        judged.is_ok(),
        "the maintained guard must admit the real document: {judged:?}"
    );
    Ok(())
}

#[test]
fn universal_byte_theorem_passes_the_unchanged_binder_guard() -> TestResult {
    // This is the observed failing shape: an eight-bit generic theorem,
    // with local nullary word definitions formerly open in its parameters.
    let problem = "(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (not (= ((_ zero_extend 56) x) (concat (_ bv0 56) x))))(check-sat)";
    guarded_zero_extend_document(problem)?;
    // Preserve the actual exclusion as the opposite control. This scanner
    // check makes no claim that the synthetic fragment is a checked proof.
    let old_shape = "(anchor :step end :args ((generic_bit Bool)))\n(define-fun open_word () (_ BitVec 1) (@bbterm generic_bit))\n(step end (cl (= (forall ((generic_bit Bool)) (= open_word open_word)) (forall ((generic_bit Bool)) true))) :rule hole)\n";
    assert!(!ay_core::pinned_carcara::binders_pinned_carcara_misreads("", old_shape).is_empty());
    Ok(())
}

#[test]
fn universal_constant_and_repeated_bit_patterns_pass_the_binder_guard() -> TestResult {
    // Distinct symbolic support stays eight even when the source is wider.
    for (source, extra) in [("(concat #x00 x)", 16), ("(concat x x)", 112)] {
        let problem = format!("(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (not (= ((_ zero_extend {extra}) {source}) (concat (_ bv0 {extra}) {source}))))(check-sat)");
        guarded_zero_extend_document(&problem)?;
    }
    Ok(())
}
