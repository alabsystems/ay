// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Sort, TheoryLemmaKind};
use std::process::Command;

fn fixture(k: i64, target: i64, reverse_p: bool, reverse_q: bool) -> (TermStore, [TermId; 2]) {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let k = t.mk_int(k.into());
    let p = t.mk_app_structural(Symbol::named("*"), [k, x], Sort::Int);
    let n42 = t.mk_int(42.into());
    let target = t.mk_int(target.into());
    let p = t.mk_app_structural(
        Symbol::named("="),
        if reverse_p { [n42, p] } else { [p, n42] },
        Sort::Bool,
    );
    let q = t.mk_app_structural(
        Symbol::named("="),
        if reverse_q { [target, x] } else { [x, target] },
        Sort::Bool,
    );
    let negative = t.mk_not_raw(p);
    (t, [negative, q])
}

fn step(clause: &[TermId]) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "arith".into(),
        clause: clause.to_vec(),
        farkas: None,
        kind: TheoryLemmaKind::ArithClauseTautology,
        lia: None,
    }
}

fn clause_for_opaque_int(terms: &mut TermStore, atom: TermId) -> [TermId; 2] {
    let two = terms.mk_int(2.into());
    let n42 = terms.mk_int(42.into());
    let n21 = terms.mk_int(21.into());
    let product = terms.mk_app_structural(Symbol::named("*"), [two, atom], Sort::Int);
    let source = terms.mk_app_structural(Symbol::named("="), [product, n42], Sort::Bool);
    let target = terms.mk_app_structural(Symbol::named("="), [atom, n21], Sort::Bool);
    [terms.mk_not_raw(source), target]
}

#[test]
fn proportional_equality_raw_handles_and_payloads_decline_before_canonical_rendering() {
    let mut terms = TermStore::new();
    let ordinary = terms.mk_var("x", Sort::Int);
    let oversized_name = terms.mk_var("v".repeat(257), Sort::Int);
    let oversized_symbol =
        terms.mk_app_structural(Symbol::named("f".repeat(257)), [ordinary], Sort::Int);
    let oversized_indices =
        terms.mk_app_structural(Symbol::indexed("opaque", vec![0; 9]), [ordinary], Sort::Int);
    let dangling = terms.mk_app_structural(Symbol::named("opaque"), [TermId(u32::MAX)], Sort::Int);
    for atom in [
        oversized_name,
        oversized_symbol,
        oversized_indices,
        dangling,
    ] {
        let clause = clause_for_opaque_int(&mut terms, atom);
        let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(64));
        assert!(printer
            .format_arith_proportional_equality(
                ProofId(3),
                &TheoryLemmaKind::ArithClauseTautology,
                &clause,
            )
            .is_none());
        assert_eq!(
            printer.work_used(),
            0,
            "canonical rendering was not entered"
        );
        assert!(!arith_proportional_equality_lowering_supported(
            &terms,
            &TheoryLemmaKind::ArithClauseTautology,
            &clause,
            None,
        ));
    }
    assert!(!arith_proportional_equality_lowering_supported(
        &terms,
        &TheoryLemmaKind::ArithClauseTautology,
        &[TermId(u32::MAX), ordinary],
        None,
    ));
}

#[test]
fn proportional_equality_opaque_array_and_uf_atoms_pass_the_actual_printer_and_carcara() {
    for opaque_function in [false, true] {
        let mut terms = TermStore::new();
        let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let index = terms.mk_var("i", Sort::Int);
        let atom = if opaque_function {
            let boolean = terms.mk_bool(true);
            let rational = terms.mk_rational(num_rational::BigRational::new(1.into(), 2.into()));
            let bits = terms.mk_bitvec(3.into(), 8);
            terms.mk_app_structural(
                Symbol::named("opaque_int"),
                [array, boolean, rational, bits],
                Sort::Int,
            )
        } else {
            terms.mk_app_structural(Symbol::named("select"), [array, index], Sort::Int)
        };
        let clause = clause_for_opaque_int(&mut terms, atom);
        let printer = AlethePrinter::new(&terms);
        printer.printed_clause_ledger_active.set(true);
        assert!(arith_proportional_equality_lowering_supported(
            &terms,
            &TheoryLemmaKind::ArithClauseTautology,
            &clause,
            None,
        ));
        let text = printer.format_step(&step(&clause), ProofId(3)).unwrap();
        assert!(text.contains(":rule la_disequality"), "{text}");
        assert!(!text.contains(":rule hole"), "{text}");
        let TermData::Not(source) = terms.get(clause[0]) else {
            unreachable!()
        };
        let source = printer.format_term(*source);
        let target = printer.format_term(clause[1]);
        let function = if opaque_function {
            "(declare-fun opaque_int ((Array Int Int) Bool Real (_ BitVec 8)) Int)\n"
        } else {
            ""
        };
        let problem = format!(
            "(set-logic ALL)\n(declare-const a (Array Int Int))\n\
             (declare-const i Int)\n{function}(assert {source})\n\
             (assert (not {target}))\n(check-sat)\n"
        );
        let proof = format!(
            "(assume h0 {source})\n(assume h1 (not {target}))\n{text}\n\
             (step t4 (cl) :rule resolution :premises (h0 h1 t3))\n"
        );
        carcara(
            if opaque_function {
                "opaque-uf"
            } else {
                "opaque-select"
            },
            &problem,
            &proof,
            "valid",
        );
    }
}

fn carcara(case: &str, problem: &str, proof: &str, expected: &str) {
    ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof).expect("checkable dialect");
    if !Command::new("carcara")
        .arg("--version")
        .output()
        .is_ok_and(|out| out.status.success())
    {
        eprintln!("carcara unavailable: skipping proportional equality {case}");
        return;
    }
    let dir = std::env::temp_dir().join(format!(
        "ay-proportional-equality-{}-{case}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("p.smt2"), problem).unwrap();
    std::fs::write(dir.join("p.alethe"), proof).unwrap();
    let result = Command::new("carcara")
        .args(["check", "--"])
        .arg(dir.join("p.alethe"))
        .arg(dir.join("p.smt2"))
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(dir);
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(text.lines().next(), Some(expected), "{text}\n{proof}");
}

#[test]
fn proportional_equality_active_local_ledger_refuses_an_unbound_generated_premise() {
    let (terms, clause) = fixture(2, 21, false, false);
    let printer = AlethePrinter::new(&terms);
    printer.printed_clause_ledger_active.set(true);
    let original = printer.format_step(&step(&clause), ProofId(3)).unwrap();
    assert!(!original.contains(":rule hole"), "{original}");
    let mut lines: Vec<_> = original.lines().map(str::to_owned).collect();
    let line = lines
        .iter_mut()
        .find(|line| line.contains(":rule or :premises ("))
        .expect("generated Boolean expansion");
    let start = line.find(":premises (").unwrap() + ":premises (".len();
    let end = start + line[start..].find(')').unwrap();
    line.replace_range(start..end, "t3.missing");
    let checked = printer
        .judge_printed_premise_rules(&step(&clause), ProofId(3), lines.join("\n"))
        .unwrap();
    assert!(checked.contains(":rule hole"), "{checked}");
}

#[test]
fn proportional_equality_lowering_preserves_signed_scales_orientation_and_order() {
    for (case, (k, target)) in [(2, 21), (-2, -21), (3, 14)].into_iter().enumerate() {
        for p in [false, true] {
            for q in [false, true] {
                let (terms, clause) = fixture(k, target, p, q);
                for (order, input) in [clause, [clause[1], clause[0]]].into_iter().enumerate() {
                    let printer = AlethePrinter::new(&terms);
                    let text = printer.format_step(&step(&input), ProofId(3)).unwrap();
                    assert!(!text.contains(":rule hole"), "{text}");
                    assert!(text.contains(":rule la_disequality"), "{text}");
                    assert!(arith_proportional_equality_lowering_supported(
                        &terms,
                        &TheoryLemmaKind::ArithClauseTautology,
                        &input,
                        None
                    ));
                    assert!(text
                        .lines()
                        .last()
                        .unwrap()
                        .starts_with(&format!("(step t3 {} ", printer.format_clause(&input))));
                    let TermData::Not(premise) = terms.get(clause[0]) else {
                        unreachable!()
                    };
                    let premise = printer.format_term(*premise);
                    let conclusion = printer.format_term(clause[1]);
                    let problem = format!("(set-logic QF_LIA)\n(declare-const x Int)\n(assert {premise})\n(assert (not {conclusion}))\n(check-sat)\n");
                    let proof = format!("(assume h0 {premise})\n(assume h1 (not {conclusion}))\n{text}\n(step t4 (cl) :rule resolution :premises (h0 h1 t3))\n");
                    carcara(
                        &format!("{case}-{p}-{q}-{order}"),
                        &problem,
                        &proof,
                        "valid",
                    );
                    if case == 0 && !p && !q && order == 0 {
                        let forged = proof.replace("2.0)", "3.0)");
                        assert_ne!(forged, proof);
                        carcara("forged-weight", &problem, &forged, "invalid");
                    }
                }
            }
        }
    }
}

#[test]
fn proportional_equality_lowering_refuses_forged_target_kind_and_surfaces() {
    let (terms, clause) = fixture(2, 22, false, false);
    assert!(!arith_proportional_equality_lowering_supported(
        &terms,
        &TheoryLemmaKind::ArithClauseTautology,
        &clause,
        None
    ));
    let (terms, clause) = fixture(2, 21, false, false);
    assert!(!arith_proportional_equality_lowering_supported(
        &terms,
        &TheoryLemmaKind::Generic,
        &clause,
        None
    ));
    for (term, replacement) in [
        (clause[0], "(not (= (* x 2) 44))"),
        (clause[0], "(= (* x 2) 42)"),
        (clause[1], "(= x 22)"),
    ] {
        let mut overrides = HashMap::default();
        overrides.insert(term, replacement.into());
        assert!(!arith_proportional_equality_lowering_supported(
            &terms,
            &TheoryLemmaKind::ArithClauseTautology,
            &clause,
            Some(&overrides)
        ));
    }
    let TermData::Not(premise) = terms.get(clause[0]) else {
        unreachable!()
    };
    let TermData::App(_, operands) = terms.get(*premise) else {
        unreachable!()
    };
    let TermData::App(_, product) = terms.get(operands[0]) else {
        unreachable!()
    };
    for (term, replacement) in [(operands[0], "(* x 3)"), (product[1], "true")] {
        let mut overrides = HashMap::default();
        overrides.insert(term, replacement.into());
        assert!(!arith_proportional_equality_lowering_supported(
            &terms,
            &TheoryLemmaKind::ArithClauseTautology,
            &clause,
            Some(&overrides)
        ));
    }
    let mut overrides = HashMap::default();
    overrides.insert(clause[0], "(not (= 42 (* 2 x)))".into());
    overrides.insert(clause[1], "(= 21 x)".into());
    assert!(arith_proportional_equality_lowering_supported(
        &terms,
        &TheoryLemmaKind::ArithClauseTautology,
        &clause,
        Some(&overrides)
    ));
}

#[test]
fn proportional_equality_printed_single_orientation_flip_checks_sign_inversion() {
    let (terms, clause) = fixture(2, 21, false, false);
    for source_flip in [false, true] {
        let mut overrides = HashMap::default();
        if source_flip {
            overrides.insert(clause[0], "(not (= 42 (* 2 x)))".into());
        } else {
            overrides.insert(clause[1], "(= 21 x)".into());
        }
        assert!(arith_proportional_equality_lowering_supported(
            &terms,
            &TheoryLemmaKind::ArithClauseTautology,
            &clause,
            Some(&overrides),
        ));
        let printer = AlethePrinter::new_with_overrides_and_budget(
            &terms,
            Some(&overrides),
            Some(4 * 1024 * 1024),
        );
        let text = printer.format_step(&step(&clause), ProofId(3)).unwrap();
        assert!(!text.contains(":rule hole"), "{text}");
        // Keep the ORIGINAL problem and assumptions. Only the lemma surface
        // reverses one equality, so native row signs alone cannot justify it.
        let problem = "(set-logic QF_LIA)\n(declare-const x Int)\n\
            (assert (= (* 2 x) 42))\n(assert (not (= x 21)))\n(check-sat)\n";
        // Connect the changed lemma spelling to the unchanged authored
        // assumptions explicitly; resolution itself does not infer symmetry.
        let (bridge, finish) = if source_flip {
            (
                "(step sy (cl (= (= (* 2 x) 42) (= 42 (* 2 x)))) :rule eq_symmetric)\n\
                 (step sp (cl (not (= (= (* 2 x) 42) (= 42 (* 2 x)))) (not (= (* 2 x) 42)) (= 42 (* 2 x))) :rule equiv_pos2)\n\
                 (step hs (cl (= 42 (* 2 x))) :rule resolution :premises (h0 sy sp))\n",
                "(step t4 (cl) :rule resolution :premises (hs h1 t3))\n",
            )
        } else {
            (
                "(step sy (cl (= (= 21 x) (= x 21))) :rule eq_symmetric)\n\
                 (step sp (cl (not (= (= 21 x) (= x 21))) (not (= 21 x)) (= x 21)) :rule equiv_pos2)\n\
                 (step ts (cl (not (= (* 2 x) 42)) (= x 21)) :rule resolution :premises (t3 sy sp))\n",
                "(step t4 (cl) :rule resolution :premises (h0 h1 ts))\n",
            )
        };
        let proof = format!(
            "(assume h0 (= (* 2 x) 42))\n\
             (assume h1 (not (= x 21)))\n{text}\n{bridge}{finish}"
        );
        carcara(
            &format!("single-flip-{source_flip}"),
            problem,
            &proof,
            "valid",
        );
    }
}

#[test]
fn proportional_equality_lowering_does_not_consume_positional_farkas_hints() {
    let (terms, clause) = fixture(2, 21, false, false);
    let mut annotated = step(&clause);
    if let ProofStep::TheoryLemma { farkas, .. } = &mut annotated {
        *farkas = Some(ay_core::FarkasAnnotation::from_ints(&[999]));
    }
    let printer = AlethePrinter::new(&terms);
    let text = printer.format_step(&annotated, ProofId(3)).unwrap();
    assert!(!text.contains(":rule hole"), "{text}");
    assert!(text.contains(":rule la_disequality"), "{text}");
    assert!(
        !text.contains("999"),
        "the independent derivation must ignore this hint"
    );
}
