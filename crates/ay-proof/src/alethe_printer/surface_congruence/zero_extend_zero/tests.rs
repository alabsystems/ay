// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{AletheRule, Proof, ProofStep};

struct Fixture {
    terms: TermStore,
    proof: Proof,
    source: [TermId; 2],
    conclusion: TermId,
    x: TermId,
    y: TermId,
}

fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}

fn extend(terms: &mut TermStore, x: TermId, amount: u32) -> TermId {
    let Sort::BitVec(width) = terms.sort(x) else {
        panic!("BV")
    };
    let width = width.width + amount;
    terms.mk_app(
        Symbol::indexed("zero_extend", vec![amount]),
        [x],
        Sort::bitvec(width),
    )
}

fn fixture(nested: usize, amount: u32) -> Fixture {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(1));
    let y = terms.mk_var("y", Sort::bitvec(1));
    let (mut a, mut b) = (x, y);
    for _ in 0..nested {
        a = extend(&mut terms, a, 0);
        b = extend(&mut terms, b, 0);
    }
    let premise = eq(&mut terms, a, b);
    a = extend(&mut terms, a, amount);
    b = extend(&mut terms, b, amount);
    let conclusion = eq(&mut terms, a, b);
    let negative = terms.mk_not_raw(conclusion);
    let mut proof = Proof::new();
    let p = proof.add_assume(premise, None);
    let n = proof.add_assume(negative, None);
    let c = proof.add_rule_step(AletheRule::Cong, vec![conclusion], vec![p], vec![]);
    proof.add_resolution(vec![], conclusion, c, n);
    Fixture {
        terms,
        proof,
        source: [premise, negative],
        conclusion,
        x,
        y,
    }
}

fn export(
    f: &Fixture,
    overrides: Option<&HashMap<TermId, String>>,
) -> Result<String, AlethePrintError> {
    crate::try_export_alethe_with_problem_scope_and_overrides(
        &f.proof, &f.terms, &f.source, overrides,
    )
}

fn prepared(f: &Fixture) -> AlethePrinter<'_> {
    let printer = AlethePrinter::new(&f.terms);
    printer.prepare_proof(&f.proof).unwrap();
    printer.format_step(&f.proof.steps[0], ProofId(0)).unwrap();
    printer
}

#[test]
fn native_zero_cong_exact_source_export_and_independent_replay_artifacts() {
    for nested in [0, 2, 63] {
        let f = fixture(nested, 0);
        crate::check_proof_strict_with_context(&f.proof, &f.terms, None, None, Some(&f.source))
            .expect("unchanged complete native congruence refutation");
        let (text, report) = dialect::capture_alethe_dialect_report(|| export(&f, None).unwrap());
        assert!(text.contains(":rule reordering :premises (t0)"), "{text}");
        assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
        assert_eq!(
            report.first_clean_only(),
            Some(dialect::CleanOnlySpelling::ZeroExtendAsConcat)
        );
        let (raw, pinned_report) = dialect::capture_alethe_dialect_report(|| {
            dialect::with_alethe_dialect(dialect::AletheDialect::PinnedCarcara, || {
                export(&f, None).unwrap()
            })
        });
        assert!(raw.contains(":rule cong :premises (t0)"));
        assert!(pinned_report.is_pinned_spelling());
        if let Ok(directory) = std::env::var("AY_NATIVE_ZERO_CONG_ARTIFACT_DIR") {
            let directory = std::path::Path::new(&directory);
            std::fs::create_dir_all(directory).unwrap();
            let problem = format!(
                "(set-logic QF_BV)\n(declare-const x (_ BitVec 1))\n(declare-const y (_ BitVec 1))\n(declare-const z (_ BitVec 1))\n(assert {})\n(assert {})\n(check-sat)\n",
                crate::format_term_alethe(&f.terms, f.source[0]),
                crate::format_term_alethe(&f.terms, f.source[1]),
            );
            for (name, problem, proof) in [
                ("fixed", problem.clone(), text),
                ("raw", problem.clone(), raw),
                (
                    "wrong-source",
                    problem.replacen("(= x y)", "(= x z)", 1),
                    export(&f, None).unwrap(),
                ),
            ] {
                if name == "wrong-source" && nested != 0 {
                    continue;
                }
                let cert = serde_json::json!({"type":"alethe_certificate", "version":"1.0", "problem":problem, "proof":proof});
                std::fs::write(
                    directory.join(format!("{name}-nested{nested}.json")),
                    serde_json::to_vec_pretty(&cert).unwrap(),
                )
                .unwrap();
            }
        }
    }
}

#[test]
fn actual_ledger_surface_controls_copy_and_orientation() {
    let f = fixture(0, 0);
    for (surface, succeeds) in [
        ("(= x y)", true),
        ("(= y x)", false),
        ("(= x z)", false),
        ("(not (= x y))", false),
    ] {
        let printer = prepared(&f);
        printer.record_printed_conclusion(ProofId(0), &format!("(assume t0 {surface})"));
        assert_eq!(
            printer.format_step(&f.proof.steps[2], ProofId(2)).is_ok(),
            succeeds,
            "{surface}"
        );
    }
    let mut overrides = HashMap::default();
    overrides.insert(
        f.conclusion,
        "(= ((_ zero_extend 0) x) ((_ zero_extend 0) z))".to_string(),
    );
    assert!(export(&f, Some(&overrides)).is_err());
    overrides.insert(
        f.conclusion,
        "(= ((_ zero_extend 0) x) ((_ zero_extend 0) y))".to_string(),
    );
    assert!(export(&f, Some(&overrides))
        .unwrap()
        .contains(":rule reordering"));
}

#[test]
fn authored_head_index_arity_and_type_changing_replacements_refuse() {
    let f = fixture(0, 0);
    for head in [
        "(_ zero_extend 1)",
        "(_ private_zero_extend 0)",
        "(_ |zero_extend| 0)",
        "(_ zero_extend 0 1)",
        "(_ zero_extend)",
    ] {
        let mut overrides = HashMap::default();
        overrides.insert(f.conclusion, format!("(= ({head} x) ({head} y))"));
        assert!(export(&f, Some(&overrides)).is_err(), "{head}");
    }
    let mut overrides = HashMap::default();
    overrides.insert(
        f.conclusion,
        "(= ((_ zero_extend 0) 3) ((_ zero_extend 0) 4))".to_string(),
    );
    overrides.insert(f.source[0], "(= 3 4)".to_string());
    assert!(export(&f, Some(&overrides)).is_err());
    overrides.clear();
    overrides.insert(f.x, "3".to_string());
    overrides.insert(f.y, "4".to_string());
    assert!(
        export(&f, Some(&overrides)).is_err(),
        "a shared malformed spelling is not a Clean reading"
    );
    overrides.clear();
    overrides.insert(f.x, "x".to_string());
    overrides.insert(f.source[0], "(= x y)".to_string());
    assert!(export(&f, Some(&overrides))
        .unwrap()
        .contains(":rule reordering"));
}

#[test]
fn actual_retirement_and_bounded_reader_are_fail_closed() {
    let mut f = fixture(0, 0);
    let p = eq(&mut f.terms, f.x, f.x);
    let z = extend(&mut f.terms, f.x, 0);
    let c = eq(&mut f.terms, z, z);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Refl, vec![p], vec![], vec![]);
    proof.add_rule_step(AletheRule::Cong, vec![c], vec![ProofId(0)], vec![]);
    let printer = AlethePrinter::new(&f.terms);
    printer.prepare_proof(&proof).unwrap();
    printer.format_step(&proof.steps[0], ProofId(0)).unwrap();
    printer.format_step(&proof.steps[1], ProofId(1)).unwrap();
    printer.finish_exported_step(ProofId(1));
    assert!(!printer
        .printed_step_clauses
        .borrow()
        .contains_key(&ProofId(0)));
    assert!(printer.format_step(&proof.steps[1], ProofId(1)).is_err());
    let printer = prepared(&f);
    let huge = format!("(assume t0 (= {} y))", "x".repeat(MAX_BYTES));
    printer.record_printed_conclusion(ProofId(0), &huge);
    assert!(printer.format_step(&f.proof.steps[2], ProofId(2)).is_err());
}

#[test]
fn eligible_missing_unreadable_unbounded_retired_and_future_premises_refuse() {
    let f = fixture(0, 0);
    for entry in [
        None,
        Some(PrintedClause::Unreadable),
        Some(PrintedClause::Unbounded),
    ] {
        let printer = prepared(&f);
        printer
            .printed_step_clauses
            .borrow_mut()
            .remove(&ProofId(0));
        if let Some(entry) = entry {
            printer
                .printed_step_clauses
                .borrow_mut()
                .insert(ProofId(0), entry);
        }
        assert!(printer.format_step(&f.proof.steps[2], ProofId(2)).is_err());
    }
    let printer = prepared(&f);
    printer.printed_clause_atom_texts.borrow_mut().clear();
    assert!(printer.format_step(&f.proof.steps[2], ProofId(2)).is_err());
    let mut future = f.proof.clone();
    future.steps[2] = ProofStep::Step {
        rule: AletheRule::Cong,
        clause: vec![f.conclusion],
        premises: vec![ProofId(3)],
        args: vec![],
    };
    future.steps[3] = ProofStep::Assume(f.source[0]);
    let printer = AlethePrinter::new(&f.terms);
    printer.prepare_proof(&future).unwrap();
    printer.format_step(&future.steps[3], ProofId(3)).unwrap();
    assert!(
        printer.format_step(&future.steps[2], ProofId(2)).is_err(),
        "future text was deliberately pre-recorded"
    );
}

#[test]
fn discharged_assumption_and_malformed_anchor_do_not_gain_authority() {
    let f = fixture(0, 0);
    for end in [3, 8] {
        let mut proof = Proof::new();
        proof.steps = vec![
            ProofStep::Anchor {
                end_step: ProofId(end),
                variables: vec![],
            },
            ProofStep::Assume(f.source[0]),
            ProofStep::Assume(f.source[1]),
            ProofStep::Step {
                rule: AletheRule::Subproof,
                clause: vec![f.source[0]],
                premises: vec![ProofId(1)],
                args: vec![],
            },
            ProofStep::Step {
                rule: AletheRule::Cong,
                clause: vec![f.conclusion],
                premises: vec![ProofId(1)],
                args: vec![],
            },
        ];
        let printer = AlethePrinter::new(&f.terms);
        printer.prepare_proof(&proof).unwrap();
        printer.format_step(&proof.steps[1], ProofId(1)).unwrap();
        assert!(printer.format_step(&proof.steps[4], ProofId(4)).is_err());
    }
}

#[test]
fn nonzero_and_private_heads_keep_the_native_path() {
    let f = fixture(0, 1);
    let (text, report) = dialect::capture_alethe_dialect_report(|| export(&f, None).unwrap());
    assert!(text.contains(":rule cong :premises (t0)"));
    assert!(!text.contains(":rule reordering"));
    assert!(report.is_pinned_spelling());
    let pinned = dialect::with_alethe_dialect(dialect::AletheDialect::PinnedCarcara, || {
        export(&f, None).unwrap()
    });
    assert_eq!(text, pinned);
    let mut f = fixture(0, 0);
    for name in ["private_zero_extend", "|zero_extend|"] {
        let a = f
            .terms
            .mk_app(Symbol::indexed(name, vec![0]), [f.x], Sort::bitvec(1));
        let b = f
            .terms
            .mk_app(Symbol::indexed(name, vec![0]), [f.y], Sort::bitvec(1));
        let c = eq(&mut f.terms, a, b);
        assert!(!AlethePrinter::new(&f.terms).is_zero_extend_zero_cong_candidate(&[c]));
    }
}

#[test]
fn malformed_native_indices_arity_sorts_width_and_arguments_refuse() {
    let mut f = fixture(0, 0);
    for (indices, operands, sort) in [
        (vec![], vec![f.x], Sort::bitvec(1)),
        (vec![0, 1], vec![f.x], Sort::bitvec(1)),
        (vec![0], vec![], Sort::bitvec(1)),
        (vec![0], vec![f.x, f.y], Sort::bitvec(1)),
        (vec![0], vec![f.x], Sort::bitvec(2)),
        (vec![0], vec![f.x], Sort::bitvec(0)),
        (vec![0], vec![f.x], Sort::Int),
    ] {
        let a = f
            .terms
            .mk_app(Symbol::indexed("zero_extend", indices), operands, sort);
        let c = eq(&mut f.terms, a, a);
        let step = ProofStep::Step {
            rule: AletheRule::Cong,
            clause: vec![c],
            premises: vec![ProofId(0)],
            args: vec![],
        };
        assert!(prepared(&f).format_step(&step, ProofId(2)).is_err());
    }
    for (premises, args, clause) in [
        (vec![], vec![], vec![f.conclusion]),
        (vec![ProofId(0), ProofId(0)], vec![], vec![f.conclusion]),
        (vec![ProofId(0)], vec![f.x], vec![f.conclusion]),
        (vec![ProofId(0)], vec![], vec![f.conclusion, f.conclusion]),
    ] {
        let step = ProofStep::Step {
            rule: AletheRule::Cong,
            clause,
            premises,
            args,
        };
        assert!(prepared(&f).format_step(&step, ProofId(2)).is_err());
    }
    let f = fixture(64, 0);
    assert!(export(&f, None).is_err());
}

#[test]
fn existing_emission_work_and_sticky_stop_are_preserved() {
    let f = fixture(0, 0);
    assert!(matches!(
        crate::try_export_alethe_with_problem_scope_overrides_and_budget(
            &f.proof,
            &f.terms,
            &f.source,
            None,
            Some(0),
        ),
        Err(AlethePrintError::EmissionBudgetExhausted { .. })
    ));
    let mut permit = false;
    let mut progress = || {
        let old = permit;
        permit = true;
        old
    };
    let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut progress);
    assert!(matches!(
        printer.prepare_proof(&f.proof),
        Err(AlethePrintError::EmissionStopped { .. })
    ));
    assert!(matches!(
        printer.zero_extend_zero_cong_bridge(ProofId(2), &[f.conclusion], &[ProofId(0)], &[]),
        Err(AlethePrintError::EmissionStopped { .. })
    ));
    assert!(printer.printed_step_clauses.borrow().is_empty());
    let mut printer = prepared(&f);
    printer.work_budget = Some(printer.work_used());
    let before = printer.printed_step_clauses.borrow().len();
    assert!(matches!(
        printer.format_step(&f.proof.steps[2], ProofId(2)),
        Err(AlethePrintError::EmissionBudgetExhausted { .. })
    ));
    assert_eq!(printer.printed_step_clauses.borrow().len(), before);
    let stop = std::cell::Cell::new(false);
    let mut progress = || !stop.get();
    let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut progress);
    printer.prepare_proof(&f.proof).unwrap();
    printer.format_step(&f.proof.steps[0], ProofId(0)).unwrap();
    stop.set(true);
    assert!(matches!(
        printer.format_step(&f.proof.steps[2], ProofId(2)),
        Err(AlethePrintError::EmissionStopped { .. })
    ));
    stop.set(false);
    assert!(matches!(
        printer.format_step(&f.proof.steps[2], ProofId(2)),
        Err(AlethePrintError::EmissionStopped { .. })
    ));
}
