// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Proof, TheoryLemmaKind};

const DECL: &str = "(set-logic ALL)
(declare-fun x () Int) (declare-fun y () Int)
(declare-fun a () Bool) (declare-fun b () Bool)
(declare-fun f (Int) Int) (declare-fun R (Int Int) Bool)
(declare-fun v () (_ BitVec 2))";

#[test]
fn an_unchecked_rule_is_refused_before_metering_or_allocating_a_label() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let meter = Meter::new(&printer);
    let mut derivation = Derivation::new(ProofId(7), meter);
    let before_work = printer.work_used();

    assert_eq!(derivation.step("p", "invented_rule", &[]), None);
    assert_eq!(derivation.output, "");
    assert_eq!(printer.work_used(), before_work);
    assert_eq!(
        derivation.step("p", "trans", &[]).as_deref(),
        Some("t7.subst.0")
    );
    assert_eq!(derivation.output, "(step t7.subst.0 (cl p) :rule trans)\n");
}

fn raw(context: &mut ay_frontend::Context, term: &ay_frontend::Term) -> TermId {
    use ay_frontend::Term;
    let inferred = context.elaborate_surface_subterm(term).unwrap();
    let sort = context.terms.sort(inferred).clone();
    let (symbol, args) = match term {
        Term::Symbol(_) | Term::Const(_) => return inferred,
        Term::IndexedApp(_, _, args) if args.is_empty() => return inferred,
        Term::App(name, args) => (Symbol::named(name), args),
        Term::IndexedApp(name, indices, args) => (
            Symbol::indexed(
                name,
                indices
                    .iter()
                    .map(|i| i.as_numeral().unwrap().parse().unwrap())
                    .collect(),
            ),
            args,
        ),
        _ => panic!("unexpected fixture grammar"),
    };
    let args: Vec<_> = args.iter().map(|arg| raw(context, arg)).collect();
    match symbol.name() {
        "not" => context.terms.mk_not_raw(args[0]),
        "ite" => context.terms.mk_ite_raw(args[0], args[1], args[2]),
        _ => context.terms.mk_app(symbol, args, sort),
    }
}

fn fixture(
    pins: &[&str],
    source: &str,
    target: &str,
) -> (TermStore, Vec<TermId>, Vec<TermId>, String) {
    let mut problem = format!("{DECL}\n");
    for formula in pins.iter().copied().chain([source]) {
        problem.push_str(&format!("(assert {formula})\n"));
    }
    problem.push_str(&format!("(assert (not {target}))\n(check-sat)\n"));
    parse_problem(problem)
}

fn parse_problem(problem: String) -> (TermStore, Vec<TermId>, Vec<TermId>, String) {
    let mut context = ay_frontend::Context::new();
    for command in ay_frontend::parse(&problem).unwrap() {
        context.process_command(&command).unwrap();
    }
    let parsed = context.assertions_parsed().to_vec();
    let roots: Vec<_> = parsed.iter().map(|t| raw(&mut context, t)).collect();
    let mut clause: Vec<_> = roots[..roots.len() - 1]
        .iter()
        .map(|&t| context.terms.mk_not_raw(t))
        .collect();
    let TermData::Not(target) = context.terms.get(*roots.last().unwrap()) else {
        panic!("negative target")
    };
    clause.push(*target);
    (context.terms, clause, roots, problem)
}

fn publish(name: &str, pins: &[&str], source: &str, target: &str) {
    publish_fixture(name, fixture(pins, source, target));
}

fn publish_fixture(name: &str, fixture: (TermStore, Vec<TermId>, Vec<TermId>, String)) {
    publish_overridden_fixture(name, fixture, None);
}

fn publish_overridden_fixture(
    name: &str,
    fixture: (TermStore, Vec<TermId>, Vec<TermId>, String),
    overrides: Option<HashMap<TermId, String>>,
) {
    let (terms, clause, roots, problem) = fixture;
    let mut remaining = MAX_WORK;
    assert!(
        checked_ground_substitution_lowering_supported(
            &terms,
            &clause,
            overrides.as_ref(),
            &mut remaining
        ),
        "{name}"
    );
    assert!(remaining < MAX_WORK);
    let mut proof = Proof::new();
    let assumptions: Vec<_> = roots.iter().map(|&r| proof.add_assume(r, None)).collect();
    let mut step = proof.add_theory_lemma_with_kind(
        "uf",
        clause.clone(),
        TheoryLemmaKind::GroundEqualitySubstitution,
    );
    let mut residual = clause.clone();
    for (i, &root) in roots[..roots.len() - 1].iter().enumerate() {
        if !residual.contains(&clause[i]) {
            continue;
        }
        residual.retain(|&literal| literal != clause[i]);
        step = proof.add_resolution(residual.clone(), root, assumptions[i], step);
    }
    proof.add_resolution(
        vec![],
        *clause.last().unwrap(),
        step,
        *assumptions.last().unwrap(),
    );
    crate::check_proof_strict(&proof, &terms).expect("native strict proof");
    let text = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &roots,
        overrides.as_ref(),
    )
    .expect("original-scope export");
    assert!(text.contains(":rule subproof"));
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    let mut streamed = Vec::new();
    crate::try_export_alethe_with_problem_scope_overrides_and_budget_to(
        &mut streamed,
        &proof,
        &terms,
        &roots,
        overrides.as_ref(),
        None,
    )
    .unwrap();
    assert_eq!(streamed, text.as_bytes());
    let path = std::env::temp_dir().join(format!(
        "ay-ground-substitution-{name}-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":text})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
}

mod additional;
mod authored_surface;

#[test]
fn structural_and_boolean_substitution_emit_replayable_proofs() {
    for (name, pins, source, target) in [
        (
            "multiple",
            vec!["(= x 1)", "(= y 2)"],
            "(R (f x) y)",
            "(R (f 1) 2)",
        ),
        ("compound", vec!["(= (f x) 1)"], "(R (f x) x)", "(R 1 x)"),
        (
            "indexed",
            vec!["(= v #b10)"],
            "(= ((_ extract 0 0) v) #b0)",
            "(= ((_ extract 0 0) #b10) #b0)",
        ),
        (
            "boolean",
            vec!["(= x 1)"],
            "(or (not (= x 1)) (and (< y x) a))",
            "(and (< y 1) a)",
        ),
        (
            "nested-singleton",
            vec!["(= x 1)"],
            "(and (= x 1) (and a b))",
            "(and a b)",
        ),
        (
            "duplicates",
            vec!["(= x 1)"],
            "(and (= x 1) a a)",
            "(and a a)",
        ),
        ("ite-true", vec!["(= x 1)"], "(ite (= x 1) a b)", "a"),
        ("ite-false", vec!["(= x 1)"], "(ite (not (= x 1)) a b)", "b"),
        ("absorber", vec!["(= x 1)"], "(or (= x 1) a)", "true"),
        (
            "double-not",
            vec!["(= x 1)"],
            "(not (not (R x y)))",
            "(R 1 y)",
        ),
        (
            "both-sides",
            vec!["(= x 1)"],
            "(R x y)",
            "(and true (R 1 y))",
        ),
        (
            "duplicate-pin",
            vec!["(= x 1)", "(= x 1)"],
            "(R x y)",
            "(R 1 y)",
        ),
    ] {
        publish(name, &pins, source, target);
    }
}

#[test]
fn altered_indices_missing_pins_and_changed_values_are_refused() {
    for (pins, source, target) in [
        (
            vec!["(= v #b10)"],
            "(= ((_ extract 0 0) v) #b0)",
            "(= ((_ extract 1 1) #b10) #b0)",
        ),
        (vec!["(= x 1)"], "(R x y)", "(R 1 2)"),
        (vec!["(= x 2)"], "(R x y)", "(R 1 y)"),
        (vec!["(= x 1)"], "(R x x)", "(R 1 x)"),
    ] {
        let (terms, clause, _, _) = fixture(&pins, source, target);
        assert!(!checked_ground_substitution_lowering_supported(
            &terms,
            &clause,
            None,
            &mut MAX_WORK.clone()
        ));
    }
}

#[test]
fn unsupported_arithmetic_normalization_retains_an_honest_hole() {
    let (terms, clause, _, _) = fixture(&["(= x 1)"], "(< y x)", "(<= y 0)");
    assert!(crate::recognize_ground_equality_substitution(
        &terms, &clause
    ));
    let printer = AlethePrinter::new(&terms);
    assert!(printer
        .format_ground_substitution(ProofId(5), &clause)
        .is_none());
    let text = printer.format_theory_lemma(
        ProofId(5),
        "uf",
        &clause,
        None,
        &TheoryLemmaKind::GroundEqualitySubstitution,
        None,
    );
    assert!(text.unwrap().contains(":rule hole"));
}

#[test]
fn altered_surface_budget_and_expansion_limits_fail_closed() {
    let (terms, clause, roots, _) = fixture(&["(= x 1)"], "(R x y)", "(R 1 y)");
    for &term in clause.iter().chain(roots.iter()) {
        let mut overrides = HashMap::default();
        overrides.insert(term, "false".to_owned());
        // The final negated target is only a proof root, outside the lemma.
        if term == *roots.last().unwrap() {
            continue;
        }
        assert!(!checked_ground_substitution_lowering_supported(
            &terms,
            &clause,
            Some(&overrides),
            &mut MAX_WORK.clone()
        ));
    }
    for mut allowance in [0, 1, 1024, 200_000] {
        assert!(!checked_ground_substitution_lowering_supported(
            &terms,
            &clause,
            None,
            &mut allowance
        ));
        assert_eq!(allowance, 0);
    }
    let source = format!("(and {})", vec!["(R x y)"; MAX_NODES].join(" "));
    let target = source.replace(" x ", " 1 ");
    let (terms, clause, _, _) = fixture(&["(= x 1)"], &source, &target);
    assert!(!checked_ground_substitution_lowering_supported(
        &terms,
        &clause,
        None,
        &mut MAX_WORK.clone()
    ));
    let source = format!(
        "{}(R x y){}",
        "(not ".repeat(MAX_DEPTH + 1),
        ")".repeat(MAX_DEPTH + 1)
    );
    let target = source.replace(" x ", " 1 ");
    let (terms, clause, _, _) = fixture(&["(= x 1)"], &source, &target);
    assert!(!checked_ground_substitution_lowering_supported(
        &terms,
        &clause,
        None,
        &mut MAX_WORK.clone()
    ));
}
