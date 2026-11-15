// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::EvalValue;
use super::booleans::set_bool_constant;
use super::*;
use ay_core::TermData;

/// A satisfiable query ay answers `unknown` on: the injectivity of `I` forces
/// `Poly` to be infinite, which the ground search does not see, so the model it
/// stops at fails ay's own check. z3 4.12.5 with MBQI off also answers
/// `unknown` and prints a candidate with `L0` true. Every model sets `L0` true;
/// `L1` guards an implication the second assertion already makes true.
const UNKNOWN_QUERY: &str = "
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-fun %I (Poly) Int)
(assert (forall ((x Int)) (! (= x (%I (I x))) :pattern ((I x)))))
(push)
(declare-const a Int)
(declare-const L0 Bool)
(declare-const L1 Bool)
(assert (<= (%I (I a)) 0))
(assert (not (and (=> L1 (< (%I (I a)) 1)) (=> L0 (> (%I (I a)) 0)))))
(check-sat)
";

fn declared(executor: &Executor, name: &str) -> TermId {
    executor
        .ctx
        .symbol_iter()
        .find(|(symbol, _)| symbol.as_str() == name)
        .and_then(|(_, info)| info.term)
        .expect("constant is declared")
}

fn kept_candidate(executor: &Executor) -> Model {
    executor
        .unknown_candidate
        .for_answer(executor.last_result.as_ref())
        .next()
        .expect("a candidate was kept")
        .clone()
}

fn executor(policy: CandidateModelPolicy) -> Executor {
    let mut executor = Executor::new();
    executor.set_candidate_model_policy(policy);
    executor
}

/// Run `script` and return the output of its last command.
fn last_output(executor: &mut Executor, script: &str) -> String {
    let commands = ay_frontend::parse(script).expect("valid SMT-LIB");
    let outputs = executor.execute_all(&commands).expect("commands execute");
    outputs.last().cloned().unwrap_or_default()
}

fn answer_unknown(executor: &mut Executor) {
    let answer = last_output(executor, UNKNOWN_QUERY);
    assert_eq!(
        answer, "unknown",
        "the fixture must answer unknown, or these tests prove nothing"
    );
}

#[test]
fn the_default_policy_withholds_the_candidate() {
    assert_eq!(
        CandidateModelPolicy::default(),
        CandidateModelPolicy::Withhold
    );
    let mut executor = Executor::new();
    assert_eq!(
        executor.candidate_model_policy(),
        CandidateModelPolicy::Withhold
    );
    answer_unknown(&mut executor);
    assert_eq!(
        last_output(&mut executor, "(get-model)"),
        "(error \"model is not available\")"
    );
}

#[test]
fn a_publishing_executor_prints_the_candidate_marked_unvalidated() {
    let mut executor = executor(CandidateModelPolicy::PublishAfterUnknown);
    answer_unknown(&mut executor);
    let model = last_output(&mut executor, "(get-model)");
    assert!(
        model.starts_with(&format!("(model\n  {UNVALIDATED_CANDIDATE_HEADER}\n")),
        "the candidate opens with the unvalidated marker: {model}"
    );
    assert!(model.contains("(define-fun L0 () Bool true)"), "{model}");
}

#[test]
fn a_boolean_no_assertion_needs_true_is_published_false() {
    let mut executor = executor(CandidateModelPolicy::PublishAfterUnknown);
    answer_unknown(&mut executor);
    let l1 = declared(&executor, "L1");
    let mut candidate = kept_candidate(&executor);
    let var = *candidate
        .term_to_var
        .get(&l1)
        .expect("L1 has a SAT variable");
    set_bool_constant(&mut candidate, l1, var, true);
    assert_eq!(executor.printed_bool(&candidate, l1), Some(true));
    let roots = executor.ctx.assertions.clone();
    let published = executor.prefer_false_booleans(&candidate, &roots);
    assert_eq!(
        executor.printed_bool(&published, l1),
        Some(false),
        "nothing needs L1 true"
    );
    let l0 = declared(&executor, "L0");
    assert_eq!(
        executor.printed_bool(&published, l0),
        Some(true),
        "the goal needs L0 true"
    );
}

/// A label that guards a quantified goal, the shape of an AIR
/// `assert forall`: the negated `forall` holds only through the label, so a
/// candidate that sets it false names no failing assertion (AIR then panics
/// looking for one). z3 4.12.5 with MBQI off answers `unknown` and prints the
/// label true.
const GUARD_UNDER_FORALL_QUERY: &str = "
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-fun %I (Poly) Int)
(assert (forall ((x Int)) (! (= x (%I (I x))) :pattern ((I x)))))
(push)
(declare-const L0 Bool)
(assert (not (forall ((y Int)) (! (=> L0 (> (%I (I y)) y)) :pattern ((I y))))))
(check-sat)
";

#[test]
fn a_guard_under_a_quantifier_stays_true() {
    let mut executor = executor(CandidateModelPolicy::PublishAfterUnknown);
    assert_eq!(
        last_output(&mut executor, GUARD_UNDER_FORALL_QUERY),
        "unknown",
        "the fixture must answer unknown, or this test proves nothing"
    );
    let l0 = declared(&executor, "L0");
    assert_eq!(
        executor.printed_bool(&kept_candidate(&executor), l0),
        Some(true),
        "the search needs L0 true"
    );
    let model = last_output(&mut executor, "(get-model)");
    assert!(model.contains("(define-fun L0 () Bool true)"), "{model}");
}

/// Declare `script` (no `check-sat`) and return the executor and its roots.
fn declared_roots(script: &str) -> (Executor, Vec<TermId>) {
    let mut executor = executor(CandidateModelPolicy::PublishAfterUnknown);
    last_output(&mut executor, script);
    let roots = executor.ctx.assertions.clone();
    (executor, roots)
}

/// The comparison inside `root` whose operand applies the function `name`.
fn atom_over(executor: &Executor, root: TermId, name: &str) -> TermId {
    let applies = |term: TermId| match executor.ctx.terms.get(term) {
        TermData::App(symbol, _) => symbol.name() == name,
        _ => false,
    };
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if let TermData::App(_, args) = executor.ctx.terms.get(term) {
            if args.iter().any(|&arg| applies(arg)) {
                return term;
            }
        }
        stack.extend(executor.ctx.terms.children(term));
    }
    panic!("no atom over {name}")
}

/// Assert that the model evaluator leaves `atom` undecided in `model`, so only
/// the SAT assignment can decide it.
fn assert_evaluator_undecided(executor: &Executor, model: &Model, atom: TermId) {
    assert!(
        !matches!(executor.evaluate_term(model, atom), EvalValue::Bool(_)),
        "the fixture needs an atom the evaluator cannot decide"
    );
}

/// A candidate in which only the SAT assignment knows anything: each of
/// `assigned` gets a SAT variable with its value, and there is no theory
/// model.
fn assignment_only(assigned: &[(TermId, bool)]) -> Model {
    let mut model = Model::empty();
    for (var, &(term, value)) in (0u32..).zip(assigned) {
        model.term_to_var.insert(term, var);
        model.sat_model.push(value);
    }
    model
}

/// The value of `root` in a candidate that assigns only `assigned`.
fn root_truth(executor: &Executor, root: TermId, assigned: &[(TermId, bool)]) -> Option<bool> {
    let mut memo = HashMap::default();
    executor.ground_truth(
        &assignment_only(assigned),
        root,
        AtomReading::Assigned,
        &mut memo,
    )
}

/// The first SAT values of `atoms` (every combination is tried) for which
/// `wanted` holds of `truth`, which reads `root` under the values plus a
/// replacement assignment of the labels.
fn atom_values(
    executor: &Executor,
    root: TermId,
    atoms: &[TermId],
    wanted: impl Fn(&dyn Fn(&[(TermId, bool)]) -> Option<bool>) -> bool,
) -> Vec<(TermId, bool)> {
    for bits in 0u32..(1 << atoms.len()) {
        let values: Vec<(TermId, bool)> = (0..atoms.len())
            .map(|index| (atoms[index], bits & (1 << index) != 0))
            .collect();
        let truth = |labels: &[(TermId, bool)]| {
            let mut assigned = labels.to_vec();
            assigned.extend_from_slice(&values);
            root_truth(executor, root, &assigned)
        };
        if wanted(&truth) {
            return values;
        }
    }
    panic!("no values of the atoms give the fixture its shape")
}

/// Two Verus assertions in AIR's shape: the second is checked assuming the
/// first.
const LABEL_CHAIN: &str = "
(declare-sort U 0)
(declare-fun f (U) Int)
(declare-fun g (U) Int)
(declare-const u U)
(declare-const L0 Bool)
(declare-const L1 Bool)
(assert (not (and (=> L0 (> (f u) 0)) (=> (> (f u) 0) (=> L1 (> (g u) 0))))))
";

#[test]
fn the_label_of_the_assertion_the_search_violated_stays_true() {
    // The search left both labels true, satisfied the first assertion and
    // violated the second; the evaluator can read neither assertion.
    let (executor, roots) = declared_roots(LABEL_CHAIN);
    let (l0, l1) = (declared(&executor, "L0"), declared(&executor, "L1"));
    let atoms = [
        atom_over(&executor, roots[0], "f"),
        atom_over(&executor, roots[0], "g"),
    ];
    let values = atom_values(&executor, roots[0], &atoms, |truth| {
        truth(&[(l0, true), (l1, true)]) == Some(true)
            && truth(&[(l0, false), (l1, true)]) == Some(true)
            && truth(&[(l0, true), (l1, false)]) == Some(false)
    });
    let mut assigned = vec![(l0, true), (l1, true)];
    assigned.extend(values);
    let candidate = assignment_only(&assigned);
    for atom in atoms {
        assert_evaluator_undecided(&executor, &candidate, atom);
    }
    let published = executor.prefer_false_booleans(&candidate, &roots);
    assert_eq!(
        executor.printed_bool(&published, l0),
        Some(false),
        "the search satisfied the assertion L0 guards"
    );
    assert_eq!(
        executor.printed_bool(&published, l1),
        Some(true),
        "the search violated the assertion L1 guards"
    );
}

#[test]
fn a_label_stays_true_when_the_assignment_violates_no_assertion() {
    // A rejected candidate can read every guarded assertion true, so the root
    // is false under the assignment and every label looks unneeded. AIR needs
    // one true label; the earliest declared one stays.
    let (executor, roots) = declared_roots(LABEL_CHAIN);
    let (l0, l1) = (declared(&executor, "L0"), declared(&executor, "L1"));
    let atoms = [
        atom_over(&executor, roots[0], "f"),
        atom_over(&executor, roots[0], "g"),
    ];
    let values = atom_values(&executor, roots[0], &atoms, |truth| {
        truth(&[(l0, true), (l1, true)]) == Some(false)
    });
    let mut assigned = vec![(l0, true), (l1, true)];
    assigned.extend(values);
    let candidate = assignment_only(&assigned);
    let published = executor.prefer_false_booleans(&candidate, &roots);
    assert_eq!(executor.printed_bool(&published, l0), Some(true));
    assert_eq!(executor.printed_bool(&published, l1), Some(false));
}

#[test]
fn the_last_true_label_stays_true_when_the_root_stays_unknown() {
    // The search violated the assertion L0 guards; the other conjunct has no
    // SAT variable and no model value, so the root is unknown once L0 is false
    // and true only through L0.
    let (executor, roots) = declared_roots(
        "(declare-sort U 0)(declare-fun g (U) Int)(declare-fun h (U) Int)
         (declare-const u U)(declare-const L0 Bool)
         (assert (not (and (=> L0 (> (g u) 0)) (> (h u) 0))))",
    );
    let l0 = declared(&executor, "L0");
    let violated = atom_over(&executor, roots[0], "g");
    let unknown = atom_over(&executor, roots[0], "h");
    let values = atom_values(&executor, roots[0], &[violated], |truth| {
        truth(&[(l0, true)]) == Some(true) && truth(&[(l0, false)]).is_none()
    });
    let mut assigned = vec![(l0, true)];
    assigned.extend(values);
    let candidate = assignment_only(&assigned);
    assert_evaluator_undecided(&executor, &candidate, violated);
    assert_evaluator_undecided(&executor, &candidate, unknown);
    let published = executor.prefer_false_booleans(&candidate, &roots);
    assert_eq!(executor.printed_bool(&published, l0), Some(true));
}

#[test]
fn a_guard_inside_a_quantifier_or_an_atom_keeps_its_value() {
    let (executor, roots) = declared_roots(
        "(declare-sort U 0)(declare-fun P (U) Bool)(declare-fun F (Bool) U)
         (declare-const u U)(declare-const L0 Bool)(declare-const L1 Bool)
         (assert (not (forall ((x U)) (=> L0 (P x)))))
         (assert (not (= (F L1) u)))",
    );
    let (l0, l1) = (declared(&executor, "L0"), declared(&executor, "L1"));
    let candidate = assignment_only(&[(l0, true), (l1, true)]);
    let published = executor.prefer_false_booleans(&candidate, &roots);
    assert_eq!(executor.printed_bool(&published, l0), Some(true));
    assert_eq!(executor.printed_bool(&published, l1), Some(true));
}

#[test]
fn a_constant_no_root_mentions_is_published_false() {
    let (executor, roots) =
        declared_roots("(declare-const L0 Bool)(declare-const L1 Bool)(assert L0)");
    let (l0, l1) = (declared(&executor, "L0"), declared(&executor, "L1"));
    let candidate = assignment_only(&[(l0, true), (l1, true)]);
    let published = executor.prefer_false_booleans(&candidate, &roots);
    assert_eq!(executor.printed_bool(&published, l0), Some(true));
    assert_eq!(executor.printed_bool(&published, l1), Some(false));
}

#[test]
fn a_candidate_that_falsifies_a_ground_assertion_is_passed_over() {
    let mut executor = executor(CandidateModelPolicy::PublishAfterUnknown);
    answer_unknown(&mut executor);
    let fitting = kept_candidate(&executor);
    let mut falsifying = fitting.clone();
    for name in ["L0", "L1"] {
        let label = declared(&executor, name);
        let var = *falsifying
            .term_to_var
            .get(&label)
            .expect("label has a SAT variable");
        set_bool_constant(&mut falsifying, label, var, false);
    }
    let l0 = declared(&executor, "L0");

    executor.unknown_candidate.models = vec![fitting, falsifying.clone()];
    let published = executor
        .publishable_candidate()
        .expect("the older candidate fits the ground assertions");
    assert_eq!(executor.printed_bool(&published, l0), Some(true));

    executor.unknown_candidate.models = vec![falsifying];
    assert!(executor.publishable_candidate().is_none());
    assert_eq!(
        last_output(&mut executor, "(get-model)"),
        "(error \"model is not available\")"
    );
}

#[test]
fn a_session_that_never_pushed_keeps_no_candidate() {
    let without_push = UNKNOWN_QUERY.replace("(push)", "");
    let mut plain = executor(CandidateModelPolicy::PublishAfterUnknown);
    assert_eq!(last_output(&mut plain, &without_push), "unknown");
    assert_eq!(
        last_output(&mut plain, "(get-model)"),
        "(error \"model is not available\")"
    );

    let mut reset = executor(CandidateModelPolicy::PublishAfterUnknown);
    let after_reset = format!("(push)(pop)(reset){without_push}(get-model)");
    let refused = last_output(&mut reset, &after_reset);
    assert!(refused.starts_with("(error "), "{refused}");
    assert!(reset.unknown_candidate.models.is_empty());
    assert!(reset.publishable_candidate().is_none());

    let mut assuming = executor(CandidateModelPolicy::PublishAfterUnknown);
    let script = without_push.replace("(check-sat)", "(check-sat-assuming (L0))");
    assert_eq!(last_output(&mut assuming, &script), "unknown");
    let model = last_output(&mut assuming, "(get-model)");
    assert!(model.contains(UNVALIDATED_CANDIDATE_HEADER), "{model}");
}

#[test]
fn the_candidate_never_reaches_get_value() {
    let mut executor = executor(CandidateModelPolicy::PublishAfterUnknown);
    answer_unknown(&mut executor);
    let value = last_output(&mut executor, "(get-value (L0))");
    assert!(value.starts_with("(error"), "{value}");
}

#[test]
fn a_changed_assertion_stack_drops_the_candidate() {
    for change in ["(assert true)", "(pop)", "(declare-const b Int)"] {
        let mut executor = executor(CandidateModelPolicy::PublishAfterUnknown);
        answer_unknown(&mut executor);
        let model = last_output(&mut executor, &format!("{change}(get-model)"));
        assert_eq!(
            model, "(error \"model is not available\")",
            "after {change}"
        );
    }
}

#[test]
fn a_later_decided_check_drops_the_candidate() {
    let mut executor = executor(CandidateModelPolicy::PublishAfterUnknown);
    answer_unknown(&mut executor);
    assert_eq!(
        last_output(&mut executor, "(assert (not L0))(check-sat)"),
        "unsat"
    );
    assert_eq!(
        last_output(&mut executor, "(get-model)"),
        "(error \"model is not available\")"
    );
}

#[test]
fn a_sat_answer_prints_the_validated_model_without_the_marker() {
    let mut executor = executor(CandidateModelPolicy::PublishAfterUnknown);
    let answer = last_output(
        &mut executor,
        "(declare-const x Int)(assert (> x 3))(check-sat)",
    );
    assert_eq!(answer, "sat");
    let model = last_output(&mut executor, "(get-model)");
    assert!(model.contains("(define-fun x () Int"), "{model}");
    assert!(!model.contains(UNVALIDATED_CANDIDATE_HEADER), "{model}");
}

#[test]
fn switching_back_to_withhold_forgets_the_candidate() {
    let mut executor = executor(CandidateModelPolicy::PublishAfterUnknown);
    answer_unknown(&mut executor);
    executor.set_candidate_model_policy(CandidateModelPolicy::Withhold);
    assert_eq!(
        last_output(&mut executor, "(get-model)"),
        "(error \"model is not available\")"
    );
}

#[test]
fn quoted_tokens_skip_string_literals() {
    assert_eq!(
        quoted_tokens(r#"(f |a b| "x|y" "q""|z|" |c|)"#),
        ["a b", "c"]
    );
}

#[test]
fn a_definition_with_an_undeclared_quoted_value_is_left_out() {
    let mut executor = executor(CandidateModelPolicy::PublishAfterUnknown);
    last_output(
        &mut executor,
        "(declare-sort S 0)(declare-const |s t| S)(declare-const u S)",
    );
    let declared = "  (define-fun |s t| () S (as @S!0 S))".to_string();
    let mut definitions = vec![declared.clone(), "  (define-fun u () S |0.0|)".to_string()];
    let mut omitted = Vec::new();
    executor.finish_candidate_definitions(&mut definitions, &mut omitted);
    assert_eq!(
        definitions,
        [format!("  {UNVALIDATED_CANDIDATE_HEADER}"), declared]
    );
    assert_eq!(omitted, ["u"]);
}
