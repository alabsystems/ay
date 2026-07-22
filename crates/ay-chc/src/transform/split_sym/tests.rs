// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for the SPLIT-SYM symbol splitter (agenda #9).

use super::*;
use crate::parser::ChcParser;
use crate::pdr::{CexVerificationResult, PdrConfig, PdrResult, PdrSolver};
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult, PortfolioSolver};
use crate::transform::TransformationPipeline;

fn parse(smt: &str) -> ChcProblem {
    ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"))
}

fn split(problem: ChcProblem) -> TransformationResult {
    TransformationPipeline::new()
        .with(SymbolSplitter::new())
        .transform(problem)
}

fn bounded_pdr_config() -> PdrConfig {
    PdrConfig {
        solve_timeout: Some(std::time::Duration::from_mins(1)),
        ..PdrConfig::default()
    }
}

fn solve_with_pdr(problem: ChcProblem) -> PortfolioResult {
    let config = PortfolioConfig::with_engines(vec![EngineConfig::Pdr(PdrConfig::default())])
        .parallel(false);
    PortfolioSolver::new(problem, config).solve()
}

/// 3-state toy FSM in the ssh SSL-state-machine shape: `P(state, x)` where
/// `state` is a constraint-implied constant in every occurrence. The state
/// argument couples the phases (x behaves differently per state), so the
/// monolithic invariant is disjunctive over states â€” the exact shape symbol
/// splitting makes local and trivial per clone.
fn fsm_safe_problem() -> ChcProblem {
    parse(
        r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(assert (forall ((s Int) (x Int)) (=> (and (= s 0) (= x 0)) (P s x))))
(assert (forall ((s Int) (t Int) (x Int) (y Int))
    (=> (and (P s x) (= s 0) (= t 1) (= y (+ x 1))) (P t y))))
(assert (forall ((s Int) (t Int) (x Int) (y Int))
    (=> (and (P s x) (= s 1) (= t 2) (= y (+ x 1))) (P t y))))
(assert (forall ((s Int) (t Int) (x Int) (y Int))
    (=> (and (P s x) (= s 2) (= t 2) (= y x)) (P t y))))
(assert (forall ((s Int) (x Int)) (=> (and (P s x) (= s 2) (> x 2)) false)))
(check-sat)
"#,
    )
}

/// Same FSM with a reachable bad state (x = 2 is reached in state 2).
fn fsm_unsafe_problem() -> ChcProblem {
    parse(
        r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(assert (forall ((s Int) (x Int)) (=> (and (= s 0) (= x 0)) (P s x))))
(assert (forall ((s Int) (t Int) (x Int) (y Int))
    (=> (and (P s x) (= s 0) (= t 1) (= y (+ x 1))) (P t y))))
(assert (forall ((s Int) (t Int) (x Int) (y Int))
    (=> (and (P s x) (= s 1) (= t 2) (= y (+ x 1))) (P t y))))
(assert (forall ((s Int) (x Int)) (=> (and (P s x) (= s 2) (>= x 2)) false)))
(check-sat)
"#,
    )
}

/// The FSM's state argument splits into one clone per state and the
/// monolithic predicate disappears from every transformed clause. The
/// back-translated Safe model must be the disjunction over clones and must
/// verify on the ORIGINAL clauses (G1 certification).
///
/// The per-clone model is constructed directly (the exact per-state
/// invariants the split makes local). Direct `PdrSolver` cannot yet prove
/// ANY 3-predicate chain Safe â€” including hand-written ones without split
/// artifacts â€” so solving the split system end-to-end is portfolio/probe
/// territory; what this test pins is the G1 reassembly + original-clause
/// certification, which is deterministic.
#[test]
fn split_sym_splits_fsm_and_backtranslates_model() {
    let problem = fsm_safe_problem();
    let result = split(problem.clone());

    let p = problem.lookup_predicate("P").unwrap();
    // Original declaration survives (id alignment) but no transformed clause
    // references the monolithic predicate.
    assert!(
        result.problem.clauses().iter().all(|c| {
            c.head.predicate_id() != Some(p) && c.body.predicates.iter().all(|(pid, _)| *pid != p)
        }),
        "monolithic P must not be referenced after splitting"
    );
    // One clone per state value {0, 1, 2}, each with the state arg dropped.
    let clones: Vec<_> = result
        .problem
        .predicates()
        .iter()
        .filter(|pred| pred.name.contains("__ssym"))
        .collect();
    assert_eq!(clones.len(), 3, "expected one clone per state value");
    assert!(
        clones.iter().all(|pred| pred.arity() == 1),
        "split argument must be dropped from clone signatures"
    );

    // Per-clone invariants of the split system: x = 0 in state 0, x = 1 in
    // state 1, x <= 2 in state 2 (clone k <-> first-seen value k).
    let clone_id = |k: usize| {
        result
            .problem
            .lookup_predicate(&format!("P__ssym0_{k}"))
            .expect("clone must be declared")
    };
    let x = ChcVar::new("x", ChcSort::Int);
    let mut model = ValidityWitness::new();
    model.set(
        clone_id(0),
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ),
    );
    model.set(
        clone_id(1),
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
    );
    model.set(
        clone_id(2),
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(2)),
        ),
    );

    let translated = result.back_translator.translate_validity(model);
    let interp = translated
        .get(&p)
        .expect("back-translated model must reassemble the split predicate");
    assert_eq!(
        interp.vars.len(),
        2,
        "reassembled interpretation must regain the split argument"
    );
    let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
    assert!(
        verifier.verify_model(&translated),
        "disjunctive back-translated model must verify on the ORIGINAL clauses"
    );
}

/// Witness back-translation end-to-end: the Unsafe verdict PDR finds on the
/// split system maps back to a counterexample that verifies on the ORIGINAL
/// clauses (G1).
#[test]
fn split_sym_backtranslates_unsafe_witness_to_original() {
    let problem = fsm_unsafe_problem();
    let result = split(problem.clone());
    assert!(
        result
            .problem
            .predicates()
            .iter()
            .any(|pred| pred.name.contains("__ssym")),
        "unsafe FSM must still split"
    );

    match PdrSolver::new(result.problem.clone(), bounded_pdr_config()).solve() {
        PdrResult::Unsafe(cex) => {
            let translated = result.back_translator.translate_invalidity(cex);
            let p = problem.lookup_predicate("P").unwrap();
            assert!(
                translated.steps.iter().all(|step| step.predicate == p),
                "every witness step must be remapped to the original predicate"
            );
            let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
            assert!(
                matches!(
                    verifier.verify_counterexample(&translated),
                    CexVerificationResult::Valid
                ),
                "back-translated witness must replay Valid on the ORIGINAL clauses"
            );
        }
        other => panic!("expected Unsafe on the split FSM, got {other:?}"),
    }
}

/// Back-translation mechanics on a POPULATED derivation witness: clone
/// predicates remap to the original id, canonical variables shift past the
/// split position, the split value is inserted into assignments/instances
/// and conjoined onto entry states, clause indices pass through the identity
/// index map, and the rebuilt witness replays Valid on the ORIGINAL clauses
/// (G1 witness replay).
#[test]
fn split_sym_backtranslates_populated_witness_mechanics() {
    use crate::pdr::counterexample::{DerivationWitness, DerivationWitnessEntry};
    use crate::pdr::{Counterexample, CounterexampleStep};
    use crate::smt::SmtValue;

    let problem = fsm_unsafe_problem();
    let result = split(problem.clone());
    let p = problem.lookup_predicate("P").unwrap();
    let clones: Vec<PredicateId> = (0..3)
        .map(|k| {
            result
                .problem
                .lookup_predicate(&format!("P__ssym0_{k}"))
                .expect("clone must be declared")
        })
        .collect();
    let canon = crate::lemma_hints::canonical_var_name;

    // Clone-space derivation of the bad state (x tracks the state number):
    // P_0(0) -[clause 1]-> P_1(1) -[clause 2]-> P_2(2), query clause 3.
    let entries: Vec<DerivationWitnessEntry> = (0..3usize)
        .map(|k| DerivationWitnessEntry {
            predicate: clones[k],
            level: k,
            state: ChcExpr::eq(
                ChcExpr::var(ChcVar::new(canon(clones[k], 0), ChcSort::Int)),
                ChcExpr::int(k as i64),
            ),
            incoming_clause: Some(k),
            premises: if k == 0 { vec![] } else { vec![k - 1] },
            instances: [(canon(clones[k], 0), SmtValue::Int(k as i128))]
                .into_iter()
                .collect(),
        })
        .collect();
    let steps: Vec<CounterexampleStep> = (0..3usize)
        .map(|k| {
            CounterexampleStep::new(
                clones[k],
                [(canon(clones[k], 0), k as i64)].into_iter().collect(),
            )
            .with_clause(k)
        })
        .collect();
    let cex = Counterexample::with_witness(
        steps,
        DerivationWitness {
            query_clause: Some(3),
            root: 2,
            entries,
        },
    );

    let translated = result.back_translator.translate_invalidity(cex);

    assert_eq!(translated.steps.len(), 3);
    for (k, step) in translated.steps.iter().enumerate() {
        assert_eq!(step.predicate, p, "step {k} must remap to the original id");
        assert_eq!(
            step.clause_index,
            Some(k),
            "identity clause map must pass step indices through"
        );
        assert_eq!(
            step.assignments.get(&canon(p, 1)).copied(),
            Some(k as i64),
            "step {k}: clone arg 0 must rename to original arg 1 (shift past split pos)"
        );
        assert_eq!(
            step.assignments.get(&canon(p, 0)).copied(),
            Some(k as i64),
            "step {k}: split state value must be inserted at the split position"
        );
    }

    let witness = translated.witness.as_ref().expect("witness preserved");
    assert_eq!(witness.query_clause, Some(3));
    for (k, entry) in witness.entries.iter().enumerate() {
        assert_eq!(
            entry.predicate, p,
            "entry {k} must remap to the original id"
        );
        assert_eq!(entry.incoming_clause, Some(k));
        assert_eq!(
            entry.instances.get(&canon(p, 1)),
            Some(&SmtValue::Int(k as i128)),
            "entry {k}: instance key must rename+shift"
        );
        assert_eq!(
            entry.instances.get(&canon(p, 0)),
            Some(&SmtValue::Int(k as i128)),
            "entry {k}: split value instance must be inserted"
        );
        let state_vars: Vec<String> = entry.state.vars().into_iter().map(|v| v.name).collect();
        assert!(
            state_vars.contains(&canon(p, 0)) && state_vars.contains(&canon(p, 1)),
            "entry {k}: state must range over renamed original canonical vars, got {state_vars:?}"
        );
    }

    let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
    assert!(
        matches!(
            verifier.verify_counterexample(&translated),
            CexVerificationResult::Valid
        ),
        "populated back-translated witness must replay Valid on the ORIGINAL clauses"
    );
}

/// Value-cap bail: a predicate whose pinned argument takes more than
/// MAX_SPLIT_VALUES distinct values must not be split (identity transform).
#[test]
fn split_sym_value_cap_bails() {
    let mut input = String::from("(set-logic HORN)\n(declare-fun P (Int Int) Bool)\n");
    for k in 0..=MAX_SPLIT_VALUES {
        input.push_str(&format!(
            "(assert (forall ((s Int) (x Int)) (=> (and (= s {k}) (= x 0)) (P s x))))\n"
        ));
    }
    input.push_str("(assert (forall ((s Int) (x Int)) (=> (and (P s x) (< x 0)) false)))\n");
    input.push_str("(check-sat)\n");
    let problem = parse(&input);
    let clause_count = problem.clauses().len();

    let result = split(problem);
    assert_eq!(
        result.problem.clauses().len(),
        clause_count,
        "over-cap value set must leave the problem untouched"
    );
    assert!(
        result
            .back_translator
            .transform_memory()
            .is_identity_grade(),
        "value-cap bail must be identity-grade"
    );
}

/// SOUNDNESS PIN (wraparound-ish tricky case): the state argument cycles
/// 0 -> 1 -> 2 -> 0 via `t = ite(s = 2, 0, s + 1)`, so the successor state is
/// constraint-implied but NOT a syntactic literal pin. A naive splitter that
/// evaluated arithmetic would clone P and lose the wraparound derivation,
/// flipping this Unsafe problem to Safe (the bad state is only reached AFTER
/// wrapping 2 -> 0 with x = 3). Ours must refuse to split and the verdict
/// must stay Unsafe.
#[test]
fn split_sym_wraparound_state_does_not_flip_verdict() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(assert (forall ((s Int) (x Int)) (=> (and (= s 0) (= x 0)) (P s x))))
(assert (forall ((s Int) (t Int) (x Int) (y Int))
    (=> (and (P s x) (= t (ite (= s 2) 0 (+ s 1))) (= y (+ x 1))) (P t y))))
(assert (forall ((s Int) (x Int)) (=> (and (P s x) (= s 0) (> x 2)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let result = split(problem.clone());

    // The successor state is not a literal/pin, so no split may happen.
    assert!(
        result
            .problem
            .predicates()
            .iter()
            .all(|pred| !pred.name.contains("__ssym")),
        "mod-computed state argument must block splitting"
    );
    assert_eq!(result.problem.clauses().len(), problem.clauses().len());

    // The bad state is reached after wrapping 0 -> 1 -> 2 -> 0 (x = 3 > 2).
    match solve_with_pdr(result.problem) {
        PortfolioResult::Unsafe(_) => {}
        other => panic!("expected Unsafe preserved on wraparound FSM, got {other:?}"),
    }
}

/// SOUNDNESS PIN (no verdict flip through a split): the Unsafe verdict of the
/// FSM must survive splitting â€” the bad state stays reachable through the
/// clone chain.
#[test]
fn split_sym_preserves_unsat_verdict_after_split() {
    let problem = fsm_unsafe_problem();
    let result = split(problem);
    assert!(
        result
            .problem
            .predicates()
            .iter()
            .any(|pred| pred.name.contains("__ssym")),
        "unsafe FSM must split"
    );
    match solve_with_pdr(result.problem) {
        PortfolioResult::Unsafe(_) => {}
        other => panic!("expected Unsafe preserved through the split, got {other:?}"),
    }
}

/// A pass-through occurrence (`P(s, x) => P(s, y)` with `s` unpinned) must
/// disqualify the position even though every other occurrence pins it.
#[test]
fn split_sym_requires_constant_in_every_occurrence() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(assert (forall ((s Int) (x Int)) (=> (and (= s 0) (= x 0)) (P s x))))
(assert (forall ((s Int) (x Int) (y Int))
    (=> (and (P s x) (= y (+ x 1))) (P s y))))
(assert (forall ((s Int) (x Int)) (=> (and (P s x) (= s 0) (< x 0)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let result = split(problem);
    assert!(
        result
            .problem
            .predicates()
            .iter()
            .all(|pred| !pred.name.contains("__ssym")),
        "unpinned pass-through occurrence must block the split"
    );
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
}

/// Transform memory of a real split forces original validation (fail-closed
/// G1 gating) while keeping Unsafe back-translation complete.
#[test]
fn split_sym_transform_memory_forces_original_validation() {
    let result = split(fsm_safe_problem());
    let memory = result.back_translator.transform_memory();
    assert!(!memory.is_identity_grade());
    assert!(memory.unsafe_backtranslation_complete());
    assert!(memory.has_obligation("original-validation-on-safe"));
    assert!(memory.has_obligation("original-replay-on-unsafe"));
}

/// The portfolio preprocessing pipeline routes SPLIT-SYM: the FSM arrives at
/// the engines already split (and the composed transform memory is non-identity
/// so Safe/Unsafe verdicts get original-clause certification).
#[test]
fn split_sym_routed_through_preprocess_pipeline() {
    // State variable at position 1 (NOT arg0): the arg0-only PcSplitter that
    // runs earlier in the same stage passes this shape through, so the
    // routing assertion specifically exercises the general SymbolSplitter.
    let problem = parse(
        r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(assert (forall ((s Int) (x Int)) (=> (and (= s 0) (= x 0)) (P x s))))
(assert (forall ((s Int) (t Int) (x Int) (y Int))
    (=> (and (P x s) (= s 0) (= t 1) (= y (+ x 1))) (P y t))))
(assert (forall ((s Int) (t Int) (x Int) (y Int))
    (=> (and (P x s) (= s 1) (= t 2) (= y (+ x 1))) (P y t))))
(assert (forall ((s Int) (t Int) (x Int) (y Int))
    (=> (and (P x s) (= s 2) (= t 2) (= y x)) (P y t))))
(assert (forall ((s Int) (x Int)) (=> (and (P x s) (= s 2) (> x 2)) false)))
(check-sat)
"#,
    );
    let summary = crate::portfolio::PreprocessSummary::build(problem, false);
    assert!(
        summary
            .transformed_problem
            .predicates()
            .iter()
            .any(|pred| pred.name.contains("__ssym")),
        "preprocess pipeline must apply the symbol splitter"
    );
    assert!(!summary.transform_memory.is_identity_grade());
    assert!(summary.transform_memory.unsafe_backtranslation_complete());
}

/// The kill switch default: SPLIT-SYM is enabled unless
/// AY_CHC_DISABLE_SPLIT_SYM is set to a non-zero value.
#[test]
fn split_sym_enabled_by_default() {
    if std::env::var("AY_CHC_DISABLE_SPLIT_SYM").is_err() {
        assert!(split_sym_enabled());
    }
}
