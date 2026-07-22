// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for pc-directed location splitting (SLayerCF shape).

use super::*;
use crate::parser::ChcParser;
use crate::pdr::{CexVerificationResult, PdrConfig, PdrResult, PdrSolver};
use crate::transform::{ClauseInliner, TransformationPipeline};

fn parse(smt: &str) -> ChcProblem {
    ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"))
}

fn split(problem: ChcProblem) -> TransformationResult {
    Box::new(PcSplitter::new().with_enabled(true)).transform(problem)
}

/// PdrConfig with a hard timeout so a slow solve fails the test instead of
/// hanging the suite.
fn bounded_pdr_config() -> PdrConfig {
    PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(60)),
        ..PdrConfig::default()
    }
}

/// Two-level SLayerCF-style pc tower: `P` steps pc 0..=6 incrementing `x`,
/// hands off to `Q` which steps pc 0..=3. Every predicate occurrence has
/// arg0 pinned to a constant (literal head args, constraint-pinned body
/// args) — exactly the SLayerCF shape. Flat BMC needs 11 transitions to
/// reach the bug; both `P` and `Q` are self-recursive, so no inlining is
/// possible before the split.
fn pc_tower(query: &str) -> ChcProblem {
    let mut input = String::from(
        "(set-logic HORN)\n\
         (declare-fun P (Int Int) Bool)\n\
         (declare-fun Q (Int Int) Bool)\n",
    );
    // Level 1 init: P(0, 0).
    input.push_str("(assert (forall ((pc Int) (x Int)) (=> (and (= pc 0) (= x 0)) (P pc x))))\n");
    // Level 1 steps: pc k -> k+1, x + 1.
    for k in 0..6 {
        input.push_str(&format!(
            "(assert (forall ((pc Int) (pc2 Int) (x Int) (y Int)) \
               (=> (and (P pc x) (= pc {k}) (= pc2 {}) (= y (+ x 1))) (P pc2 y))))\n",
            k + 1
        ));
    }
    // Hand-off: P at pc 6 enters Q at pc 0.
    input.push_str(
        "(assert (forall ((pc Int) (q Int) (x Int)) \
           (=> (and (P pc x) (= pc 6) (= q 0)) (Q q x))))\n",
    );
    // Level 2 steps: pc k -> k+1, x unchanged.
    for k in 0..3 {
        input.push_str(&format!(
            "(assert (forall ((pc Int) (pc2 Int) (x Int)) \
               (=> (and (Q pc x) (= pc {k}) (= pc2 {})) (Q pc2 x))))\n",
            k + 1
        ));
    }
    // Terminal self-loop at Q pc 3 (keeps a loop vertex after location
    // splitting + inlining, like the SLayerCF exit levels). Every arg0
    // occurrence stays constant, so the SLayerCF shape is preserved.
    input.push_str(
        "(assert (forall ((pc Int) (pc2 Int) (x Int)) \
           (=> (and (Q pc x) (= pc 3) (= pc2 3)) (Q pc2 x))))\n",
    );
    input.push_str(query);
    input.push_str("\n(check-sat)\n");
    parse(&input)
}

/// Reachable bug: x = 6 at Q pc 3 (11 derivation steps from init).
fn unsafe_tower() -> ChcProblem {
    pc_tower("(assert (forall ((pc Int) (x Int)) (=> (and (Q pc x) (= pc 3) (>= x 6)) false)))")
}

/// Safe variant: x never reaches 100.
fn safe_tower() -> ChcProblem {
    pc_tower("(assert (forall ((pc Int) (x Int)) (=> (and (Q pc x) (= pc 3) (>= x 100)) false)))")
}

// ========================================================================
// Shape detection and split structure
// ========================================================================

#[test]
fn splits_pc_tower_into_location_predicates() {
    let problem = unsafe_tower();
    let result = split(problem.clone());

    // P has pc values 0..=6 (7 clones), Q has 0..=3 (4 clones).
    assert_eq!(result.problem.predicates().len(), 11);
    assert!(
        result
            .problem
            .predicates()
            .iter()
            .all(|p| p.name.contains("__ay_pc")),
        "all predicates must be location clones"
    );
    // Clause count is preserved 1:1.
    assert_eq!(result.problem.clauses().len(), problem.clauses().len());
    // Clones dropped the pc argument.
    assert!(result
        .problem
        .predicates()
        .iter()
        .all(|p| p.arg_sorts.len() == 1));

    // The pinned pc variables are eliminated from the split clauses entirely
    // (env-substituted + constant-folded): every remaining constraint
    // variable also occurs in some predicate occurrence of its clause.
    for clause in result.problem.clauses() {
        let mut occurrence_vars: Vec<ChcVar> = Vec::new();
        for (_, args) in &clause.body.predicates {
            for arg in args {
                occurrence_vars.extend(arg.vars());
            }
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for arg in args {
                occurrence_vars.extend(arg.vars());
            }
        }
        if let Some(constraint) = &clause.body.constraint {
            for var in constraint.vars() {
                assert!(
                    occurrence_vars.contains(&var),
                    "dead pinned variable {} left in split constraint {constraint}",
                    var.name
                );
            }
        }
    }

    let memory = result.back_translator.transform_memory();
    assert_eq!(memory.transform(), "pc_split");
    assert!(memory.validates_original());
    assert!(memory.safe_requires_original_validation());
    assert!(memory.unsafe_backtranslation_complete());
    assert!(
        !memory.is_identity_grade(),
        "pc_split must force original-clause validation (fail-closed)"
    );
    assert_eq!(memory.fact_value("pc_split_predicates"), Some("2"));
    assert_eq!(memory.fact_value("pc_split_clones"), Some("11"));
}

#[test]
fn non_pc_shape_is_left_untouched() {
    // Loop's arg0 is NOT constraint-pinned in the self-loop — not SLayerCF.
    let input = r#"
(set-logic HORN)
(declare-fun Loop (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Loop x))))
(assert (forall ((x Int) (y Int))
    (=> (and (Loop x) (< x 10) (= y (+ x 1))) (Loop y))))
(assert (forall ((x Int)) (=> (and (Loop x) (< x 0)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let clause_count = problem.clauses().len();
    let result = split(problem);
    assert_eq!(result.problem.predicates().len(), 1);
    assert_eq!(result.problem.predicates()[0].name, "Loop");
    assert_eq!(result.problem.clauses().len(), clause_count);
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
}

#[test]
fn kill_switch_disables_split() {
    let problem = unsafe_tower();
    let result = TransformationPipeline::new()
        .with(PcSplitter::new().with_enabled(false))
        .transform(problem.clone());
    assert_eq!(
        result.problem.predicates().len(),
        problem.predicates().len()
    );
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
}

#[test]
fn kill_switch_env_parsing() {
    // The env parser itself: unset/0/empty enable, anything else disables.
    // (Tested via the value predicate to avoid mutating process env.)
    fn disabled(v: Option<&str>) -> bool {
        v.map(|v| !v.is_empty() && v != "0").unwrap_or(false)
    }
    assert!(!disabled(None));
    assert!(!disabled(Some("0")));
    assert!(!disabled(Some("")));
    assert!(disabled(Some("1")));
    assert!(disabled(Some("true")));
}

#[test]
fn value_cap_leaves_wide_predicate_unsplit() {
    // 130 distinct pc values > MAX_PC_VALUES_PER_PREDICATE: no split.
    let mut input = String::from("(set-logic HORN)\n(declare-fun P (Int) Bool)\n");
    for k in 0..130 {
        input.push_str(&format!(
            "(assert (forall ((pc Int)) (=> (= pc {k}) (P pc))))\n"
        ));
    }
    input.push_str("(assert (forall ((pc Int)) (=> (and (P pc) (= pc 500)) false)))\n");
    input.push_str("(check-sat)\n");
    let problem = parse(&input);
    let result = split(problem);
    assert_eq!(result.problem.predicates().len(), 1);
    assert!(result
        .back_translator
        .transform_memory()
        .is_identity_grade());
}

#[test]
fn bv_pc_values_are_split() {
    // SLayerCF proper is BV32; make sure BV literals key the split.
    let input = r#"
(set-logic HORN)
(declare-fun T ((_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((pc (_ BitVec 32)) (x (_ BitVec 32)))
    (=> (and (= pc #x00000000) (= x #x00000000)) (T pc x))))
(assert (forall ((pc (_ BitVec 32)) (pc2 (_ BitVec 32)) (x (_ BitVec 32)))
    (=> (and (T pc x) (= pc #x00000000) (= pc2 #x00000001)) (T pc2 x))))
(assert (forall ((pc (_ BitVec 32)) (x (_ BitVec 32)))
    (=> (and (T pc x) (= pc #x00000001) (= x #x00000005)) false)))
(check-sat)
"#;
    let problem = parse(input);
    let result = split(problem);
    assert_eq!(
        result.problem.predicates().len(),
        2,
        "T must split into per-pc clones for #x00000000 and #x00000001"
    );
}

// ========================================================================
// Refutation: split system refutes at a shallow depth cap
// ========================================================================

/// The flat tower needs 11 derivation steps to reach the bug (P/Q are
/// self-recursive with pc folded into the predicate, so inlining cannot
/// shorten anything). After the split, the per-location predicates form an
/// acyclic low-out-degree chain that ClauseInliner collapses, and a
/// depth-capped BMC refutes shallowly — the SLayerCF play in miniature.
#[test]
#[ntest::timeout(120_000)]
fn split_system_refutes_at_shallow_depth_and_backtranslates() {
    use crate::bmc::{BmcConfig, BmcSolver};
    use crate::ChcEngineResult;

    let problem = unsafe_tower();
    let depth_cap = 3;

    let pipeline_result = TransformationPipeline::new()
        .with(PcSplitter::new().with_enabled(true))
        .with(ClauseInliner::new())
        .transform(problem.clone());
    let split_config = BmcConfig::default()
        .with_max_depth(depth_cap)
        .with_time_budget(std::time::Duration::from_secs(30));
    let split_run = BmcSolver::new(pipeline_result.problem.clone(), split_config).solve();
    let ChcEngineResult::Unsafe(cex) = split_run else {
        panic!("split system must refute at depth {depth_cap}, got {split_run}");
    };

    // The composed back-translation must restore the ORIGINAL vocabulary:
    // every step predicate / clause index must be valid in the original
    // problem, so the portfolio's fail-closed original-clause replay can run.
    // (Full CERTIFIED replay of the collapsed inlined witness on the original
    // clauses is now pinned directly by
    // `deriv_expansion_split_inline_bmc_replays_on_original` — derivation-chain
    // expansion, #chc25-deriv-expansion — closing the hole this comment used to
    // acknowledge.)
    let translated = pipeline_result.back_translator.translate_invalidity(cex);
    assert!(
        !translated.steps.is_empty() || translated.witness.is_some(),
        "back-translation must not lose the refutation"
    );
    for step in &translated.steps {
        assert!(
            problem.get_predicate(step.predicate).is_some(),
            "step predicate must exist in the original problem"
        );
        if let Some(clause_index) = step.clause_index {
            assert!(clause_index < problem.clauses().len());
        }
    }
    if let Some(witness) = &translated.witness {
        for entry in &witness.entries {
            assert!(problem.get_predicate(entry.predicate).is_some());
            if let Some(clause_index) = entry.incoming_clause {
                assert!(clause_index < problem.clauses().len());
            }
        }
    }
}

// ========================================================================
// Derivation-chain expansion (#chc25-deriv-expansion)
// ========================================================================

/// CORE PIN: PcSplitter -> ClauseInliner -> BMC -> translate_invalidity ->
/// verify_counterexample == Valid on the unsafe tower. The inliner COLLAPSES
/// the split location chain into a single composite fact clause; without
/// derivation-chain expansion the composite witness entry has no matching
/// original clause and the refutation is discarded (Unknown). This pins that
/// the expanded chain replays on the ORIGINAL clauses.
#[test]
#[ntest::timeout(180_000)]
fn deriv_expansion_split_inline_bmc_replays_on_original() {
    use crate::bmc::{BmcConfig, BmcSolver};
    use crate::ChcEngineResult;

    let problem = unsafe_tower();
    let pipeline_result = TransformationPipeline::new()
        .with(PcSplitter::new().with_enabled(true))
        .with(ClauseInliner::new())
        .transform(problem.clone());

    let cfg = BmcConfig::default()
        .with_max_depth(4)
        .with_time_budget(std::time::Duration::from_secs(60));
    let ChcEngineResult::Unsafe(cex) = BmcSolver::new(pipeline_result.problem.clone(), cfg).solve()
    else {
        panic!("inlined split tower must refute at a shallow depth");
    };

    // NON-VACUOUS: the inliner collapses the whole P0..Q3 location chain into
    // ONE composite fact clause, so the raw witness has a single entry. With
    // expansion the back-translated witness must contain the reconstructed
    // multi-entry chain (proving expansion fired, not just the fallback replay).
    let raw_entries = cex.witness.as_ref().map(|w| w.entries.len()).unwrap_or(0);
    let translated = pipeline_result.back_translator.translate_invalidity(cex);
    let n_entries = translated
        .witness
        .as_ref()
        .map(|w| w.entries.len())
        .unwrap_or(0);
    assert!(
        n_entries >= 5 && n_entries > raw_entries,
        "expansion must reconstruct the collapsed chain (raw={raw_entries}, expanded={n_entries})"
    );
    // The expanded witness must certify on the ORIGINAL clauses.
    let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
    assert_eq!(
        verifier.verify_counterexample(&translated),
        CexVerificationResult::Valid,
        "expanded inlined refutation must certify on the original clauses"
    );
}

/// REQUIRED PIN (closes the acknowledged hole at pc_split/tests.rs above):
/// PcSplitter -> CondenseSuperpass -> ClauseInliner -> BMC ->
/// translate_invalidity -> verify_counterexample == Valid on the unsafe tower.
#[test]
#[ntest::timeout(180_000)]
fn deriv_expansion_split_condense_inline_bmc_replays_on_original() {
    use crate::bmc::{BmcConfig, BmcSolver};
    use crate::transform::CondenseSuperpass;
    use crate::ChcEngineResult;

    // Honor the condense kill switch so this test self-skips when condense is
    // disabled (mirrors condense/split_sym test guards).
    if std::env::var("AY_CHC_DISABLE_CONDENSE").is_ok() {
        return;
    }

    let problem = unsafe_tower();
    let pipeline_result = TransformationPipeline::new()
        .with(PcSplitter::new().with_enabled(true))
        .with(CondenseSuperpass::new())
        .with(ClauseInliner::new())
        .transform(problem.clone());

    let cfg = BmcConfig::default()
        .with_max_depth(6)
        .with_time_budget(std::time::Duration::from_secs(90));
    let ChcEngineResult::Unsafe(cex) = BmcSolver::new(pipeline_result.problem.clone(), cfg).solve()
    else {
        panic!("split+condense+inline tower must refute at a shallow depth");
    };

    let raw_entries = cex.witness.as_ref().map(|w| w.entries.len()).unwrap_or(0);
    let translated = pipeline_result.back_translator.translate_invalidity(cex);
    let n_entries = translated
        .witness
        .as_ref()
        .map(|w| w.entries.len())
        .unwrap_or(0);
    assert!(
        n_entries >= 5 && n_entries > raw_entries,
        "expansion must reconstruct the collapsed chain through condense (raw={raw_entries}, expanded={n_entries})"
    );
    let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
    assert_eq!(
        verifier.verify_counterexample(&translated),
        CexVerificationResult::Valid,
        "expanded split+condense+inline refutation must certify on the original clauses"
    );
}

/// ADVERSARIAL (a): expansion must not launder a refutation across the
/// safe/unsafe boundary. The UNSAFE tower's expanded witness derives the bad
/// state x = 6; replayed against the SAFE tower's ORIGINAL clauses (identical
/// except the query demands x >= 100) it must be REJECTED, never Valid. This
/// pins that the fully-expanded chain is still gated by the original query.
#[test]
#[ntest::timeout(180_000)]
fn deriv_expansion_expanded_witness_rejected_on_safe_query() {
    use crate::bmc::{BmcConfig, BmcSolver};
    use crate::ChcEngineResult;

    let unsafe_problem = unsafe_tower();
    let pipeline_result = TransformationPipeline::new()
        .with(PcSplitter::new().with_enabled(true))
        .with(ClauseInliner::new())
        .transform(unsafe_problem.clone());

    let cfg = BmcConfig::default()
        .with_max_depth(4)
        .with_time_budget(std::time::Duration::from_secs(60));
    let ChcEngineResult::Unsafe(cex) = BmcSolver::new(pipeline_result.problem.clone(), cfg).solve()
    else {
        panic!("inlined unsafe tower must refute");
    };
    let translated = pipeline_result.back_translator.translate_invalidity(cex);

    // Sanity: it IS valid on the unsafe tower (expansion produced a real chain).
    let mut ok = PdrSolver::new(unsafe_problem, bounded_pdr_config());
    assert_eq!(
        ok.verify_counterexample(&translated),
        CexVerificationResult::Valid
    );

    // But on the SAFE tower (query x >= 100) the same expanded witness must NOT
    // certify: x = 6 does not violate the safe query. Fail closed.
    let mut safe_verifier = PdrSolver::new(safe_tower(), bounded_pdr_config());
    assert_ne!(
        safe_verifier.verify_counterexample(&translated),
        CexVerificationResult::Valid,
        "expanded witness must never certify against the safe query"
    );
}

// ========================================================================
// Model back-translation (Safe side)
// ========================================================================

/// Deterministic G1 pin for the Safe side: a hand-built VALID model of the
/// split system (P at pc k carries x = k; Q carries x = 6) must reassemble
/// disjunctively onto the original vocabulary and pass `verify_model` on the
/// ORIGINAL clauses. No solver search involved — this pins exactly the
/// disjunctive back-translation, independent of engine heuristics.
#[test]
#[ntest::timeout(120_000)]
fn split_safe_model_backtranslates_and_verifies_on_original() {
    let problem = safe_tower();
    let result = split(problem.clone());

    // Valid clone model: P__ay_pc{k}(x) := x = k (x counts the k increments),
    // Q__ay_pc{k}(x) := x = 6 (x is frozen at 6 after the hand-off).
    let mut model = crate::InvariantModel::new();
    for pred in result.problem.predicates() {
        let var = ChcVar::new(canonical_var_name(pred.id, 0), ChcSort::Int);
        let value = if let Some(k) = pred.name.strip_prefix("P__ay_pc") {
            k.parse::<i128>().unwrap()
        } else if pred.name.starts_with("Q__ay_pc") {
            6
        } else {
            panic!("unexpected predicate {}", pred.name)
        };
        let formula = ChcExpr::eq(ChcExpr::var(var.clone()), ChcExpr::Int(value));
        model.set(pred.id, PredicateInterpretation::new(vec![var], formula));
    }

    let translated = result.back_translator.translate_validity(model);
    // Disjunctive reassembly restores the original vocabulary.
    for pred in problem.predicates() {
        let interp = translated
            .get(&pred.id)
            .unwrap_or_else(|| panic!("missing interpretation for {}", pred.name));
        assert_eq!(interp.vars.len(), pred.arg_sorts.len());
    }
    let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
    assert!(
        verifier.verify_model(&translated),
        "back-translated disjunctive model must verify on the original clauses"
    );
}

// ========================================================================
// Soundness pins (no false results through the gate)
// ========================================================================

/// The split must never manufacture a Safe verdict: on the UNSAFE tower the
/// split system stays refutable, and the back-translated witness verifies
/// on the original clauses (the certified-unsafe path).
#[test]
#[ntest::timeout(180_000)]
fn soundness_pin_unsafe_stays_unsafe_through_split() {
    let problem = unsafe_tower();
    let result = split(problem.clone());

    let mut solver = PdrSolver::new(result.problem.clone(), bounded_pdr_config());
    match solver.solve() {
        PdrResult::Unsafe(cex) => {
            let translated = result.back_translator.translate_invalidity(cex);
            let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
            assert!(
                matches!(
                    verifier.verify_counterexample(&translated),
                    CexVerificationResult::Valid
                ),
                "split-system refutation must certify on the original clauses"
            );
        }
        other => panic!("expected Unsafe on split unsafe tower, got {other:?}"),
    }
}

/// A bogus all-`true` clone model must NOT pass the original-clause gate
/// after back-translation: the fail-closed pipeline (translate, then
/// verify_model on ORIGINAL clauses) rejects it. This pins that the
/// back-translator cannot launder junk models into Safe verdicts.
#[test]
#[ntest::timeout(120_000)]
fn soundness_pin_bogus_model_is_rejected_by_original_verification() {
    let problem = safe_tower();
    let result = split(problem.clone());

    // Fabricate the weakest possible model: every clone is `true`.
    let mut bogus = crate::InvariantModel::new();
    for pred in result.problem.predicates() {
        let vars: Vec<ChcVar> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(canonical_var_name(pred.id, i), sort.clone()))
            .collect();
        bogus.set(
            pred.id,
            PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
        );
    }

    let translated = result.back_translator.translate_validity(bogus);
    let mut verifier = PdrSolver::new(problem, bounded_pdr_config());
    assert!(
        !verifier.verify_model(&translated),
        "all-true clone model must fail verification on the original clauses"
    );
}

// ========================================================================
// Constant-environment extraction
// ========================================================================

#[test]
fn const_env_resolves_direct_and_chained_equalities() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let constraint = ChcExpr::and_all([
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(5)),
        ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::var(x.clone())),
    ]);
    let env = constraint_const_env(Some(&constraint));
    assert_eq!(
        occurrence_pc_value(&ChcExpr::var(x), &env),
        Some(ChcExpr::Int(5))
    );
    assert_eq!(
        occurrence_pc_value(&ChcExpr::var(y), &env),
        Some(ChcExpr::Int(5)),
        "var-var chains must propagate"
    );
    assert_eq!(
        occurrence_pc_value(&ChcExpr::Int(7), &env),
        Some(ChcExpr::Int(7))
    );
    let free = ChcVar::new("z", ChcSort::Int);
    assert_eq!(occurrence_pc_value(&ChcExpr::var(free), &env), None);
}
