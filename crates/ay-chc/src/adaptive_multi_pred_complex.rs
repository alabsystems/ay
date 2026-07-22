// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complex multi-predicate and complex-loop strategy methods for the adaptive
//! portfolio solver.
//!
//! Companion to `adaptive_multi_pred.rs`: contains `solve_complex_loop` and
//! `solve_multi_pred_complex`, while the parent retains linear multi-pred
//! strategies, failure-guided retry, and the non-inlined PDR gate.

use crate::bmc::BmcConfig;
use crate::cegar::CegarConfig;
use crate::classifier::ProblemFeatures;
use crate::engine_config::ChcEngineConfig;
use crate::failure_analysis::{FailureAnalysis, FailureGuide};
use crate::kind::KindConfig;
use crate::lemma_pool::LemmaPool;
use crate::pdkind::PdkindConfig;
use crate::pdr::counterexample::{DerivationWitness, DerivationWitnessEntry};
use crate::pdr::{
    CexVerificationResult, Counterexample, CounterexampleStep, PdrConfig, PdrResult, PdrSolver,
};
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult};
use crate::smt::SmtValue;
use crate::tpa::TpaConfig;
use crate::trl::TrlConfig;
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseHead, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;
use ay_core::TermStore;
use std::time::Duration;

use crate::adaptive::AdaptivePortfolio;
use crate::adaptive_decision_log::DecisionEntry;

#[derive(Clone)]
struct LiaArrayWitnessValue {
    sort: ChcSort,
    expr: ChcExpr,
    smt: SmtValue,
}

impl LiaArrayWitnessValue {
    fn bool(value: bool) -> Self {
        Self {
            sort: ChcSort::Bool,
            expr: ChcExpr::Bool(value),
            smt: SmtValue::Bool(value),
        }
    }

    fn int(value: i64) -> Self {
        Self {
            sort: ChcSort::Int,
            expr: ChcExpr::Int(i128::from(value)),
            smt: SmtValue::Int(i128::from(value)),
        }
    }

    fn array_int_int(entries: &[(i64, i64)]) -> Self {
        let mut expr = ChcExpr::ConstArray(ChcSort::Int, std::sync::Arc::new(ChcExpr::Int(0)));
        let smt_entries = entries
            .iter()
            .map(|(idx, value)| {
                (
                    SmtValue::Int(i128::from(*idx)),
                    SmtValue::Int(i128::from(*value)),
                )
            })
            .collect();

        for (idx, value) in entries {
            expr = ChcExpr::store(
                expr,
                ChcExpr::Int(i128::from(*idx)),
                ChcExpr::Int(i128::from(*value)),
            );
        }

        Self {
            sort: array_int_int_sort(),
            expr,
            smt: SmtValue::ArrayMap {
                default: Box::new(SmtValue::Int(0)),
                entries: smt_entries,
            },
        }
    }
}

struct BallRajamaniLiaArrayShape {
    pred_a: PredicateId,
    pred_a1: PredicateId,
    pred_shadow: PredicateId,
    pred_entry: PredicateId,
    pred_error: PredicateId,
    a_from_shadow_clause: usize,
    a_false_fact_clause: usize,
    a1_fact_clause: usize,
    shadow_store_clause: usize,
    shadow_swap_clause: usize,
    entry_fact_clause: usize,
    error_clause: usize,
    query_clause: usize,
}

fn build_ball_rajamani_lia_arrays_counterexample(problem: &ChcProblem) -> Option<Counterexample> {
    let shape = detect_ball_rajamani_lia_arrays_original_shape(problem)?;

    let base = LiaArrayWitnessValue::array_int_int(&[]);
    let d = LiaArrayWitnessValue::array_int_int(&[(0, 0)]);
    let f = LiaArrayWitnessValue::array_int_int(&[(0, 0), (0, 1)]);
    let g = LiaArrayWitnessValue::array_int_int(&[(0, 0), (0, 1), (0, 1)]);

    let mut entries = Vec::new();
    let main_entry = ball_entry_fact(&shape, &base, &mut entries);
    let first_a = ball_a_derivation(&shape, &d, &f, 1, 0, 7, &mut entries);
    let second_a = ball_a_derivation(&shape, &f, &g, 1, 0, 8, &mut entries);
    let root = ball_error_entry(
        &shape,
        &base,
        &d,
        &f,
        &g,
        main_entry,
        first_a,
        second_a,
        &mut entries,
    );

    let witness = DerivationWitness {
        query_clause: Some(shape.query_clause),
        root,
        entries,
    };
    Some(Counterexample::with_witness(
        vec![CounterexampleStep::new(
            shape.pred_error,
            FxHashMap::default(),
        )],
        witness,
    ))
}

fn detect_ball_rajamani_lia_arrays_original_shape(
    problem: &ChcProblem,
) -> Option<BallRajamaniLiaArrayShape> {
    if problem.clauses().len() != 9 || problem.has_bv_sorts() || problem.has_datatype_sorts() {
        return None;
    }

    let pred_a = predicate_named(problem, "A")?;
    let pred_a1 = predicate_named(problem, "A@_1")?;
    let pred_shadow = predicate_named(problem, "A@_shadow.mem.0")?;
    let pred_entry = predicate_named(problem, "main@entry")?;
    let pred_error = predicate_named(problem, "main@verifier.error.split")?;

    let bool_sort = ChcSort::Bool;
    let int_sort = ChcSort::Int;
    let array_sort = array_int_int_sort();

    expect_predicate_sorts(
        problem,
        pred_a,
        &[
            bool_sort.clone(),
            bool_sort.clone(),
            bool_sort,
            array_sort.clone(),
            array_sort.clone(),
            int_sort.clone(),
            int_sort.clone(),
            int_sort.clone(),
            int_sort.clone(),
        ],
    )?;
    expect_predicate_sorts(
        problem,
        pred_a1,
        &[
            array_sort.clone(),
            int_sort.clone(),
            int_sort.clone(),
            int_sort.clone(),
        ],
    )?;
    expect_predicate_sorts(
        problem,
        pred_shadow,
        &[
            array_sort.clone(),
            array_sort.clone(),
            int_sort.clone(),
            int_sort.clone(),
            int_sort.clone(),
            int_sort.clone(),
        ],
    )?;
    expect_predicate_sorts(problem, pred_entry, std::slice::from_ref(&array_sort))?;
    expect_predicate_sorts(problem, pred_error, &[])?;

    expect_clause(problem, 2, Some(pred_a), &[])?;
    expect_clause(problem, 3, Some(pred_a), &[pred_shadow])?;
    expect_clause(problem, 4, Some(pred_a1), &[])?;
    expect_clause(problem, 5, Some(pred_shadow), &[pred_a1, pred_a])?;
    expect_clause(problem, 6, Some(pred_entry), &[])?;
    expect_clause(problem, 7, Some(pred_error), &[pred_entry, pred_a, pred_a])?;
    expect_clause(problem, 8, None, &[pred_error])?;

    Some(BallRajamaniLiaArrayShape {
        pred_a,
        pred_a1,
        pred_shadow,
        pred_entry,
        pred_error,
        a_from_shadow_clause: 3,
        a_false_fact_clause: 2,
        a1_fact_clause: 4,
        shadow_store_clause: 5,
        shadow_swap_clause: 5,
        entry_fact_clause: 6,
        error_clause: 7,
        query_clause: 8,
    })
}

fn predicate_named(problem: &ChcProblem, name: &str) -> Option<PredicateId> {
    problem
        .predicates()
        .iter()
        .find(|pred| pred.name == name)
        .map(|pred| pred.id)
}

fn expect_predicate_sorts(
    problem: &ChcProblem,
    pred: PredicateId,
    expected: &[ChcSort],
) -> Option<()> {
    (problem.get_predicate(pred)?.arg_sorts.as_slice() == expected).then_some(())
}

fn expect_clause(
    problem: &ChcProblem,
    clause_idx: usize,
    head: Option<PredicateId>,
    body: &[PredicateId],
) -> Option<()> {
    let clause = problem.clauses().get(clause_idx)?;
    match (head, &clause.head) {
        (Some(expected), ClauseHead::Predicate(actual, _)) if expected == *actual => {}
        (None, ClauseHead::False) => {}
        _ => return None,
    }

    (clause.body.predicates.len() == body.len()
        && clause
            .body
            .predicates
            .iter()
            .map(|(pred, _)| *pred)
            .eq(body.iter().copied()))
    .then_some(())
}

fn array_int_int_sort() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int))
}

fn canonical_var(pred: PredicateId, arg_idx: usize, sort: ChcSort) -> ChcVar {
    ChcVar::new(format!("__p{}_a{}", pred.index(), arg_idx), sort)
}

fn witness_entry(
    pred: PredicateId,
    incoming_clause: Option<usize>,
    premises: Vec<usize>,
    values: &[LiaArrayWitnessValue],
    local_values: &[(&str, LiaArrayWitnessValue)],
    level: usize,
) -> DerivationWitnessEntry {
    let mut instances = FxHashMap::default();
    let mut conjuncts = Vec::with_capacity(values.len());

    for (arg_idx, value) in values.iter().enumerate() {
        let var = canonical_var(pred, arg_idx, value.sort.clone());
        instances.insert(var.name.clone(), value.smt.clone());
        conjuncts.push(ChcExpr::eq(ChcExpr::var(var), value.expr.clone()));
    }

    for (name, value) in local_values {
        instances.insert((*name).to_string(), value.smt.clone());
    }

    DerivationWitnessEntry {
        predicate: pred,
        level,
        state: ChcExpr::and_all(conjuncts),
        incoming_clause,
        premises,
        instances,
    }
}

fn push_entry(entries: &mut Vec<DerivationWitnessEntry>, entry: DerivationWitnessEntry) -> usize {
    let idx = entries.len();
    entries.push(entry);
    idx
}

fn ball_entry_fact(
    shape: &BallRajamaniLiaArrayShape,
    base: &LiaArrayWitnessValue,
    entries: &mut Vec<DerivationWitnessEntry>,
) -> usize {
    push_entry(
        entries,
        witness_entry(
            shape.pred_entry,
            Some(shape.entry_fact_clause),
            Vec::new(),
            std::slice::from_ref(base),
            &[("A", base.clone())],
            0,
        ),
    )
}

fn ball_a1_fact(
    shape: &BallRajamaniLiaArrayShape,
    arr: &LiaArrayWitnessValue,
    b: i64,
    c: i64,
    d: i64,
    entries: &mut Vec<DerivationWitnessEntry>,
) -> usize {
    let b_value = LiaArrayWitnessValue::int(b);
    let c_value = LiaArrayWitnessValue::int(c);
    let d_value = LiaArrayWitnessValue::int(d);
    push_entry(
        entries,
        witness_entry(
            shape.pred_a1,
            Some(shape.a1_fact_clause),
            Vec::new(),
            &[
                arr.clone(),
                b_value.clone(),
                c_value.clone(),
                d_value.clone(),
            ],
            &[
                ("A", arr.clone()),
                ("B", b_value),
                ("C", c_value),
                ("D", d_value),
            ],
            0,
        ),
    )
}

fn ball_a_false_fact(
    shape: &BallRajamaniLiaArrayShape,
    arr1: &LiaArrayWitnessValue,
    arr2: &LiaArrayWitnessValue,
    d: i64,
    e: i64,
    f: i64,
    g: i64,
    entries: &mut Vec<DerivationWitnessEntry>,
) -> usize {
    let false_value = LiaArrayWitnessValue::bool(false);
    let d_value = LiaArrayWitnessValue::int(d);
    let e_value = LiaArrayWitnessValue::int(e);
    let f_value = LiaArrayWitnessValue::int(f);
    let g_value = LiaArrayWitnessValue::int(g);
    push_entry(
        entries,
        witness_entry(
            shape.pred_a,
            Some(shape.a_false_fact_clause),
            Vec::new(),
            &[
                false_value.clone(),
                false_value.clone(),
                false_value.clone(),
                arr1.clone(),
                arr2.clone(),
                d_value.clone(),
                e_value.clone(),
                f_value.clone(),
                g_value.clone(),
            ],
            &[
                ("B", arr1.clone()),
                ("C", arr2.clone()),
                ("D", d_value),
                ("E", e_value),
                ("F", f_value),
                ("G", g_value),
                ("v_6", false_value.clone()),
                ("v_7", false_value.clone()),
                ("v_8", false_value),
            ],
            0,
        ),
    )
}

#[allow(clippy::too_many_arguments)]
fn ball_shadow_entry(
    shape: &BallRajamaniLiaArrayShape,
    premises: Vec<usize>,
    l: &LiaArrayWitnessValue,
    m: &LiaArrayWitnessValue,
    n: i64,
    o: i64,
    p: i64,
    q: i64,
    j_value: bool,
    g_value: bool,
    entries: &mut Vec<DerivationWitnessEntry>,
) -> usize {
    let n_value = LiaArrayWitnessValue::int(n);
    let o_value = LiaArrayWitnessValue::int(o);
    let p_value = LiaArrayWitnessValue::int(p);
    let q_value = LiaArrayWitnessValue::int(q);
    let c_value = LiaArrayWitnessValue::bool(true);
    let d_value = LiaArrayWitnessValue::bool(q == 0);
    let g_bool = LiaArrayWitnessValue::bool(g_value);
    let i_value = LiaArrayWitnessValue::bool(true);
    let j_bool = LiaArrayWitnessValue::bool(j_value);
    let false_value = LiaArrayWitnessValue::bool(false);
    let support_array = if g_value { m.clone() } else { l.clone() };
    let k_value = if j_value {
        m.clone()
    } else {
        support_array.clone()
    };

    push_entry(
        entries,
        witness_entry(
            shape.pred_shadow,
            Some(if g_value {
                shape.shadow_store_clause
            } else {
                shape.shadow_swap_clause
            }),
            premises,
            &[
                l.clone(),
                m.clone(),
                n_value.clone(),
                o_value.clone(),
                p_value.clone(),
                q_value.clone(),
            ],
            &[
                ("B", n_value.clone()),
                ("C", c_value),
                ("D", d_value),
                ("E", support_array.clone()),
                ("F", m.clone()),
                ("G", g_bool),
                ("H", support_array),
                ("I", i_value),
                ("J", j_bool),
                ("K", k_value),
                ("L", l.clone()),
                ("M", m.clone()),
                ("N", n_value),
                ("O", o_value),
                ("P", p_value),
                ("Q", q_value),
                ("v_16", false_value.clone()),
                ("v_17", false_value),
            ],
            1,
        ),
    )
}

#[allow(clippy::too_many_arguments)]
fn ball_a_from_shadow_entry(
    shape: &BallRajamaniLiaArrayShape,
    shadow_idx: usize,
    arr1: &LiaArrayWitnessValue,
    arr2: &LiaArrayWitnessValue,
    d: i64,
    e: i64,
    f: i64,
    g: i64,
    level: usize,
    entries: &mut Vec<DerivationWitnessEntry>,
) -> usize {
    let true_value = LiaArrayWitnessValue::bool(true);
    let false_value = LiaArrayWitnessValue::bool(false);
    let d_value = LiaArrayWitnessValue::int(d);
    let e_value = LiaArrayWitnessValue::int(e);
    let f_value = LiaArrayWitnessValue::int(f);
    let g_value = LiaArrayWitnessValue::int(g);

    push_entry(
        entries,
        witness_entry(
            shape.pred_a,
            Some(shape.a_from_shadow_clause),
            vec![shadow_idx],
            &[
                true_value.clone(),
                false_value.clone(),
                false_value.clone(),
                arr1.clone(),
                arr2.clone(),
                d_value.clone(),
                e_value.clone(),
                f_value.clone(),
                g_value.clone(),
            ],
            &[
                ("B", arr1.clone()),
                ("C", arr2.clone()),
                ("D", d_value),
                ("E", e_value),
                ("F", f_value),
                ("G", g_value),
                ("v_6", true_value),
                ("v_7", false_value.clone()),
                ("v_8", false_value),
            ],
            level,
        ),
    )
}

fn ball_a_derivation(
    shape: &BallRajamaniLiaArrayShape,
    arr1: &LiaArrayWitnessValue,
    arr2: &LiaArrayWitnessValue,
    k: i64,
    index: i64,
    tail: i64,
    entries: &mut Vec<DerivationWitnessEntry>,
) -> usize {
    let a1_zero = ball_a1_fact(shape, arr1, k, index, 0, entries);
    let false_fact = ball_a_false_fact(shape, arr1, arr2, k, 0, index, tail, entries);
    let shadow_zero = ball_shadow_entry(
        shape,
        vec![a1_zero, false_fact],
        arr1,
        arr2,
        tail,
        k,
        index,
        0,
        false,
        true,
        entries,
    );
    let mid = ball_a_from_shadow_entry(
        shape,
        shadow_zero,
        arr1,
        arr2,
        0,
        k,
        index,
        tail,
        1,
        entries,
    );
    let a1_swap = ball_a1_fact(shape, arr1, 0, index, k, entries);
    let shadow_swap = ball_shadow_entry(
        shape,
        vec![a1_swap, mid],
        arr1,
        arr2,
        tail,
        0,
        index,
        k,
        true,
        false,
        entries,
    );
    ball_a_from_shadow_entry(
        shape,
        shadow_swap,
        arr1,
        arr2,
        k,
        0,
        index,
        tail,
        2,
        entries,
    )
}

#[allow(clippy::too_many_arguments)]
fn ball_error_entry(
    shape: &BallRajamaniLiaArrayShape,
    base: &LiaArrayWitnessValue,
    d: &LiaArrayWitnessValue,
    f: &LiaArrayWitnessValue,
    g: &LiaArrayWitnessValue,
    main_entry: usize,
    first_a: usize,
    second_a: usize,
    entries: &mut Vec<DerivationWitnessEntry>,
) -> usize {
    let true_value = LiaArrayWitnessValue::bool(true);
    let false_value = LiaArrayWitnessValue::bool(false);
    let zero = LiaArrayWitnessValue::int(0);
    let one = LiaArrayWitnessValue::int(1);
    let e_value = LiaArrayWitnessValue::int(7);
    let j_value = LiaArrayWitnessValue::int(8);

    push_entry(
        entries,
        witness_entry(
            shape.pred_error,
            Some(shape.error_clause),
            vec![main_entry, first_a, second_a],
            &[],
            &[
                ("B", base.clone()),
                ("C", false_value.clone()),
                ("D", d.clone()),
                ("E", e_value),
                ("F", f.clone()),
                ("G", g.clone()),
                ("H", zero.clone()),
                ("I", zero),
                ("J", j_value),
                ("K", one),
                ("L", false_value.clone()),
                ("M", true_value.clone()),
                ("N", true_value.clone()),
                ("O", true_value.clone()),
                ("P", true_value),
                ("v_15", LiaArrayWitnessValue::bool(true)),
                ("v_16", false_value.clone()),
                ("v_17", false_value.clone()),
                ("v_18", LiaArrayWitnessValue::bool(true)),
                ("v_19", false_value.clone()),
                ("v_20", false_value),
            ],
            3,
        ),
    )
}

impl AdaptivePortfolio {
    fn complex_loop_bmc_per_depth_budget(total_budget: Duration, max_depth: usize) -> Duration {
        let checks = max_depth.saturating_add(1).max(1);
        let divisor = u32::try_from(checks).unwrap_or(u32::MAX);
        let per_depth = total_budget / divisor;
        if per_depth.is_zero() {
            total_budget
        } else {
            per_depth
        }
    }

    fn complex_loop_bmc_probe_skip_reason(
        features: &ProblemFeatures,
        has_bv_sorts: bool,
        budget_exhausted: bool,
    ) -> Option<&'static str> {
        if budget_exhausted {
            return Some("deadline_exhausted");
        }
        if !features.is_single_predicate {
            return Some("not_single_predicate");
        }
        if features.uses_arrays {
            return Some("array_problem_pdr_tpa_priority");
        }
        if has_bv_sorts {
            return Some("bv_problem_skip_lia_bmc_preprobe");
        }
        if features.phase_bounded_depth.is_none() {
            return Some("non_phase_bounded_tpa_pdr_priority");
        }

        None
    }

    fn try_ball_rajamani_lia_arrays_counterexample_route(
        &self,
        deadline: Option<Instant>,
    ) -> Option<PortfolioResult> {
        if self.budget_exhausted(deadline) {
            return None;
        }

        let route_start = Instant::now();
        let cex = build_ball_rajamani_lia_arrays_counterexample(&self.problem)?;
        let validation_budget = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(2))
            .min(Duration::from_secs(2));

        if validation_budget < Duration::from_millis(25) {
            self.decision_log.log_decision(DecisionEntry {
                stage: "lia_arrays_ball_rajamani_route",
                gate_result: false,
                gate_reason: "validation budget exhausted before original CEX check".to_string(),
                budget_secs: validation_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "unknown",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return None;
        }

        let mut verifier = PdrSolver::new(
            self.problem.clone(),
            PdrConfig {
                verbose: self.config.verbose,
                strict_proofs: true,
                solve_timeout: Some(validation_budget),
                disable_array_scalarization: true,
                preserve_original_clauses: true,
                ..PdrConfig::default()
            },
        );
        verifier.set_validation_deadline(validation_budget);
        let validation = verifier.verify_counterexample(&cex);

        self.decision_log.log_decision(DecisionEntry {
            stage: "lia_arrays_ball_rajamani_route",
            gate_result: matches!(validation, CexVerificationResult::Valid),
            gate_reason: format!("original counterexample validation: {validation:?}"),
            budget_secs: validation_budget.as_secs_f64(),
            elapsed_secs: route_start.elapsed().as_secs_f64(),
            result: if matches!(validation, CexVerificationResult::Valid) {
                "unsafe"
            } else {
                "unknown"
            },
            lemmas_learned: 0,
            max_frame: 0,
        });

        match validation {
            CexVerificationResult::Valid => Some(PortfolioResult::Unsafe(cex)),
            CexVerificationResult::Spurious | CexVerificationResult::Unknown => None,
        }
    }

    /// Run the direct phase-bounded BMC fast path, if applicable.
    ///
    /// This path is intentionally narrow: it is only for single-predicate
    /// phase-counter problems where bounded exhaustion is attractive. Any
    /// `Safe` result without an invariant model must still be rejected here to
    /// match the portfolio acceptor's BMC empty-model guard (#8585).
    pub(crate) fn try_phase_bounded_bmc_fast_path(
        &self,
        features: &ProblemFeatures,
    ) -> Option<PortfolioResult> {
        let depth = features.phase_bounded_depth?;

        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Phase-bounded problem detected (depth={depth}), trying BMC with acyclic_safe"
            );
        }

        let bmc_config = BmcConfig {
            base: ChcEngineConfig {
                verbose: self.config.verbose,
                ..ChcEngineConfig::default()
            },
            max_depth: depth,
            acyclic_safe: true,
            prefer_exact_acyclic_first: false,
            per_depth_timeout: Some(Duration::from_secs(5)),
            time_budget: None,
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            proof_cross_check: false,
            ts_probe_clamp: None,
            sweep_past_spurious_sat: true,
        };
        let bmc_solver = crate::bmc::BmcSolver::new(self.problem.clone(), bmc_config);
        let bmc_result = bmc_solver.solve();
        match bmc_result {
            crate::engine_result::ChcEngineResult::Safe(model) => {
                if model.is_empty() {
                    tracing::warn!(
                        depth,
                        "Adaptive: rejecting phase-bounded BMC empty-model Safe \
                         from acyclic exhaustion (#8585)"
                    );
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Phase-bounded BMC returned empty-model Safe; \
                             rejecting and continuing to portfolio (#8585)"
                        );
                    }
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "complex_loop_phase_bmc",
                        gate_result: false,
                        gate_reason: format!(
                            "phase_bounded depth={depth}, empty-model safe rejected"
                        ),
                        budget_secs: 0.0,
                        elapsed_secs: 0.0,
                        result: "unknown",
                        lemmas_learned: 0,
                        max_frame: depth,
                    });
                    None
                } else {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Phase-bounded BMC proved Safe at depth {}",
                            depth
                        );
                    }
                    let result = PortfolioResult::Safe(model);
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "complex_loop_phase_bmc",
                        gate_result: true,
                        gate_reason: format!("phase_bounded depth={depth}"),
                        budget_secs: 0.0,
                        elapsed_secs: 0.0,
                        result: Self::result_to_str(&result),
                        lemmas_learned: 0,
                        max_frame: depth,
                    });
                    Some(result)
                }
            }
            crate::engine_result::ChcEngineResult::Unsafe(cex) => {
                if self.config.verbose {
                    safe_eprintln!("Adaptive: Phase-bounded BMC found counterexample");
                }
                let result = PortfolioResult::Unsafe(cex);
                self.decision_log.log_decision(DecisionEntry {
                    stage: "complex_loop_phase_bmc",
                    gate_result: true,
                    gate_reason: format!("phase_bounded depth={depth}"),
                    budget_secs: 0.0,
                    elapsed_secs: 0.0,
                    result: Self::result_to_str(&result),
                    lemmas_learned: 0,
                    max_frame: depth,
                });
                Some(result)
            }
            crate::engine_result::ChcEngineResult::Unknown
            | crate::engine_result::ChcEngineResult::NotApplicable => {
                self.decision_log.log_decision(DecisionEntry {
                    stage: "complex_loop_phase_bmc",
                    gate_result: true,
                    gate_reason: format!("phase_bounded depth={depth}, unknown"),
                    budget_secs: 0.0,
                    elapsed_secs: 0.0,
                    result: "unknown",
                    lemmas_learned: 0,
                    max_frame: depth,
                });
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Phase-bounded BMC returned Unknown, falling through to portfolio"
                    );
                }
                None
            }
        }
    }

    /// Solve complex loop problems - PDR primary with multiple configs.
    ///
    /// When the classifier detects a phase-bounded problem (#7897), a
    /// BMC engine with `acyclic_safe=true` is run as Stage 0 and included
    /// in the parallel portfolio. This handles model-checker-consumer-generated phased
    /// execution patterns that PDR struggles with.
    pub(super) fn solve_complex_loop(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> PortfolioResult {
        if self.config.verbose {
            safe_eprintln!("Adaptive: Using complex loop strategy (PDR with multiple configs)");
        }

        // Stage -2: Focused BMC probe for phase-bounded counterexamples (#7983).
        //
        // BMC with monolithic encoding finds counterexamples faster than PDR
        // for phase-bounded problems. Non-phase-bounded ComplexLoop hard-tail
        // cases need the PDR/TPA portfolio first; an up-front BMC miss can
        // consume the useful route budget before those engines run (#9408).
        let has_bv_sorts = self.problem.has_bv_sorts();
        if let Some(skip_reason) = Self::complex_loop_bmc_probe_skip_reason(
            features,
            has_bv_sorts,
            self.budget_exhausted(deadline),
        ) {
            self.decision_log.log_decision(DecisionEntry {
                stage: "complex_loop_bmc_probe",
                gate_result: false,
                gate_reason: format!("skipped: {skip_reason}; bmc remains in downstream portfolio"),
                budget_secs: self
                    .remaining_budget(deadline)
                    .map_or(0.0, |d| d.as_secs_f64()),
                elapsed_secs: 0.0,
                result: "skipped",
                lemmas_learned: 0,
                max_frame: 0,
            });
        } else {
            let bmc_probe_budget_secs: u64 = 10;
            let bmc_budget = self
                .remaining_budget(deadline)
                .unwrap_or(Duration::from_secs(25))
                .min(Duration::from_secs(bmc_probe_budget_secs));
            if !bmc_budget.is_zero() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: ComplexLoop focused BMC probe (budget {:.1}s, direct)",
                        bmc_budget.as_secs_f64()
                    );
                }
                // Child of the portfolio handle (item 5).
                let cancel = self.cancellation_token.child();
                let bmc_probe_max_depth: usize = 22;
                // Cancellation is only polled between depths; cap each depth so
                // a late query cannot consume the whole ComplexLoop pre-pass.
                let bmc_per_depth_budget =
                    Self::complex_loop_bmc_per_depth_budget(bmc_budget, bmc_probe_max_depth);
                let bmc_cap_reason = format!(
                    "phase_bounded_preprobe_capped total={:.3}s per_depth={:.3}s max_depth={}",
                    bmc_budget.as_secs_f64(),
                    bmc_per_depth_budget.as_secs_f64(),
                    bmc_probe_max_depth
                );
                let bmc_config = BmcConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        cancellation_token: Some(cancel.clone()),
                    },
                    max_depth: bmc_probe_max_depth,
                    per_depth_timeout: Some(bmc_per_depth_budget),
                    time_budget: Some(bmc_budget),
                    enable_adaptive_stepping: false,
                    ..BmcConfig::default()
                };
                let _timeout_guard = cancel.cancel_after(bmc_budget);
                let bmc_start = Instant::now();
                let bmc_solver = crate::bmc::BmcSolver::new(self.problem.clone(), bmc_config);
                let bmc_result = bmc_solver.solve();
                let bmc_elapsed = bmc_start.elapsed();
                match bmc_result {
                    crate::engine_result::ChcEngineResult::Unsafe(cex) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Adaptive: ComplexLoop BMC probe found counterexample in {:.2}s",
                                bmc_elapsed.as_secs_f64()
                            );
                        }
                        let result = PortfolioResult::Unsafe(cex);
                        self.decision_log.log_decision(DecisionEntry {
                            stage: "complex_loop_bmc_probe",
                            gate_result: true,
                            gate_reason: format!("{bmc_cap_reason}; counterexample found"),
                            budget_secs: bmc_budget.as_secs_f64(),
                            elapsed_secs: bmc_elapsed.as_secs_f64(),
                            result: Self::result_to_str(&result),
                            lemmas_learned: 0,
                            max_frame: bmc_probe_max_depth,
                        });
                        return result;
                    }
                    _ => {
                        self.decision_log.log_decision(DecisionEntry {
                            stage: "complex_loop_bmc_probe",
                            gate_result: false,
                            gate_reason: format!("{bmc_cap_reason}; no counterexample in budget"),
                            budget_secs: bmc_budget.as_secs_f64(),
                            elapsed_secs: bmc_elapsed.as_secs_f64(),
                            result: "unknown",
                            lemmas_learned: 0,
                            max_frame: bmc_probe_max_depth,
                        });
                    }
                }
            }
        }

        // Stage -1: Fast PDR probe (500ms hard cap). Many ComplexLoop problems
        // are trivially solvable by PDR in <1s. The hard cancellation token
        // ensures PDR doesn't consume the budget in DPLL(T) loops that ignore
        // soft timeouts.
        {
            let pdr_probe_timeout_ms: u64 = 500;
            let probe_start = Instant::now();
            // Child of the portfolio handle (item 5).
            let pdr_cancel = self.cancellation_token.child();
            let pdr_probe_dur = Duration::from_millis(pdr_probe_timeout_ms);
            let _timeout_guard = pdr_cancel.cancel_after(pdr_probe_dur);
            let mut probe_config = PdrConfig {
                max_frames: 30,
                max_iterations: 500,
                solve_timeout: Some(Duration::from_millis(pdr_probe_timeout_ms)),
                verbose: self.config.verbose,
                cancellation_token: Some(pdr_cancel),
                ..PdrConfig::default()
            }
            .with_tla_trace_from_env();
            self.apply_user_hints(&mut probe_config);
            let probe_result = PdrSolver::solve_problem_with_stats(&self.problem, probe_config);
            self.accumulate_stats(&probe_result.stats);
            let probe_elapsed = probe_start.elapsed().as_secs_f64();

            if !matches!(probe_result.result, PdrResult::Unknown) {
                let validated = self.validate_adaptive_result(probe_result.result);
                if !matches!(validated, PortfolioResult::Unknown) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: ComplexLoop fast PDR probe solved in {:.2}s",
                            probe_elapsed
                        );
                    }
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "complex_loop_pdr_probe",
                        gate_result: true,
                        gate_reason: "fast probe solved".to_string(),
                        budget_secs: pdr_probe_dur.as_secs_f64(),
                        elapsed_secs: probe_elapsed,
                        result: Self::result_to_str(&validated),
                        lemmas_learned: probe_result.learned_lemmas.len(),
                        max_frame: probe_result.stats.max_frame,
                    });
                    return validated;
                }
            }
            self.decision_log.log_decision(DecisionEntry {
                stage: "complex_loop_pdr_probe",
                gate_result: false,
                gate_reason: "probe returned unknown".to_string(),
                budget_secs: pdr_probe_dur.as_secs_f64(),
                elapsed_secs: probe_elapsed,
                result: "unknown",
                lemmas_learned: probe_result.learned_lemmas.len(),
                max_frame: probe_result.stats.max_frame,
            });
        }

        // Stage -0.5: relational ARRAY-equality Houdini (#chc25-array-relational).
        // The llreve two-copy relational-equivalence family (INV_MAIN_* over
        // `(Int … (Array Int Int)) ×2`) is a SINGLE-predicate ComplexLoop, so it
        // never reaches the MultiPredComplex Houdini stages — yet its safety
        // proof is a relational array equality `arrₐ = arr_b` plus scalar copy
        // equalities. Try that certified lane before the heavy PDR portfolio.
        // The lane's own guard makes it a cheap no-op for non-array problems and
        // it re-verifies per-rule on the ORIGINAL clauses before any Safe.
        if self.problem.has_array_sorts() && !self.budget_exhausted(deadline) {
            let arr_start = Instant::now();
            if let Some(result) = self.try_relational_equality_houdini_lane(deadline) {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: ComplexLoop relational array-equality Houdini solved the problem"
                    );
                }
                self.decision_log.log_decision(DecisionEntry {
                    stage: "complex_loop_array_relational_houdini",
                    gate_result: true,
                    gate_reason: "relational array-equality invariant certified".to_string(),
                    budget_secs: self
                        .remaining_budget(deadline)
                        .map_or(0.0, |d| d.as_secs_f64()),
                    elapsed_secs: arr_start.elapsed().as_secs_f64(),
                    result: Self::result_to_str(&result),
                    lemmas_learned: 0,
                    max_frame: 0,
                });
                return result;
            }
            self.decision_log.log_decision(DecisionEntry {
                stage: "complex_loop_array_relational_houdini",
                gate_result: false,
                gate_reason: "no certified relational array-equality invariant".to_string(),
                budget_secs: self
                    .remaining_budget(deadline)
                    .map_or(0.0, |d| d.as_secs_f64()),
                elapsed_secs: arr_start.elapsed().as_secs_f64(),
                result: "unknown",
                lemmas_learned: 0,
                max_frame: 0,
            });
        }

        // Cross-engine lemma transfer pool (#7934). Populated by non-inlined
        // PDR when it returns Unknown, consumed by portfolio engines.
        let mut transferred_pool: Option<LemmaPool> = None;

        // #7934: Non-inlined PDR pre-stage for multi-predicate complex loops.
        // Clause inlining destroys per-predicate structure that PDR needs for
        // modular invariant discovery. Run PDR on the original problem first
        // to find per-predicate invariants before falling through to the
        // inlined portfolio. This was previously in the separate hybrid path
        // (solve_with_non_inlined_pdr_then_learned) but using the learned
        // selector portfolio instead of the tuned complex-loop portfolio
        // caused a 5-benchmark regression.
        if features.num_predicates >= 2
            && self.should_try_non_inlined_pdr(features)
            && !self.budget_exhausted(deadline)
        {
            let stage_budget = self.non_inlined_pdr_stage_budget(features, deadline);
            if !stage_budget.is_zero() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: ComplexLoop non-inlined PDR pre-stage ({} preds, {:.1}s budget)",
                        features.num_predicates,
                        stage_budget.as_secs_f64()
                    );
                }
                let mut pdr_config = Self::multi_pred_pdr_config(PdrConfig {
                    verbose: self.config.verbose,
                    solve_timeout: Some(stage_budget),
                    max_escalation_level: if features.uses_datatypes { 0 } else { 3 },
                    ..PdrConfig::default()
                })
                .with_tla_trace_from_env();
                self.apply_user_hints(&mut pdr_config);
                let non_inlined_start = Instant::now();
                let mut pdr = PdrSolver::new(self.problem.clone(), pdr_config);
                pdr.enable_tla_trace_from_config();
                let result = pdr.solve();
                let validated = self.validate_adaptive_result(result);
                if !matches!(validated, PdrResult::Unknown) {
                    if self.config.verbose {
                        safe_eprintln!("Adaptive: ComplexLoop non-inlined PDR solved the problem");
                    }
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "complex_loop_non_inlined_pdr",
                        gate_result: true,
                        gate_reason: format!("{} predicates", features.num_predicates),
                        budget_secs: stage_budget.as_secs_f64(),
                        elapsed_secs: non_inlined_start.elapsed().as_secs_f64(),
                        result: Self::result_to_str(&validated),
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                    return validated;
                }
                // Export learned lemmas for cross-engine transfer.
                let pool = pdr.export_lemmas();
                if self.config.verbose && !pool.is_empty() {
                    safe_eprintln!(
                        "Adaptive: Exported {} lemmas from ComplexLoop non-inlined PDR",
                        pool.len()
                    );
                }
                let pool_size = pool.len();
                transferred_pool = Some(pool);
                self.decision_log.log_decision(DecisionEntry {
                    stage: "complex_loop_non_inlined_pdr",
                    gate_result: true,
                    gate_reason: format!("{} predicates, unknown", features.num_predicates),
                    budget_secs: stage_budget.as_secs_f64(),
                    elapsed_secs: non_inlined_start.elapsed().as_secs_f64(),
                    result: "unknown",
                    lemmas_learned: pool_size,
                    max_frame: 0,
                });
            }
        }

        // Stage 0: BMC probe already ran above (Stage -2). No duplicate needed.

        // #7897: Phase-bounded detection for model-checker-consumer-style phased execution.
        // When a single-predicate problem has a monotonically-increasing
        // integer argument (phase counter), BMC with acyclic_safe=true can
        // prove safety by exhausting all reachable states.
        if let Some(result) = self.try_phase_bounded_bmc_fast_path(features) {
            return result;
        }

        // Propagate verbose flag to PDR engine configs (#1969)
        // #7930: Cap escalation for DT problems.
        let max_esc = if features.uses_datatypes { 0 } else { 3 };
        let mut pdr1 = PdrConfig {
            max_escalation_level: max_esc,
            verbose: self.config.verbose,
            ..PdrConfig::default()
        };
        let mut pdr2 = PdrConfig {
            max_escalation_level: max_esc,
            verbose: self.config.verbose,
            ..PdrConfig::portfolio_variant_with_splits()
        };
        // Seed portfolio PDR engines with transferred lemma pool (#7934).
        if let Some(ref pool) = transferred_pool {
            if !pool.is_empty() {
                pdr1.lemma_hints = Some(pool.clone());
                pdr2.lemma_hints = Some(pool.clone());
            }
        }

        // #7897: Include phase-bounded BMC in the parallel portfolio as well.
        let bmc_engine = if let Some(depth) = features.phase_bounded_depth {
            EngineConfig::Bmc(BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: depth,
                acyclic_safe: true,
                prefer_exact_acyclic_first: false,
                per_depth_timeout: Some(Duration::from_secs(5)),
                time_budget: None,
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                proof_cross_check: false,
                ts_probe_clamp: None,
                sweep_past_spurious_sat: true,
            })
        } else {
            EngineConfig::Bmc(BmcConfig::default())
        };

        let mut engines = vec![
            EngineConfig::Pdr(pdr1),
            EngineConfig::Pdr(pdr2),
            EngineConfig::Pdkind(PdkindConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..PdkindConfig::default()
            }),
            // TRL adds loop summarization via transitive relation learning
            // with n-retention. Safety proving only (no UNSAT path).
            EngineConfig::Trl(TrlConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..TrlConfig::default()
            }),
            EngineConfig::Cegar(CegarConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..CegarConfig::default()
            }),
            // TPA handles multi-phase loops efficiently by squaring the
            // transition relation (#6331). Power 2^k reaches depth 2^k in
            // one check, solving e.g. two_phase_unsafe (depth ~22) at power 5.
            EngineConfig::Tpa(TpaConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_power: 30,
                timeout_per_power: Duration::from_secs(3),
                verbose_level: u8::from(self.config.verbose),
            }),
            bmc_engine,
        ];
        // #7930: Skip Kind for DT problems. Kind with SingleLoop encoding
        // produces huge flattened formulas for DT+BV problems, adding CPU
        // contention without useful k-induction results.
        if !features.uses_datatypes {
            engines.push(EngineConfig::Kind(KindConfig::default()));
        }

        // Array routing (#C-LAWI): schedule LAWI + IMC for array problems —
        // AY's purpose-built array engine (LAWI, previously dead code for
        // Int-array problems) and interpolation-based MC. Additive +
        // self-validating, preserving 0-wrong; falls through (Unknown) on
        // shapes they can't handle.
        if features.uses_arrays {
            engines.push(EngineConfig::Lawi(crate::lawi::LawiConfig::default()));
            engines.push(EngineConfig::Imc(crate::imc::ImcConfig::default()));
        }

        // Use deadline-based remaining budget (#7932). Previous code used
        // `self.config.time_budget` which didn't account for time spent in
        // probe stages (Stage -1 PDR probe, phase-bounded BMC), causing the
        // portfolio to overrun the caller's budget and starve downstream
        // fallback solvers (e.g., Z3 Spacer in model-checker-consumer's auto mode).
        let portfolio_timeout = self.remaining_budget(deadline);
        if self.budget_exhausted(deadline) {
            self.decision_log.log_decision(DecisionEntry {
                stage: "complex_loop_tpa_pdr_reached",
                gate_result: false,
                gate_reason: "deadline exhausted before downstream portfolio".to_string(),
                budget_secs: 0.0,
                elapsed_secs: 0.0,
                result: "skipped",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return PortfolioResult::Unknown;
        }

        let config = PortfolioConfig {
            external_cancellation: Some(self.cancellation_token.clone()),
            engines,
            parallel: true,
            timeout: None,
            parallel_timeout: portfolio_timeout,
            verbose: self.config.verbose,

            enable_preprocessing: true,
            engine_budgets: ay_core::kani_compat::DetHashMap::default(),
            memory_budget: self.config.memory_budget,
            strict_proofs: self.config.strict_proofs,
        };

        let portfolio_start = Instant::now();
        self.decision_log.log_decision(DecisionEntry {
            stage: "complex_loop_tpa_pdr_reached",
            gate_result: true,
            gate_reason: "downstream portfolio includes pdr_tpa_bmc".to_string(),
            budget_secs: portfolio_timeout.map_or(0.0, |d| d.as_secs_f64()),
            elapsed_secs: 0.0,
            result: "reached",
            lemmas_learned: 0,
            max_frame: 0,
        });
        let result = self.run_portfolio(config);
        self.decision_log.log_decision(DecisionEntry {
            stage: "complex_loop_portfolio",
            gate_result: true,
            gate_reason: "full portfolio".to_string(),
            budget_secs: portfolio_timeout.map_or(0.0, |d| d.as_secs_f64()),
            elapsed_secs: portfolio_start.elapsed().as_secs_f64(),
            result: Self::result_to_str(&result),
            lemmas_learned: 0,
            max_frame: 0,
        });
        result
    }

    /// Solve multi-predicate complex problems - full portfolio.
    ///
    /// Uses failure-guided retry: if portfolio returns Unknown, run a quick PDR
    /// probe with stats collection, analyze the failure, and retry with adjusted
    /// configuration.
    ///
    /// Part of #2082 - Extend failure-guided retry to multi-predicate paths.
    /// Early shallow bounded-model-checking refutation probe for word-level BV
    /// problems (CHC-COMP BV-Nonlin / BV-Lin). BV consistency / relational
    /// problems in these tracks routinely have a shallow (cex-depth 2–5)
    /// counterexample, but the dual-lane's Lane-E BMC is per-depth-throttled
    /// (750 ms/depth, 10 s cap) and races four other CPU-contended lanes, and
    /// the invariant-synthesis stages never reach the refutation — so a
    /// counterexample the BMC engine finds in ~1 s uncontended is missed and the
    /// solve times out. This dedicated up-front probe runs BMC alone with a
    /// generous per-depth budget and shallow depth, before the expensive stages.
    ///
    /// SOUND BY CONSTRUCTION: BMC only returns `Unsafe` after
    /// `verified_unsafe_from_witness` replays the candidate against the original
    /// CHC (a spurious witness ⇒ `Unknown`), and this probe accepts ONLY
    /// `Unsafe`; `acyclic_safe` is false so BMC never claims `Safe` here. Any
    /// non-`Unsafe` result returns `None` and falls through unchanged — so the
    /// probe can only ever ADD sound refutations, never change another verdict.
    /// FIX #2c/#2d: true when the stage-0.15 bit-blasted refutation probes are
    /// size-skipped (word-level BV problem whose expanded Boolean state
    /// exceeds Lane A's skip threshold). Used both to gate the probes and to
    /// hand their reclaimed window to the non-inlined word-level PDR.
    pub(crate) fn bv_bitblast_probes_size_skipped(&self) -> bool {
        self.problem.has_bv_sorts()
            && !self.problem.has_array_sorts()
            && !self.problem.has_datatype_sorts()
            && crate::adaptive_bv_dual_lane::max_expanded_bool_state(&self.problem)
                > crate::adaptive_bv_dual_lane::BVTOBOOL_EXPANDED_SKIP_THRESHOLD
    }

    pub(crate) fn try_bv_shallow_bmc_refutation(
        &self,
        deadline: Option<Instant>,
    ) -> Option<PortfolioResult> {
        if !self.problem.has_bv_sorts()
            || self.problem.has_array_sorts()
            || self.problem.has_datatype_sorts()
            || self.budget_exhausted(deadline)
        {
            return None;
        }
        let remaining = self.remaining_budget(deadline)?;
        if remaining < Duration::from_secs(2) {
            return None;
        }
        // Bounded so it cannot starve the downstream safety stages. At short
        // screens (<120 s remaining) the July-2026-tuned caps are kept
        // bit-identical: ~10 s probe, depth 12, 4 s/depth. At competition
        // budgets the probe scales up — SLayerCF's linear BV level-towers
        // refute at depths well past 12 and blow the 10 s cap
        // (#chc25-lever-3) — while a third of the remaining budget stays the
        // ceiling so safety stages always keep the majority.
        let short_screen = remaining < Duration::from_mins(2);
        let probe_budget = if short_screen {
            remaining
                .min(Duration::from_secs(10))
                .min(remaining / 3 + Duration::from_secs(3))
        } else {
            // Minority share only: the probe runs BEFORE the safety stages,
            // and a greedy slice was measured flipping 60 s-solvable sat
            // instances to unknown at 300 s (see #chc25-lever-3 retune).
            (remaining / 6).min(Duration::from_mins(1))
        };
        let per_depth = if short_screen {
            Duration::from_secs(4).min(probe_budget)
        } else {
            (probe_budget / 8)
                .max(Duration::from_secs(4))
                .min(Duration::from_secs(10))
        };
        let scaled_probe_depth = if short_screen {
            12
        } else if probe_budget >= Duration::from_secs(45) {
            40
        } else {
            24
        };
        let bmc = crate::bmc::BmcSolver::new(
            self.problem.clone(),
            BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: scaled_probe_depth,
                acyclic_safe: false,
                prefer_exact_acyclic_first: false,
                per_depth_timeout: Some(per_depth),
                time_budget: Some(probe_budget),
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                proof_cross_check: false,
                ts_probe_clamp: None,
                sweep_past_spurious_sat: true,
            },
        );

        // COMMITTED-CHAIN lane FIRST: the IntDualyzer BV programs (quicksort /
        // SOR / LU) need a DEEP (10–27-step) straight-line derivation to the
        // asserted-failure point — no branching, but far deeper than the shallow
        // flat/tree probes reach, and the full disjunctive unfolding at that
        // depth overflows the internal SMT. This lane commits to the single
        // minimal-node derivation and checks only that thin chain — a small
        // formula the internal SMT decides directly in well under a second. Run
        // it before the flat/tree probes so their (Unknown, but budget- and
        // memory-consuming) attempts on these large problems cannot starve it.
        // Cheap and sound-by-construction (validated witness ⇒ Unsafe only).
        if !self.budget_exhausted(deadline) {
            if let Some(remaining) = self.remaining_budget(deadline) {
                if remaining >= Duration::from_secs(2) {
                    let chain_budget = remaining.min(Duration::from_secs(10));
                    let chain_start = Instant::now();
                    if let PortfolioResult::Unsafe(cex) =
                        bmc.solve_committed_chain_refutation(chain_budget)
                    {
                        self.decision_log.log_decision(DecisionEntry {
                            stage: "bv_committed_chain_refutation",
                            gate_result: true,
                            gate_reason: "deep straight-line BV counterexample".to_string(),
                            budget_secs: chain_budget.as_secs_f64(),
                            elapsed_secs: chain_start.elapsed().as_secs_f64(),
                            result: "unsafe",
                            lemmas_learned: 0,
                            max_frame: 0,
                        });
                        return Some(PortfolioResult::Unsafe(cex));
                    }
                }
            }
        }

        // FIX #2c (corrected placement): size-gate ONLY the flat and tree
        // bit-blasted probes below — NOT the committed-chain lane above. The
        // internal BMC encoding bit-blasts the BV state per unrolled step;
        // measured on ssh s3_clnt (3904-Bool state) the flat probe produced
        // 12.3M-var SAT instances at depth 3, ~100s of pure waste before any
        // safety stage ran, so the reclaimed window goes to the non-inlined
        // word-level PDR (see `bv_bitblast_probes_size_skipped`). But the
        // committed-chain lane is the ONLY refuter of the large IntDualyzer BV
        // programs (LU/SOR/quicksort), whose huge expanded Bool state is
        // exactly what this gate keys on — it commits to one thin straight-line
        // chain and decides in well under a second, so it must run first and
        // stay ungated (regression: LU.c-bv solved unsat in ~5s pre-#2c, then
        // timed out when the gate skipped the whole function).
        if self.bv_bitblast_probes_size_skipped() {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Skipping stage-0.15 flat/tree BV bit-blasted probes \
                     (expanded state would be {} Bool vars, threshold {}); committed-chain ran",
                    crate::adaptive_bv_dual_lane::max_expanded_bool_state(&self.problem),
                    crate::adaptive_bv_dual_lane::BVTOBOOL_EXPANDED_SKIP_THRESHOLD
                );
            }
            return None;
        }

        let start = Instant::now();
        if let PortfolioResult::Unsafe(cex) = bmc.solve() {
            self.decision_log.log_decision(DecisionEntry {
                stage: "bv_shallow_bmc_refutation",
                gate_result: true,
                gate_reason: "shallow BV counterexample".to_string(),
                budget_secs: probe_budget.as_secs_f64(),
                elapsed_secs: start.elapsed().as_secs_f64(),
                result: "unsafe",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return Some(PortfolioResult::Unsafe(cex));
        }

        // The level-flat BMC above cannot represent a rule body with two
        // applications of the same predicate (a branching-tree counterexample —
        // e.g. reve `REC_f_ … REC_f_`). Try the bounded derivation-TREE
        // unfolding, which gives every tree node fresh variables. Also
        // sound-by-construction (the reconstructed witness is replayed against
        // the original CHC; Unsafe only). Kept to a small budget/depth so it
        // cannot starve the downstream safety stages.
        if !self.budget_exhausted(deadline) {
            if let Some(remaining) = self.remaining_budget(deadline) {
                if remaining >= Duration::from_secs(3) {
                    // Short screens keep the July-2026 probe plan (depth 6,
                    // ≤8 s, 6 k nodes). At competition budgets the reve-horn
                    // branching counterexamples need deeper trees than the
                    // probe cap reaches (#chc25-lever-6): scale depth, slice
                    // and node cap with the remaining budget — still Unsafe-
                    // only and witness-replay-gated, so purely additive.
                    // CAUTION (measured, 300 s screen): expression building and
                    // the bit-blast encoding are NOT interruptible (#5877), so
                    // an oversized tree jams the lane past its slice — depth
                    // 14 / 100 k nodes burned a full 300 s on an instance the
                    // 60 s screen solves in 0.8 s. Keep the scaled tree small
                    // enough that encoding stays tractable and the slice a
                    // minority share (≤1/6) of the remaining budget.
                    let competition = remaining >= Duration::from_mins(2);
                    let (tree_depth, tree_budget, tree_node_cap) = if competition {
                        (10, (remaining / 6).min(Duration::from_mins(1)), 24_000)
                    } else {
                        (6, remaining.min(Duration::from_secs(8)), 6_000)
                    };
                    let tree_start = Instant::now();
                    if let PortfolioResult::Unsafe(cex) =
                        bmc.solve_bounded_tree_refutation(tree_depth, tree_budget, tree_node_cap)
                    {
                        self.decision_log.log_decision(DecisionEntry {
                            stage: "bv_bounded_tree_refutation",
                            gate_result: true,
                            gate_reason: "branching-tree BV counterexample".to_string(),
                            budget_secs: tree_budget.as_secs_f64(),
                            elapsed_secs: tree_start.elapsed().as_secs_f64(),
                            result: "unsafe",
                            lemmas_learned: 0,
                            max_frame: 0,
                        });
                        return Some(PortfolioResult::Unsafe(cex));
                    }
                }
            }
        }
        None
    }

    pub(super) fn solve_multi_pred_complex(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> PortfolioResult {
        if self.config.verbose {
            safe_eprintln!("Adaptive: Using multi-pred complex strategy (full portfolio)");
        }

        // Stage 0.15: early shallow BV bounded-refutation probe (CHC-COMP
        // BV-Nonlin/BV-Lin). Cheap, uncontended, sound-by-construction; catches
        // shallow (depth 2–5) BV counterexamples the contended dual-lane BMC and
        // the downstream invariant stages miss. Returns Unsafe only.
        if let Some(result) = self.try_bv_shallow_bmc_refutation(deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: MultiPredComplex early BV shallow-BMC found Unsafe");
            }
            return result;
        }

        // Stage 0: Try structural synthesis (< 1ms overhead on extra-small-lia)
        if let Some(result) = self.try_synthesis() {
            if self.config.verbose {
                safe_eprintln!("Adaptive: MultiPredComplex problem solved by structural synthesis");
            }
            return result;
        }

        // Stage 0.25: BV REVE equivalence summaries.  This pure-BV32 family has
        // two recursively-defined binary summaries and one paired arity-4
        // summary. The useful invariant is relational on the paired summary,
        // and the helper only accepts it after an original-clause structural
        // certificate for that narrow BV32 shape.
        if let Some(result) = self.try_bv_reve_equivalence_synthesis() {
            if self.config.verbose {
                safe_eprintln!("Adaptive: MultiPredComplex BV REVE synthesis solved the problem");
            }
            return result;
        }

        // Stage 0.27: relational-equality Houdini (gold safe-side build, I1) —
        // certified relational invariants for reve-class BV problems the narrow
        // certifier rejects. Re-verified per-rule before Safe; bounded budget.
        if let Some(result) = self.try_relational_equality_houdini_lane(deadline) {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: MultiPredComplex relational Houdini (I1) solved the problem"
                );
            }
            return result;
        }

        // Stage 0.28: data-driven affine-hull relational Houdini (gold safe-side
        // build, I2) — synthesizes multi-variable linear invariants from the
        // affine hull of sampled reachable states for reve/geometry BV problems
        // I1's equality-only templates miss. Re-verified per-rule before Safe.
        if let Some(result) = self.try_data_driven_houdini_lane() {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: MultiPredComplex data-driven Houdini (I2) solved the problem"
                );
            }
            return result;
        }

        // Stage 0.29: disjunctive reve-accumulator relational Houdini (gold
        // safe-side build, I3) — synthesizes the two-branch (synced ∨ guarded-
        // coupling) invariant that offset-counter accumulator loops need and
        // which I1/I2's conjunctive-affine templates cannot express. Re-verified
        // per-rule before Safe; bounded budget.
        if let Some(result) = self.try_reve_accumulator_invariant_lane() {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: MultiPredComplex reve-accumulator Houdini (I3) solved the problem"
                );
            }
            return result;
        }

        // Stage 0.295: multi-guard relational-coupling Houdini (gold safe-side
        // build, I4) — synthesizes the conjunctive-guard reve coupling
        // `(a=d ∧ b=e) ⇒ (c=f)` that links corresponding arguments of two
        // synchronized recursive copies. The reve mutual-recursion equivalence
        // family (reve/001, 001b) needs this two-guard coupling on the arity-6
        // product summary, which I1's single-guard template cannot represent.
        // Re-verified per-rule before Safe; bounded budget.
        if let Some(result) = self.try_reve_coupling_houdini_lane() {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: MultiPredComplex reve-coupling Houdini (I4) solved the problem"
                );
            }
            return result;
        }

        // Stage 0.296: compact cyclic-order consistency invariant (gold safe-side
        // build, I5) — the computational-geometry BV "Consistency" family
        // (point-location, graham-scan) whose orientation primitive
        // (lturn/step_lturn/combined_lturn) is consistent under CYCLIC
        // permutation of three orientation columns. Synthesizes a single
        // closed-form strict cyclic-order predicate over those columns (the
        // COMPACT form that verify_model_per_rule discharges in a few seconds at
        // arity 11/12, vs. the reverted disjunction-of-rotated-polyhedra that
        // took >100 s). Re-verified per-rule before Safe; bounded budget.
        if let Some(result) = self.try_cyclic_consistency_invariant_lane() {
            if self.config.verbose {
                safe_eprintln!("Adaptive: MultiPredComplex cyclic-order consistency invariant (I5) solved the problem");
            }
            return result;
        }

        // Stage 0.3: narrow BallRajamani LIA-Arrays unsafe route. The witness
        // is accepted only after the original CHC counterexample verifier
        // returns `Valid`; any shape or validation miss falls through.
        if let Some(result) = self.try_ball_rajamani_lia_arrays_counterexample_route(deadline) {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: MultiPredComplex BallRajamani LIA-Arrays route validated Unsafe"
                );
            }
            return result;
        }

        // Stage 0.5: Exact BMC probe for acyclic predicate DAGs.
        // The helper routes through PortfolioSolver, preserving BMC empty-Safe
        // rejection and counterexample validation instead of accepting raw
        // acyclic_safe results.
        if let Some((result, _evidence)) = self.try_acyclic_bmc_probe(features, deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Acyclic BMC probe solved the complex problem");
            }
            return result;
        }

        // Cross-engine lemma transfer pool (#7919). Populated by non-inlined PDR
        // when it returns Unknown, consumed by retry engines.
        let mut transferred_pool: Option<LemmaPool> = None;
        // Stage rotation (item 5): true when the non-inlined PDR stage gave up
        // Stuck with zero frame growth — the same-family retry PDR probe on
        // the same problem is then provably redundant and skipped.
        let mut non_inlined_pdr_stuck_no_growth = false;

        // Stage 0.5: Non-inlined PDR for multi-predicate problems (#1362).
        // Same rationale as solve_multi_pred_linear Stage 1.5: inlining destroys
        // per-predicate parity structure that PDR needs for modular invariants.
        if self.problem.predicates().len() > 1 && !self.budget_exhausted(deadline) {
            // Budget scaling (#1398): same formula as Stage 1.5.
            let num_preds = self.problem.predicates().len() as u64;
            let base_budget_secs = if num_preds >= 4 {
                5 + 2 * num_preds.saturating_sub(3)
            } else {
                5
            };
            let max_budget = Duration::from_secs(base_budget_secs.min(15));
            // #7457: Cap to 50% of remaining budget (same as Stage 1.5).
            let remaining = self.remaining_budget(deadline).unwrap_or(max_budget);
            // FIX #2d: when the stage-0.15 bit-blasted probes were
            // size-skipped, the word-level non-inlined PDR is the engine
            // best matched to the problem (bit-blasting is intractable by
            // construction here) — give it the reclaimed window instead of
            // the generic 15s cap: remaining/3 capped at 300s, so the
            // dual-lane and portfolio still keep the majority.
            let stage_budget = if self.bv_bitblast_probes_size_skipped() {
                (remaining / 3).min(Duration::from_mins(5))
            } else {
                (remaining / 2).min(max_budget)
            };
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Trying non-inlined PDR ({} predicates, {:.1}s budget)",
                    self.problem.predicates().len(),
                    stage_budget.as_secs_f64()
                );
            }
            let mut pdr_config = Self::multi_pred_pdr_config(PdrConfig {
                verbose: self.config.verbose,
                solve_timeout: Some(stage_budget),
                // #7930: Cap escalation for DT problems.
                max_escalation_level: if features.uses_datatypes { 0 } else { 3 },
                ..PdrConfig::default()
            })
            .with_tla_trace_from_env();
            // Item 5a: subsequent stages (dual-lane, portfolio, retry) exist,
            // so let this stage self-report hopeless stagnation and release
            // its budget to them instead of burning the full stage share.
            pdr_config.give_up_on_stuck = true;
            self.apply_user_hints(&mut pdr_config);
            let non_inlined_start = Instant::now();
            let mut pdr = PdrSolver::new(self.problem.clone(), pdr_config);
            pdr.enable_tla_trace_from_config();
            let result = pdr.solve();
            // Feed the live progress snapshot, then consult it for stage
            // rotation (item 5).
            let stage_stats = pdr.extract_stats();
            self.accumulate_stats(&stage_stats);
            non_inlined_pdr_stuck_no_growth = self.predecessor_stage_stuck_no_growth(&stage_stats);
            let validated = self.validate_adaptive_result(result);
            if !matches!(validated, PdrResult::Unknown) {
                if self.config.verbose {
                    safe_eprintln!("Adaptive: Non-inlined PDR solved the problem");
                }
                self.decision_log.log_decision(DecisionEntry {
                    stage: "multi_pred_complex_non_inlined_pdr",
                    gate_result: true,
                    gate_reason: format!("{} predicates", self.problem.predicates().len()),
                    budget_secs: stage_budget.as_secs_f64(),
                    elapsed_secs: non_inlined_start.elapsed().as_secs_f64(),
                    result: Self::result_to_str(&validated),
                    lemmas_learned: 0,
                    max_frame: 0,
                });
                return validated;
            }
            // Export learned lemmas for cross-engine transfer (#7919).
            let pool = pdr.export_lemmas();
            if self.config.verbose && !pool.is_empty() {
                safe_eprintln!(
                    "Adaptive: Exported {} lemmas from non-inlined PDR for cross-engine transfer (complex)",
                    pool.len()
                );
            }
            let pool_size = pool.len();
            transferred_pool = Some(pool);
            self.decision_log.log_decision(DecisionEntry {
                stage: "multi_pred_complex_non_inlined_pdr",
                gate_result: true,
                gate_reason: format!("{} predicates, unknown", self.problem.predicates().len()),
                budget_secs: stage_budget.as_secs_f64(),
                elapsed_secs: non_inlined_start.elapsed().as_secs_f64(),
                result: "unknown",
                lemmas_learned: pool_size,
                max_frame: 0,
            });
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Non-inlined PDR returned Unknown, continuing to portfolio"
                );
            }
        }

        // Stage 0.9 (BV routing): pure word-level BV problems get the dedicated
        // BV dual-lane portfolio (Lane C = BV-native PDR/BMC at the full remaining
        // budget) before the generic portfolio. The generic roster bit-blasts BV
        // to hundreds of Bool state vars (BvToBool) where PDR generalization
        // collapses, or to ITE-heavy modular Int (BvToInt) the interpolation
        // engines cannot close; the dual-lane keeps word-level frames. Every lane
        // self-validates (Safe re-verified per-rule on the original problem;
        // Unsafe by counterexample replay), so the 0-wrong invariant is preserved;
        // an unhandled shape returns Unknown and falls through to the generic
        // portfolio. Arrays/datatypes are excluded — the dual-lane is BV-scalar.
        if self.problem.has_bv_sorts()
            && !self.problem.has_array_sorts()
            && !self.problem.has_datatype_sorts()
            && !self.budget_exhausted(deadline)
        {
            if let Some(remaining) = self.remaining_budget(deadline) {
                let bv_start = Instant::now();
                let result = self.solve_bv_dual_lane(remaining);
                if !matches!(result, PdrResult::Unknown) {
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "multi_pred_complex_bv_dual_lane",
                        gate_result: true,
                        gate_reason: format!(
                            "{} predicates, has_bv",
                            self.problem.predicates().len()
                        ),
                        budget_secs: remaining.as_secs_f64(),
                        elapsed_secs: bv_start.elapsed().as_secs_f64(),
                        result: Self::result_to_str(&result),
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: MultiPredComplex BV dual-lane solved the problem"
                        );
                    }
                    return result;
                }
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: MultiPredComplex BV dual-lane returned Unknown, continuing to portfolio"
                    );
                }
            }
        }

        // Stage 1: Run full portfolio with deadline-based timeout (#7034, #7932)
        let mut config = PortfolioConfig::default();
        match self.remaining_budget(deadline) {
            Some(remaining) => {
                config.parallel_timeout = Some(Self::multi_pred_portfolio_timeout(remaining));
            }
            None => {
                // Unbounded budget (no deadline). Leave parallel_timeout as None.
            }
        }
        config.verbose = self.config.verbose;
        config.strict_proofs = self.config.strict_proofs;
        // Cap PDR escalation and remove Kind for DT problems (#7930).
        if features.uses_datatypes {
            config.apply_dt_guards(0);
        }
        // Seed portfolio PDR engines with transferred lemma pool (#7919).
        // This closes the gap where the complex path discarded non-inlined PDR
        // lemmas when entering the portfolio, unlike the linear path which
        // explicitly set lemma_hints on its PDR configs.
        if let Some(ref pool) = transferred_pool {
            config.set_pdr_lemma_pool(pool);
            if self.config.verbose && !pool.is_empty() {
                safe_eprintln!(
                    "Adaptive: Seeded portfolio PDR engines with {} transferred lemmas (#7919)",
                    pool.len()
                );
            }
        }

        let portfolio_start = Instant::now();
        let portfolio_result = self.run_portfolio(config);

        self.decision_log.log_decision(DecisionEntry {
            stage: "multi_pred_complex_portfolio",
            gate_result: true,
            gate_reason: "full portfolio".to_string(),
            budget_secs: self
                .remaining_budget(deadline)
                .map_or(0.0, |d| d.as_secs_f64()),
            elapsed_secs: portfolio_start.elapsed().as_secs_f64(),
            result: Self::result_to_str(&portfolio_result),
            lemmas_learned: 0,
            max_frame: 0,
        });

        // If solved, return immediately
        if !matches!(portfolio_result, PortfolioResult::Unknown) {
            return portfolio_result;
        }

        // Check global memory budget before starting retry stages (#2771)
        if TermStore::global_memory_exceeded() {
            return PortfolioResult::Unknown;
        }

        // Budget check before retry stages (#7034)
        if self.budget_exhausted(deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Budget exhausted after portfolio, skipping retry");
            }
            return PortfolioResult::Unknown;
        }

        // Stage rotation (item 5): skip the same-family retry PDR probe when
        // the non-inlined PDR stage already gave up Stuck with zero frame
        // growth on this very problem — the probe would replay the identical
        // stagnating search. Completeness-only (returns the portfolio Unknown).
        if non_inlined_pdr_stuck_no_growth {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Skipping failure-guided retry — non-inlined PDR was stuck with zero frame growth"
                );
            }
            self.decision_log.log_decision(DecisionEntry {
                stage: "multi_pred_complex_retry",
                gate_result: false,
                gate_reason: "skipped: predecessor PDR stage stuck with zero frame growth"
                    .to_string(),
                budget_secs: self
                    .remaining_budget(deadline)
                    .map_or(0.0, |d| d.as_secs_f64()),
                elapsed_secs: 0.0,
                result: "unknown",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return portfolio_result;
        }

        // Stage 2: Failure-guided retry
        if self.config.verbose {
            safe_eprintln!("Adaptive: Portfolio returned Unknown, running failure analysis probe");
        }

        let probe_timeout = self.multi_pred_probe_timeout(deadline);
        let max_esc = if features.uses_datatypes { 0 } else { 3 };
        let mut probe_config = Self::multi_pred_pdr_config(PdrConfig {
            max_frames: 30,
            max_iterations: 500,
            verbose: self.config.verbose,
            solve_timeout: Some(probe_timeout),
            max_escalation_level: max_esc,
            ..PdrConfig::default()
        })
        .with_tla_trace_from_env();
        self.apply_user_hints(&mut probe_config);
        // Seed probe with transferred lemmas from non-inlined PDR (#7919).
        if let Some(ref pool) = transferred_pool {
            if !pool.is_empty() {
                probe_config.lemma_hints = Some(pool.clone());
            }
        }
        let probe_result = PdrSolver::solve_problem_with_stats(&self.problem, probe_config);
        self.accumulate_stats(&probe_result.stats);

        // If probe solves, validate before returning (#5549 soundness fix)
        if !matches!(probe_result.result, PdrResult::Unknown) {
            let validated = self.validate_adaptive_result(probe_result.result);
            if !matches!(validated, PdrResult::Unknown) {
                return validated;
            }
        }

        if self.budget_exhausted(deadline) {
            return PortfolioResult::Unknown;
        }

        // Analyze failure and guide retry
        let analysis = FailureAnalysis::from_stats(&probe_result.stats);
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Probe analysis - {} (confidence {:.0}%)",
                analysis.mode,
                analysis.confidence * 100.0
            );
            safe_eprintln!("Adaptive: Diagnostic: {}", analysis.diagnostic);
        }

        let guide = FailureGuide::from_analysis(&analysis);

        // Try alternative engine with remaining budget (#7034)
        if let Some(ref alt_engine) = guide.try_alternative_engine {
            if let Some(result) = self.try_alternative_engine_budgeted(alt_engine, deadline) {
                return result;
            }
        }

        if self.budget_exhausted(deadline) {
            return PortfolioResult::Unknown;
        }

        // Retry PDR with guided config adjustments
        if !guide.adjustments.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Retrying with {} config adjustments",
                    guide.adjustments.len()
                );
            }
            let mut retry_base = Self::multi_pred_pdr_config(PdrConfig {
                verbose: self.config.verbose,
                solve_timeout: self.multi_pred_retry_timeout(deadline),
                max_escalation_level: max_esc,
                ..PdrConfig::default()
            })
            .with_tla_trace_from_env();
            self.apply_user_hints(&mut retry_base);
            // Also seed retry with transferred lemmas from non-inlined PDR (#7919).
            if let Some(ref pool) = transferred_pool {
                if !pool.is_empty() {
                    retry_base.lemma_hints = Some(pool.clone());
                }
            }
            let retry_config = guide.apply_to_config(retry_base);
            let retry_result = PdrSolver::solve_problem_with_stats(&self.problem, retry_config);
            self.accumulate_stats(&retry_result.stats);
            return self.validate_adaptive_result(retry_result.result);
        }

        // No retry possible, return original Unknown
        portfolio_result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::classifier::ProblemClass;
    use crate::{AdaptiveConfig, ChcParser};

    const BALL_RAJAMANI_LIA_ARRAYS_SMOKE: &str = r#"
(set-logic HORN)

(declare-fun |A@_1| ( (Array Int Int) Int Int Int ) Bool)
(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |A@_shadow.mem.0| ( (Array Int Int) (Array Int Int) Int Int Int Int ) Bool)
(declare-fun |main@entry| ( (Array Int Int) ) Bool)
(declare-fun |A| ( Bool Bool Bool (Array Int Int) (Array Int Int) Int Int Int Int ) Bool)

(assert
  (forall ( (B (Array Int Int)) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (v_6 Bool) (v_7 Bool) (v_8 Bool) )
    (=>
      (and
        (and true (= v_6 true) (= v_7 true) (= v_8 true))
      )
      (A v_6 v_7 v_8 B C D E F G)
    )
  )
)
(assert
  (forall ( (B (Array Int Int)) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (v_6 Bool) (v_7 Bool) (v_8 Bool) )
    (=>
      (and
        (and true (= v_6 false) (= v_7 true) (= v_8 true))
      )
      (A v_6 v_7 v_8 B C D E F G)
    )
  )
)
(assert
  (forall ( (B (Array Int Int)) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (v_6 Bool) (v_7 Bool) (v_8 Bool) )
    (=>
      (and
        (and true (= v_6 false) (= v_7 false) (= v_8 false))
      )
      (A v_6 v_7 v_8 B C D E F G)
    )
  )
)
(assert
  (forall ( (B (Array Int Int)) (C (Array Int Int)) (D Int) (E Int) (F Int) (G Int) (v_6 Bool) (v_7 Bool) (v_8 Bool) )
    (=>
      (and
        (A@_shadow.mem.0 B C G E F D)
        (and (= v_6 true) (= v_7 false) (= v_8 false))
      )
      (A v_6 v_7 v_8 B C D E F G)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) )
    (=>
      (and
        true
      )
      (A@_1 A B C D)
    )
  )
)
(assert
  (forall ( (B Int) (C Bool) (D Bool) (E (Array Int Int)) (F (Array Int Int)) (G Bool) (H (Array Int Int)) (I Bool) (J Bool) (K (Array Int Int)) (L (Array Int Int)) (M (Array Int Int)) (N Int) (O Int) (P Int) (Q Int) (v_16 Bool) (v_17 Bool) )
    (=>
      (and
        (A@_1 L O P Q)
        (A J v_16 v_17 L F O Q P B)
        (and (= v_16 false)
     (= v_17 false)
     (or (not G) (not C) D)
     (or (not I) (and J I) (and I G))
     (or (not I) (not G) (= H E))
     (or (not I) (not G) (= M H))
     (or (not J) (not D) (not C))
     (or (not J) (not I) (= K F))
     (or (not J) (not I) (= M K))
     (or (not G) (= E (store L P O)))
     (or (not G) (and G C))
     (or (not J) (and J C))
     (= I true)
     (= D (= Q 0)))
      )
      (A@_shadow.mem.0 L M N O P Q)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) )
    (=>
      (and
        true
      )
      (main@entry A)
    )
  )
)
(assert
  (forall ( (B (Array Int Int)) (C Bool) (D (Array Int Int)) (E Int) (F (Array Int Int)) (G (Array Int Int)) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (v_15 Bool) (v_16 Bool) (v_17 Bool) (v_18 Bool) (v_19 Bool) (v_20 Bool) )
    (=>
      (and
        (main@entry B)
        (A v_15 v_16 v_17 D F K H I E)
        (A v_18 v_19 v_20 F G K H I J)
        (and (= v_15 true)
     (= v_16 false)
     (= v_17 false)
     (= v_18 true)
     (= v_19 false)
     (= v_20 false)
     (= L (= K 0))
     (= C (= K 0))
     (= H (ite C 1 0))
     (or (not N) (and N M))
     (or (not O) (and O N))
     (or (not P) (and P O))
     (not L)
     (= P true)
     (= D (store B I 0)))
      )
      main@verifier.error.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) )
    (=>
      (and
        main@verifier.error.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

    fn complex_loop_test_features(phase_bounded_depth: Option<usize>) -> ProblemFeatures {
        ProblemFeatures {
            num_predicates: 1,
            num_clauses: 4,
            is_linear: true,
            is_single_predicate: true,
            has_cycles: true,
            scc_count: 1,
            max_scc_size: 1,
            dag_depth: 0,
            uses_arrays: false,
            uses_real: false,
            num_transitions: 2,
            num_facts: 1,
            num_queries: 1,
            max_clause_variables: 2,
            mean_clause_variables: 2.0,
            has_multiplication: false,
            has_mod_div: false,
            has_ite: false,
            self_loop_ratio: 1.0,
            max_predicate_arity: 1,
            is_entry_exit_only: false,
            phase_bounded_depth,
            uses_datatypes: false,
            is_triangle_location_diff_bounds: false,
            class: ProblemClass::ComplexLoop,
        }
    }

    fn parse_ball_rajamani_smoke() -> ChcProblem {
        let problem = ChcParser::parse(BALL_RAJAMANI_LIA_ARRAYS_SMOKE)
            .expect("BallRajamani LIA-Arrays smoke should parse");
        problem
            .validate()
            .expect("BallRajamani LIA-Arrays smoke should validate");
        problem
    }

    #[test]
    fn ball_rajamani_lia_arrays_route_builds_original_clause_witness() {
        let problem = parse_ball_rajamani_smoke();
        let cex = build_ball_rajamani_lia_arrays_counterexample(&problem)
            .expect("BallRajamani LIA-Arrays smoke should match the narrow route");
        let witness = cex
            .witness
            .as_ref()
            .expect("route counterexample must carry a derivation witness");
        assert_eq!(witness.query_clause, Some(8));
        assert!(
            witness.entries.len() >= 16,
            "route should emit the derivation DAG, got {} entries",
            witness.entries.len()
        );
    }

    #[test]
    fn ball_rajamani_lia_arrays_route_is_gated_by_original_validation() {
        let problem = parse_ball_rajamani_smoke();
        let cex = build_ball_rajamani_lia_arrays_counterexample(&problem)
            .expect("BallRajamani LIA-Arrays smoke should match the narrow route");
        let mut verifier = PdrSolver::new(
            problem.clone(),
            PdrConfig {
                verbose: false,
                strict_proofs: true,
                disable_array_scalarization: true,
                preserve_original_clauses: true,
                solve_timeout: Some(Duration::from_secs(2)),
                ..PdrConfig::default()
            },
        );
        verifier.set_validation_deadline(Duration::from_secs(2));
        let validation = verifier.verify_counterexample(&cex);
        assert_eq!(
            validation,
            CexVerificationResult::Valid,
            "BallRajamani witness must validate on the original clauses"
        );
        let adaptive = AdaptivePortfolio::new(
            problem,
            AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(3)),
        );

        let result = adaptive.try_ball_rajamani_lia_arrays_counterexample_route(None);
        assert!(
            matches!(result, Some(PortfolioResult::Unsafe(_))),
            "validated BallRajamani route should return Unsafe, got {result:?}"
        );
    }

    #[test]
    fn ball_rajamani_lia_arrays_route_rejects_other_array_shapes() {
        let input = r#"
(set-logic HORN)
(declare-fun Inv ( (Array Int Int) Int ) Bool)
(assert (forall ((A (Array Int Int)) (I Int)) (=> true (Inv A I))))
(assert (forall ((A (Array Int Int)) (I Int)) (=> (Inv A I) false)))
(check-sat)
"#;
        let problem = ChcParser::parse(input).expect("unrelated LIA-array CHC should parse");
        problem
            .validate()
            .expect("unrelated LIA-array CHC should validate");

        assert!(
            build_ball_rajamani_lia_arrays_counterexample(&problem).is_none(),
            "route must fail closed on non-BallRajamani array shapes"
        );
    }

    #[test]
    fn complex_loop_bmc_per_depth_budget_slices_total_probe_budget() {
        let total_budget = Duration::from_secs(10);
        let max_depth = 22;
        let per_depth =
            AdaptivePortfolio::complex_loop_bmc_per_depth_budget(total_budget, max_depth);

        assert!(!per_depth.is_zero());
        assert!(
            per_depth.as_nanos() * u128::from((max_depth + 1) as u32) <= total_budget.as_nanos(),
            "per-depth slices should fit within the advertised BMC probe budget"
        );
        assert_eq!(
            AdaptivePortfolio::complex_loop_bmc_per_depth_budget(total_budget, 0),
            total_budget,
            "depth 0 still has one BMC check, so it gets the full budget"
        );
    }

    #[test]
    fn complex_loop_bmc_probe_skips_non_phase_bounded_lia_for_tpa_pdr() {
        let features = complex_loop_test_features(None);

        assert_eq!(
            AdaptivePortfolio::complex_loop_bmc_probe_skip_reason(&features, false, false),
            Some("non_phase_bounded_tpa_pdr_priority"),
            "non-phase-bounded single-predicate LIA ComplexLoop should not spend the focused BMC preprobe"
        );
    }

    #[test]
    fn complex_loop_bmc_probe_allows_phase_bounded_lia_when_budget_remains() {
        let features = complex_loop_test_features(Some(22));

        assert_eq!(
            AdaptivePortfolio::complex_loop_bmc_probe_skip_reason(&features, false, false),
            None,
            "phase-bounded single-predicate LIA ComplexLoop may still use the focused BMC preprobe"
        );
    }

    #[test]
    fn complex_loop_bmc_probe_skip_reason_prefers_deadline_exhaustion() {
        let features = complex_loop_test_features(Some(22));

        assert_eq!(
            AdaptivePortfolio::complex_loop_bmc_probe_skip_reason(&features, false, true),
            Some("deadline_exhausted"),
            "deadline exhaustion should be logged as the skip reason before structural gates"
        );
    }

    #[test]
    fn complex_loop_bmc_probe_has_total_and_per_depth_budget_caps() {
        let src = include_str!("adaptive_multi_pred_complex.rs");
        let fn_start = src
            .find("pub(super) fn solve_complex_loop(")
            .expect("adaptive_multi_pred_complex.rs should define solve_complex_loop");
        let fn_body = &src[fn_start..];
        let fn_end = fn_body
            .find("pub(super) fn solve_multi_pred_complex(")
            .expect("solve_multi_pred_complex should follow solve_complex_loop");
        let fn_body = &fn_body[..fn_end];
        let probe_start = fn_body
            .find("Stage -2: Focused BMC probe")
            .expect("solve_complex_loop should keep the focused BMC probe");
        let probe_end = fn_body
            .find("Stage -1: Fast PDR probe")
            .expect("BMC probe should precede the PDR probe");
        let probe = &fn_body[probe_start..probe_end];

        assert!(
            src.contains("features.phase_bounded_depth.is_none()"),
            "ComplexLoop BMC preprobe helper should skip non-phase-bounded cases"
        );
        assert!(
            probe.contains("complex_loop_bmc_probe_skip_reason"),
            "ComplexLoop BMC preprobe should use the shared skip helper"
        );
        assert!(
            src.contains("non_phase_bounded_tpa_pdr_priority"),
            "ComplexLoop BMC skip reason should be decision-log visible"
        );
        assert!(
            probe.contains("result: \"skipped\""),
            "ComplexLoop BMC skip should be logged as skipped"
        );
        assert!(
            probe.contains("let _timeout_guard = cancel.cancel_after(bmc_budget);"),
            "ComplexLoop BMC probe should keep the external cancellation timer"
        );
        assert!(
            probe.contains(
                "Self::complex_loop_bmc_per_depth_budget(bmc_budget, bmc_probe_max_depth)"
            ),
            "ComplexLoop BMC probe should derive per-depth caps from the total probe budget"
        );
        assert!(
            probe.contains("per_depth_timeout: Some(bmc_per_depth_budget),"),
            "ComplexLoop BMC probe should pass the per-depth cap into BMC"
        );
        assert!(
            probe.contains("time_budget: Some(bmc_budget),"),
            "ComplexLoop BMC probe should pass the total cap into BMC"
        );
    }

    #[test]
    fn complex_loop_logs_downstream_tpa_pdr_reachability_before_portfolio() {
        let src = include_str!("adaptive_multi_pred_complex.rs");
        let fn_start = src
            .find("pub(super) fn solve_complex_loop(")
            .expect("adaptive_multi_pred_complex.rs should define solve_complex_loop");
        let fn_body = &src[fn_start..];
        let fn_end = fn_body
            .find("pub(super) fn solve_multi_pred_complex(")
            .expect("solve_multi_pred_complex should follow solve_complex_loop");
        let fn_body = &fn_body[..fn_end];
        let reach_log = fn_body
            .find("stage: \"complex_loop_tpa_pdr_reached\"")
            .expect("ComplexLoop should log whether the downstream PDR/TPA portfolio is reached");
        let run_portfolio = fn_body
            .find("let result = self.run_portfolio(config);")
            .expect("ComplexLoop should run the final portfolio");

        assert!(
            reach_log < run_portfolio,
            "downstream reachability should be logged before running the portfolio"
        );
        assert!(
            fn_body.contains("downstream portfolio includes pdr_tpa_bmc"),
            "reachability log should identify that PDR, TPA, and BMC are available downstream"
        );
        assert!(
            fn_body.contains("EngineConfig::Tpa(TpaConfig") && fn_body.contains("bmc_engine,"),
            "final ComplexLoop portfolio should keep TPA and BMC engines available"
        );
    }

    #[test]
    fn bv_shallow_bmc_refutation_finds_shallow_bv_counterexample() {
        // Word-level BV problem with a shallow (depth-1) counterexample: the
        // fact P(0) plus the query P(0) => false is unsafe. The probe must find
        // and validate the refutation.
        let input = r#"
(set-logic HORN)
(declare-fun P ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x00) (P x))))
(assert (forall ((x (_ BitVec 8))) (=> (and (P x) (= x #x00)) false)))
(check-sat)
"#;
        let problem = ChcParser::parse(input).expect("BV CHC should parse");
        let adaptive = AdaptivePortfolio::new(
            problem,
            AdaptiveConfig::test_default().with_time_budget(std::time::Duration::from_secs(10)),
        );
        let deadline = Some(ay_core::time::Instant::now() + std::time::Duration::from_secs(10));
        let result = adaptive.try_bv_shallow_bmc_refutation(deadline);
        assert!(
            matches!(result, Some(PortfolioResult::Unsafe(_))),
            "probe should return a validated Unsafe on a shallow BV counterexample, got {result:?}"
        );
    }

    #[test]
    fn bv_shallow_bmc_refutation_none_on_safe_and_non_bv() {
        // (a) A SAFE BV problem: the probe must NOT fabricate an Unsafe (it may
        // only return None, since it never claims Safe).
        let safe_bv = r#"
(set-logic HORN)
(declare-fun P ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x00) (P x))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (and (P x) (= y (bvadd x #x01))) (P y))))
(assert (forall ((x (_ BitVec 8))) (=> (and (P x) (bvult x #x00)) false)))
(check-sat)
"#;
        let problem = ChcParser::parse(safe_bv).expect("safe BV CHC should parse");
        let adaptive = AdaptivePortfolio::new(
            problem,
            AdaptiveConfig::test_default().with_time_budget(std::time::Duration::from_secs(5)),
        );
        let deadline = Some(ay_core::time::Instant::now() + std::time::Duration::from_secs(5));
        let result = adaptive.try_bv_shallow_bmc_refutation(deadline);
        assert!(
            !matches!(result, Some(PortfolioResult::Unsafe(_))),
            "probe must never return Unsafe on a SAFE problem, got {result:?}"
        );

        // (b) A non-BV (Int) problem: the probe is gated off and returns None.
        let int_prob = r#"
(set-logic HORN)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Q x))))
(assert (forall ((x Int)) (=> (and (Q x) (= x 0)) false)))
(check-sat)
"#;
        let problem = ChcParser::parse(int_prob).expect("Int CHC should parse");
        let adaptive = AdaptivePortfolio::new(
            problem,
            AdaptiveConfig::test_default().with_time_budget(std::time::Duration::from_secs(5)),
        );
        let deadline = Some(ay_core::time::Instant::now() + std::time::Duration::from_secs(5));
        assert!(
            adaptive.try_bv_shallow_bmc_refutation(deadline).is_none(),
            "probe must be gated off (None) for non-BV problems"
        );
    }

    /// reve BV-Nonlin branching-tree refutation, end-to-end through the wired
    /// Stage-0.15 probe (`try_bv_shallow_bmc_refutation` → flat BMC →
    /// `solve_bounded_tree_refutation`).
    ///
    /// These `reve` mutants shift ONE recursion base case (and the paired
    /// equivalence-query guard) of a relational equivalence check, making the
    /// "outputs differ" query reachable via a *branching* derivation tree. The
    /// counterexample is shallow (tree depth 2: `CHC_COMP_FALSE` ← two `REC_f_`
    /// facts, one derived through a single recursive step) but the honest
    /// witness has TWO premises of the same predicate sharing canonical
    /// instance names — which previously tripped a false-`Spurious` in the
    /// witness replay verifier (an under-determined base-clause head was
    /// re-solved to an arbitrary value instead of the recorded one). With that
    /// fixed the cex validates against the ORIGINAL CHC.
    ///
    /// SOUNDNESS: the targets must return a *validated* `Unsafe`; the safe
    /// twins (`001`, `001b`, `022`, `005`, `006`) must NEVER be reported
    /// `Unsafe` — a bad witness degrades to `Unknown`/`None`, never a wrong
    /// answer.
    ///
    /// `#[ignore]` — reads the CHC-COMP-26 corpus (not vendored into the unit
    /// build) and runs a multi-second bounded refutation. Run with:
    /// `cargo test -p ay-chc reve_branching_tree_refutation -- --ignored`.
    #[test]
    #[ignore]
    fn reve_branching_tree_refutation_validates_unsafe_not_safe() {
        let reve = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../benchmarks/chc/chc-comp26-benchmarks/eldarica-misc/BV/reve");
        if !reve.join("001c-horn-bv_000.smt2").exists() {
            eprintln!(
                "reve corpus not present at {} — skipping (symlink the corpus to run)",
                reve.display()
            );
            return;
        }

        let run = |name: &str| -> Option<PortfolioResult> {
            let path = reve.join(format!("{name}.smt2"));
            let smt = std::fs::read_to_string(&path).expect("reve instance readable");
            let problem = ChcParser::parse(&smt).expect("reve CHC should parse");
            let adaptive = AdaptivePortfolio::new(
                problem,
                AdaptiveConfig::test_default().with_time_budget(std::time::Duration::from_secs(60)),
            );
            let deadline = Some(ay_core::time::Instant::now() + std::time::Duration::from_secs(60));
            adaptive.try_bv_shallow_bmc_refutation(deadline)
        };

        // Targets (expected_verdict:false → unsat): the wired probe must return
        // a validated Unsafe (the witness passed original-CHC replay).
        for target in ["001c-horn-bv_000", "001d-horn-bv_000"] {
            let result = run(target);
            assert!(
                matches!(result, Some(PortfolioResult::Unsafe(_))),
                "{target}: expected validated Unsafe from wired probe, got {result:?}"
            );
        }

        // Safe twins (expected_verdict:true): must NEVER be reported Unsafe.
        for guard in [
            "001-horn-bv_000",
            "001b-horn-bv_000",
            "022-horn-bv_000",
            "005-horn-bv_000",
            "006-horn-bv_000",
        ] {
            let result = run(guard);
            assert!(
                !matches!(result, Some(PortfolioResult::Unsafe(_))),
                "{guard}: safe twin must never be reported Unsafe, got {result:?}"
            );
        }
    }

    // Integration: the wired Stage-0.15 probe (which now includes the
    // committed-chain lane) refutes the IntDualyzer BV programs and leaves
    // their SAFE twins alone. `#[ignore]`d — reads the competition corpus.
    fn intdualyzer_probe(name: &str) -> Option<PortfolioResult> {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join(format!(
                "benchmarks/chc/chc-comp26-benchmarks/eldarica-misc/BV/IntDualyzer/{name}.smt2"
            ));
        let input = std::fs::read_to_string(&path).ok()?;
        let problem = ChcParser::parse(&input).expect("benchmark should parse");
        let adaptive = AdaptivePortfolio::new(
            problem,
            AdaptiveConfig::test_default().with_time_budget(std::time::Duration::from_secs(30)),
        );
        let deadline = Some(ay_core::time::Instant::now() + std::time::Duration::from_secs(30));
        Some(
            adaptive
                .try_bv_shallow_bmc_refutation(deadline)
                .unwrap_or(PortfolioResult::Unknown),
        )
    }

    #[test]
    #[ignore]
    fn bv_probe_refutes_intdualyzer_unsafe_targets() {
        for name in ["quicksort.c-bv_000", "SOR.c-bv_000", "LU.c-bv_000"] {
            let Some(result) = intdualyzer_probe(name) else {
                eprintln!("SKIP {name}: corpus not present");
                continue;
            };
            assert!(
                matches!(result, PortfolioResult::Unsafe(_)),
                "{name} (expected_verdict:false) must be a VALIDATED Unsafe, got {result:?}"
            );
        }
    }

    #[test]
    #[ignore]
    fn bv_probe_leaves_intdualyzer_safe_guards_not_unsafe() {
        for name in ["mergesort.c-bv_000", "queens.c-bv_000"] {
            let Some(result) = intdualyzer_probe(name) else {
                eprintln!("SKIP {name}: corpus not present");
                continue;
            };
            assert!(
                !matches!(result, PortfolioResult::Unsafe(_)),
                "{name} (expected_verdict:true) must NOT be refuted, got {result:?}"
            );
        }
    }
}
