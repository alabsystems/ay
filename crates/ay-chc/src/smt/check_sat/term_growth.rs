// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term-growth mutation handlers for the DPLL(T) loop.
//!
//! When the theory solver requests a branch-and-bound split, disequality
//! split, or expression split, this module applies the mutations to the
//! CNF state (adding new Tseitin variables and clauses) and tracks
//! per-variable split counts to prevent infinite enumeration.

use std::collections::BTreeMap;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::term::Symbol;
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use super::super::context::SmtContext;
use super::super::types::{DiseqGuardKind, SmtResult};
use super::TermGrowthAction;

/// Baseline per-variable split cap (unbounded case).
const MAX_VAR_SPLITS: usize = 200;

/// Maximum model-equality encoding rounds per check (Phase 3 Fix 4).
///
/// Mirrors ay-dpll's `MODEL_EQ_MAX_ROUNDS_EAGER` (split_incremental/
/// model_equality.rs): a round is counted only when at least one NEW
/// equality pair is encoded, so repeated requests for known pairs cannot
/// burn the budget. Exceeding the cap fails closed to Unknown.
const MAX_MODEL_EQ_ROUNDS: usize = 20;

/// Split-tracking state threaded through the `'term_growth` loop.
///
/// Tracks per-variable disequality split counts and which disequality
/// terms have been "promoted" from single-value enumeration to
/// expression splits. Shared between the inner theory loop (which
/// increments `split_count`) and the outer term-growth handler.
pub(super) struct SplitState {
    pub(super) split_count: usize,
    pub(super) max_splits: usize,
    pub(super) var_diseq_splits: FxHashMap<TermId, usize>,
    pub(super) promoted_diseq_terms: FxHashSet<TermId>,
    /// Normalized (lhs, rhs) pairs already encoded as speculative model
    /// equalities (Phase 3 Fix 4). When a theory result requests only
    /// known pairs, the loop accepts the theory model instead of failing
    /// to Unknown (the final model is still re-verified before SAT is
    /// reported).
    pub(super) seen_model_eq_requests: FxHashSet<(TermId, TermId)>,
    /// Number of model-equality encoding rounds consumed (capped by
    /// `MAX_MODEL_EQ_ROUNDS`; counted only when a new pair is encoded).
    pub(super) model_eq_rounds: usize,
}

impl SplitState {
    pub(super) fn new() -> Self {
        Self {
            split_count: 0,
            // QF_LIA is decidable — the only termination risk is from unbounded
            // enumeration, which is already guarded by the per-variable split cap
            // (MAX_VAR_SPLITS = 200). The global cap is a safety valve, not a
            // correctness requirement. Use 1M uniformly to avoid spurious Unknown
            // on hard-but-finite queries from PDR internals (SCC inductiveness,
            // blocking, generalization) that call check_sat without timeout.
            // (#2472/#2475)
            max_splits: 1_000_000,
            var_diseq_splits: FxHashMap::default(),
            promoted_diseq_terms: FxHashSet::default(),
            seen_model_eq_requests: FxHashSet::default(),
            model_eq_rounds: 0,
        }
    }

    /// Normalized dedup key for a model-equality pair.
    pub(super) fn model_eq_key(eq: &ay_core::ModelEqualityRequest) -> (TermId, TermId) {
        if eq.lhs <= eq.rhs {
            (eq.lhs, eq.rhs)
        } else {
            (eq.rhs, eq.lhs)
        }
    }

    /// True when at least one request names a pair we have not encoded yet.
    pub(super) fn has_new_model_eq_pair(&self, eqs: &[ay_core::ModelEqualityRequest]) -> bool {
        eqs.iter().any(|eq| {
            !self
                .seen_model_eq_requests
                .contains(&Self::model_eq_key(eq))
        })
    }
}

impl SmtContext {
    /// Apply a term-growth action to the CNF state.
    ///
    /// Handles integer splits (branch-and-bound), disequality splits
    /// (value exclusion), and expression splits (multi-variable
    /// disequality decomposition). Returns `Ok(())` to continue the
    /// `'term_growth` loop or `Err(SmtResult)` to terminate.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn apply_term_growth_action(
        &mut self,
        action: TermGrowthAction,
        term_to_var: &mut BTreeMap<TermId, u32>,
        var_to_term: &mut BTreeMap<u32, TermId>,
        num_vars: &mut u32,
        sat: &mut ay_sat::Solver,
        split_state: &mut SplitState,
        debug: bool,
        dt_iterations: usize,
    ) -> Result<(), SmtResult> {
        match action {
            TermGrowthAction::Split { split } => {
                self.apply_integer_split(split, term_to_var, var_to_term, num_vars, sat, debug);
            }
            TermGrowthAction::DisequalitySplit { model, split } => {
                self.apply_disequality_split(
                    model,
                    split,
                    term_to_var,
                    var_to_term,
                    num_vars,
                    sat,
                    split_state,
                    debug,
                    dt_iterations,
                )?;
            }
            TermGrowthAction::ExpressionSplit { split } => {
                self.apply_expression_split(
                    split,
                    term_to_var,
                    var_to_term,
                    num_vars,
                    sat,
                    debug,
                    dt_iterations,
                )?;
            }
            TermGrowthAction::ModelEqualities { eqs } => {
                self.apply_model_equalities(
                    eqs,
                    term_to_var,
                    var_to_term,
                    num_vars,
                    sat,
                    split_state,
                    debug,
                    dt_iterations,
                )?;
            }
        }
        Ok(())
    }

    /// Encode speculative model-equality atoms requested by the theory
    /// (Phase 3 Fix 4; ports ay-dpll's `pipeline_encode_model_equality!`).
    ///
    /// For each NEW normalized pair: create the `=` atom (Int/Real coercion
    /// via `mk_eq_coerce`), allocate a CNF variable, bias its phase to true
    /// (the equality is a model-guided guess — CDCL retracts it via theory
    /// conflicts if wrong, never forced), add Int/Real triangle axioms
    /// `(= a b) ⇔ (a ≤ b) ∧ (b ≤ a)`, and — when the theory proved the
    /// equality (`implied` with a fully-mapped reason) — the lemma
    /// `¬reason ∨ eq`. Counted rounds are capped by `MAX_MODEL_EQ_ROUNDS`.
    #[allow(clippy::too_many_arguments)]
    fn apply_model_equalities(
        &mut self,
        eqs: Vec<ay_core::ModelEqualityRequest>,
        term_to_var: &mut BTreeMap<TermId, u32>,
        var_to_term: &mut BTreeMap<u32, TermId>,
        num_vars: &mut u32,
        sat: &mut ay_sat::Solver,
        split_state: &mut SplitState,
        debug: bool,
        dt_iterations: usize,
    ) -> Result<(), SmtResult> {
        let mut any_new = false;
        for eq in eqs {
            let key = SplitState::model_eq_key(&eq);
            if !split_state.seen_model_eq_requests.insert(key) {
                continue;
            }
            if !any_new {
                any_new = true;
                split_state.model_eq_rounds += 1;
                if split_state.model_eq_rounds > MAX_MODEL_EQ_ROUNDS {
                    if debug {
                        safe_eprintln!(
                            "[CHC-SMT] iter {}: model-equality round cap ({}) exceeded",
                            dt_iterations,
                            MAX_MODEL_EQ_ROUNDS
                        );
                    }
                    return Err(SmtResult::Unknown);
                }
            }

            let eq_term = self.terms.mk_eq_coerce(eq.lhs, eq.rhs);
            let eq_var = *term_to_var.entry(eq_term).or_insert_with(|| {
                *num_vars += 1;
                var_to_term.insert(*num_vars, eq_term);
                *num_vars
            });
            sat.ensure_num_vars(*num_vars as usize);
            let eq_sat_var = ay_sat::Variable::new(eq_var - 1);
            // Phase bias + activity: try the equality first, never force it.
            sat.set_var_phase(eq_sat_var, true);
            for _ in 0..20 {
                sat.bump_variable_activity(eq_sat_var);
            }

            // Triangle axioms for same-sort arithmetic pairs only (#8596).
            let lhs_sort = self.terms.sort(eq.lhs).clone();
            if matches!(lhs_sort, Sort::Int | Sort::Real) && &lhs_sort == self.terms.sort(eq.rhs) {
                let le_lr = self.terms.mk_le(eq.lhs, eq.rhs);
                let le_rl = self.terms.mk_le(eq.rhs, eq.lhs);
                let le_lr_var = *term_to_var.entry(le_lr).or_insert_with(|| {
                    *num_vars += 1;
                    var_to_term.insert(*num_vars, le_lr);
                    *num_vars
                });
                let le_rl_var = *term_to_var.entry(le_rl).or_insert_with(|| {
                    *num_vars += 1;
                    var_to_term.insert(*num_vars, le_rl);
                    *num_vars
                });
                sat.ensure_num_vars(*num_vars as usize);
                let le_lr_lit = ay_sat::Literal::positive(ay_sat::Variable::new(le_lr_var - 1));
                let le_rl_lit = ay_sat::Literal::positive(ay_sat::Variable::new(le_rl_var - 1));
                let eq_pos = ay_sat::Literal::positive(eq_sat_var);
                let eq_neg = ay_sat::Literal::negative(eq_sat_var);
                sat.add_clause(vec![eq_neg, le_lr_lit]);
                sat.add_clause(vec![eq_neg, le_rl_lit]);
                sat.add_clause(vec![eq_pos, le_lr_lit.negated(), le_rl_lit.negated()]);
            }

            // Theory-proved equality: add `¬reason ∨ eq` when every reason
            // literal maps to a CNF variable; drop silently otherwise (it is
            // an optional lemma, not required for soundness).
            if eq.implied && !eq.reason.is_empty() {
                let mut clause = Vec::with_capacity(eq.reason.len() + 1);
                let mut all_mapped = true;
                for lit in &eq.reason {
                    match term_to_var.get(&lit.term) {
                        Some(&cnf_var) => {
                            let sv = ay_sat::Variable::new(cnf_var - 1);
                            clause.push(if lit.value {
                                ay_sat::Literal::negative(sv)
                            } else {
                                ay_sat::Literal::positive(sv)
                            });
                        }
                        None => {
                            all_mapped = false;
                            break;
                        }
                    }
                }
                if all_mapped {
                    clause.push(ay_sat::Literal::positive(eq_sat_var));
                    sat.add_clause(clause);
                }
            }

            if debug {
                safe_eprintln!(
                    "[CHC-SMT] iter {}: encoded model equality {:?} = {:?} (round {})",
                    dt_iterations,
                    eq.lhs,
                    eq.rhs,
                    split_state.model_eq_rounds
                );
            }
        }
        Ok(())
    }

    fn apply_integer_split(
        &mut self,
        split: ay_core::SplitRequest,
        term_to_var: &mut BTreeMap<TermId, u32>,
        var_to_term: &mut BTreeMap<u32, TermId>,
        num_vars: &mut u32,
        sat: &mut ay_sat::Solver,
        debug: bool,
    ) {
        let floor_term = self.terms.mk_int(split.floor.clone());
        let ceil_term = self.terms.mk_int(split.ceil.clone());
        let le_atom = self.terms.mk_le(split.variable, floor_term);
        let ge_atom = self.terms.mk_ge(split.variable, ceil_term);

        let le_var = *term_to_var.entry(le_atom).or_insert_with(|| {
            *num_vars += 1;
            var_to_term.insert(*num_vars, le_atom);
            *num_vars
        });
        let ge_var = *term_to_var.entry(ge_atom).or_insert_with(|| {
            *num_vars += 1;
            var_to_term.insert(*num_vars, ge_atom);
            *num_vars
        });

        sat.ensure_num_vars(*num_vars as usize);

        let le_sat_var = ay_sat::Variable::new(le_var - 1);
        let ge_sat_var = ay_sat::Variable::new(ge_var - 1);
        self.apply_integer_split_phase_hint(sat, le_sat_var, ge_sat_var, &split);
        sat.add_clause(vec![
            ay_sat::Literal::positive(le_sat_var),
            ay_sat::Literal::positive(ge_sat_var),
        ]);

        if debug {
            safe_eprintln!(
                "[CHC-SMT] Added split clause: le_var={}, ge_var={}",
                le_var,
                ge_var
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_disequality_split(
        &mut self,
        model: Vec<bool>,
        split: ay_core::DisequalitySplitRequest,
        term_to_var: &mut BTreeMap<TermId, u32>,
        var_to_term: &mut BTreeMap<u32, TermId>,
        num_vars: &mut u32,
        sat: &mut ay_sat::Solver,
        split_state: &mut SplitState,
        debug: bool,
        dt_iterations: usize,
    ) -> Result<(), SmtResult> {
        use ay_core::term::TermData;

        let (lb, ub) =
            if self.terms.sort(split.variable) == &Sort::Int && split.excluded_value.is_integer() {
                self.infer_int_bounds_from_sat_model(split.variable, &model, var_to_term.iter())
            } else {
                (None, None)
            };
        let max_var_splits = match (lb, ub) {
            (Some(l), Some(u)) if l <= u => {
                let range_size = u.saturating_sub(l).saturating_add(1);
                if (1..=256).contains(&range_size) {
                    MAX_VAR_SPLITS.max(range_size as usize + 2)
                } else {
                    MAX_VAR_SPLITS
                }
            }
            _ => MAX_VAR_SPLITS,
        };

        let var_count = split_state
            .var_diseq_splits
            .entry(split.variable)
            .or_insert(0);
        *var_count += 1;
        if *var_count > max_var_splits {
            if let Some(diseq_term) = split.disequality_term {
                if split_state.promoted_diseq_terms.insert(diseq_term) {
                    if debug {
                        safe_eprintln!(
                            "[CHC-SMT] Exceeded max per-variable splits ({}) for {:?}; promoting {:?} to expression split",
                            max_var_splits, split.variable, diseq_term
                        );
                    }

                    split_state.var_diseq_splits.remove(&split.variable);

                    let (lhs, rhs) = match self.terms.get(diseq_term) {
                        TermData::App(Symbol::Named(name), args)
                            if args.len() == 2 && (name == "=" || name == "distinct") =>
                        {
                            (args[0], args[1])
                        }
                        TermData::Not(inner) => match self.terms.get(*inner) {
                            TermData::App(Symbol::Named(name), args)
                                if args.len() == 2 && (name == "=" || name == "distinct") =>
                            {
                                (args[0], args[1])
                            }
                            _ => {
                                if debug {
                                    safe_eprintln!(
                                        "[CHC-SMT] Promotion: cannot parse negated disequality term {:?}",
                                        diseq_term
                                    );
                                }
                                return Err(SmtResult::Unknown);
                            }
                        },
                        _ => {
                            if debug {
                                safe_eprintln!(
                                    "[CHC-SMT] Promotion: cannot parse disequality term {:?}",
                                    diseq_term
                                );
                            }
                            return Err(SmtResult::Unknown);
                        }
                    };

                    if !matches!(self.terms.sort(lhs), Sort::Int | Sort::Real)
                        || self.terms.sort(lhs) != self.terms.sort(rhs)
                    {
                        if debug {
                            safe_eprintln!(
                                "[CHC-SMT] Promotion: non-arithmetic disequality {:?} with sorts {:?} and {:?}",
                                diseq_term,
                                self.terms.sort(lhs),
                                self.terms.sort(rhs)
                            );
                        }
                        return Err(SmtResult::Unknown);
                    }

                    let lt_atom = self.terms.mk_lt(lhs, rhs);
                    let gt_atom = self.terms.mk_gt(lhs, rhs);

                    let lt_var = *term_to_var.entry(lt_atom).or_insert_with(|| {
                        *num_vars += 1;
                        var_to_term.insert(*num_vars, lt_atom);
                        *num_vars
                    });
                    let gt_var = *term_to_var.entry(gt_atom).or_insert_with(|| {
                        *num_vars += 1;
                        var_to_term.insert(*num_vars, gt_atom);
                        *num_vars
                    });

                    sat.ensure_num_vars(*num_vars as usize);

                    let lt_sat_var = ay_sat::Variable::new(lt_var - 1);
                    let gt_sat_var = ay_sat::Variable::new(gt_var - 1);
                    self.apply_disequality_split_phase_hint(sat, lt_sat_var, gt_sat_var, &split);

                    let guard_lit = term_to_var.get(&diseq_term).copied().map(|cnf_var| {
                        let sat_var = ay_sat::Variable::new(cnf_var - 1);
                        match self.terms.get(diseq_term) {
                            TermData::App(Symbol::Named(name), _) if name == "distinct" => {
                                ay_sat::Literal::negative(sat_var)
                            }
                            _ => ay_sat::Literal::positive(sat_var),
                        }
                    });

                    if let Some(g) = guard_lit {
                        sat.add_clause(vec![
                            g,
                            ay_sat::Literal::positive(lt_sat_var),
                            ay_sat::Literal::positive(gt_sat_var),
                        ]);
                    } else {
                        sat.add_clause(vec![
                            ay_sat::Literal::positive(lt_sat_var),
                            ay_sat::Literal::positive(gt_sat_var),
                        ]);
                    }

                    // Promotion path: continue the 'term_growth loop.
                    return Ok(());
                }
            }

            if debug {
                safe_eprintln!(
                    "[CHC-SMT] Exceeded max per-variable splits ({}) for {:?} - returning Unknown",
                    max_var_splits,
                    split.variable
                );
            }
            return Err(SmtResult::Unknown);
        }

        if debug {
            safe_eprintln!(
                "[CHC-SMT] iter {}: NeedDisequalitySplit on var {:?}, excluded={} (count={})",
                dt_iterations,
                split.variable,
                split.excluded_value,
                *var_count
            );
        }

        let var_sort = self.terms.sort(split.variable).clone();
        let (left_atom, right_atom) = if var_sort == Sort::Int && split.excluded_value.is_integer()
        {
            let excluded = split.excluded_value.numer().clone();
            let le_bound = self.terms.mk_int(&excluded - BigInt::from(1));
            let ge_bound = self.terms.mk_int(&excluded + BigInt::from(1));
            let left = self.terms.mk_le(split.variable, le_bound);
            let right = self.terms.mk_ge(split.variable, ge_bound);
            if debug {
                safe_eprintln!(
                    "[CHC-SMT] Created split atoms: left={:?} ({:?}), right={:?} ({:?})",
                    left,
                    self.terms.get(left),
                    right,
                    self.terms.get(right)
                );
            }
            (left, right)
        } else if var_sort == Sort::Int {
            let floor_val = split.excluded_value.floor().to_integer();
            let ceil_val = split.excluded_value.ceil().to_integer();
            let le_bound = self.terms.mk_int(floor_val);
            let ge_bound = self.terms.mk_int(ceil_val);
            let left = self.terms.mk_le(split.variable, le_bound);
            let right = self.terms.mk_ge(split.variable, ge_bound);
            if debug {
                safe_eprintln!(
                    "[CHC-SMT] Int var with non-integer excluded: left={:?} ({:?}), right={:?} ({:?})",
                    left,
                    self.terms.get(left),
                    right,
                    self.terms.get(right)
                );
            }
            (left, right)
        } else {
            let excluded_term = self.terms.mk_rational(split.excluded_value.clone());
            (
                self.terms.mk_lt(split.variable, excluded_term),
                self.terms.mk_gt(split.variable, excluded_term),
            )
        };

        let lt_var = *term_to_var.entry(left_atom).or_insert_with(|| {
            *num_vars += 1;
            var_to_term.insert(*num_vars, left_atom);
            *num_vars
        });
        let gt_var = *term_to_var.entry(right_atom).or_insert_with(|| {
            *num_vars += 1;
            var_to_term.insert(*num_vars, right_atom);
            *num_vars
        });

        sat.ensure_num_vars(*num_vars as usize);

        let lt_sat_var = ay_sat::Variable::new(lt_var - 1);
        let gt_sat_var = ay_sat::Variable::new(gt_var - 1);
        self.apply_disequality_split_phase_hint(sat, lt_sat_var, gt_sat_var, &split);
        let guard_lit = self
            .find_diseq_guard_atom(
                split.variable,
                &split.excluded_value,
                &model,
                var_to_term.iter(),
            )
            .and_then(|(guard_term, kind)| {
                term_to_var.get(&guard_term).copied().map(|cnf_var| {
                    let sat_var = ay_sat::Variable::new(cnf_var - 1);
                    match kind {
                        DiseqGuardKind::Distinct => ay_sat::Literal::negative(sat_var),
                        DiseqGuardKind::Eq => ay_sat::Literal::positive(sat_var),
                    }
                })
            });
        let guard_lit = if let Some(g) = guard_lit {
            g
        } else {
            let val_term = if split.excluded_value.is_integer() {
                self.terms.mk_int(split.excluded_value.numer().clone())
            } else {
                self.terms.mk_rational(split.excluded_value.clone())
            };
            let eq_atom = self.terms.mk_eq(split.variable, val_term);
            let eq_var = *term_to_var.entry(eq_atom).or_insert_with(|| {
                *num_vars += 1;
                var_to_term.insert(*num_vars, eq_atom);
                *num_vars
            });
            sat.ensure_num_vars(*num_vars as usize);
            let eq_sat_var = ay_sat::Variable::new(eq_var - 1);
            ay_sat::Literal::positive(eq_sat_var)
        };
        sat.add_clause(vec![
            guard_lit,
            ay_sat::Literal::positive(lt_sat_var),
            ay_sat::Literal::positive(gt_sat_var),
        ]);

        if debug {
            safe_eprintln!(
                "[CHC-SMT] Added disequality split clause: lt_var={}, gt_var={}, left_atom={:?}, right_atom={:?}, num_vars={}, var_to_term.len()={}",
                lt_var, gt_var, left_atom, right_atom, num_vars, var_to_term.len()
            );
            let lt_in_map = var_to_term.get(&lt_var);
            let gt_in_map = var_to_term.get(&gt_var);
            safe_eprintln!(
                "[CHC-SMT]   var_to_term[{}] = {:?}, var_to_term[{}] = {:?}",
                lt_var,
                lt_in_map,
                gt_var,
                gt_in_map
            );
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_expression_split(
        &mut self,
        split: ay_core::ExpressionSplitRequest,
        term_to_var: &mut BTreeMap<TermId, u32>,
        var_to_term: &mut BTreeMap<u32, TermId>,
        num_vars: &mut u32,
        sat: &mut ay_sat::Solver,
        debug: bool,
        dt_iterations: usize,
    ) -> Result<(), SmtResult> {
        use ay_core::term::TermData;

        if debug {
            safe_eprintln!(
                "[CHC-SMT] iter {}: NeedExpressionSplit on disequality {:?}",
                dt_iterations,
                split.disequality_term
            );
        }

        let (lhs, rhs) = match self.terms.get(split.disequality_term) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                if name == "=" || name == "distinct" {
                    (args[0], args[1])
                } else {
                    if debug {
                        safe_eprintln!("[CHC-SMT] ExpressionSplit: unexpected operator {:?}", name);
                    }
                    return Err(SmtResult::Unknown);
                }
            }
            TermData::Not(inner) => match self.terms.get(*inner) {
                TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                    if name == "=" || name == "distinct" {
                        (args[0], args[1])
                    } else {
                        if debug {
                            safe_eprintln!(
                                "[CHC-SMT] ExpressionSplit: unexpected negated operator {:?}",
                                name
                            );
                        }
                        return Err(SmtResult::Unknown);
                    }
                }
                _ => {
                    if debug {
                        safe_eprintln!(
                            "[CHC-SMT] ExpressionSplit: cannot parse negated disequality term {:?}",
                            split.disequality_term
                        );
                    }
                    return Err(SmtResult::Unknown);
                }
            },
            _ => {
                if debug {
                    safe_eprintln!(
                        "[CHC-SMT] ExpressionSplit: cannot parse disequality term {:?}",
                        split.disequality_term
                    );
                }
                return Err(SmtResult::Unknown);
            }
        };

        if !matches!(self.terms.sort(lhs), Sort::Int | Sort::Real)
            || self.terms.sort(lhs) != self.terms.sort(rhs)
        {
            if debug {
                safe_eprintln!(
                    "[CHC-SMT] ExpressionSplit: non-arithmetic disequality {:?} with sorts {:?} and {:?}",
                    split.disequality_term,
                    self.terms.sort(lhs),
                    self.terms.sort(rhs)
                );
            }
            return Err(SmtResult::Unknown);
        }

        let lt_atom = self.terms.mk_lt(lhs, rhs);
        let gt_atom = self.terms.mk_gt(lhs, rhs);

        if debug {
            safe_eprintln!(
                "[CHC-SMT] Created expression split atoms: lt={:?} ({:?}), gt={:?} ({:?})",
                lt_atom,
                self.terms.get(lt_atom),
                gt_atom,
                self.terms.get(gt_atom)
            );
        }

        let lt_var = *term_to_var.entry(lt_atom).or_insert_with(|| {
            *num_vars += 1;
            var_to_term.insert(*num_vars, lt_atom);
            *num_vars
        });
        let gt_var = *term_to_var.entry(gt_atom).or_insert_with(|| {
            *num_vars += 1;
            var_to_term.insert(*num_vars, gt_atom);
            *num_vars
        });

        sat.ensure_num_vars(*num_vars as usize);

        let lt_sat_var = ay_sat::Variable::new(lt_var - 1);
        let gt_sat_var = ay_sat::Variable::new(gt_var - 1);
        let guard_term = split.disequality_term;
        let guard_lit = term_to_var.get(&guard_term).map(|&cnf_var| {
            let sat_var = ay_sat::Variable::new(cnf_var - 1);
            match self.terms.get(guard_term) {
                TermData::App(Symbol::Named(name), _) if name == "distinct" => {
                    ay_sat::Literal::negative(sat_var)
                }
                _ => ay_sat::Literal::positive(sat_var),
            }
        });

        if let Some(g) = guard_lit {
            sat.add_clause(vec![
                g,
                ay_sat::Literal::positive(lt_sat_var),
                ay_sat::Literal::positive(gt_sat_var),
            ]);
        } else {
            sat.add_clause(vec![
                ay_sat::Literal::positive(lt_sat_var),
                ay_sat::Literal::positive(gt_sat_var),
            ]);
        }

        if debug {
            safe_eprintln!(
                "[CHC-SMT] Added expression split clause: lt_var={}, gt_var={}, guard={:?}",
                lt_var,
                gt_var,
                guard_lit
            );
        }
        Ok(())
    }
}
