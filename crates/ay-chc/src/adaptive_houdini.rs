// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conjunctive Houdini pre-engine for single-predicate transition systems.
//!
//! The vmt-chc lustre family encodes reactive systems as a single `state`
//! predicate with a query of the form `state(a_0..a_n) ∧ ¬a_i ⇒ false`
//! where Bool argument `a_i` is the "property holds" flag. The Tier-1
//! query-flag prepass (`try_query_flag_invariant_prepass`) handles the
//! instances where the flag alone is inductive. This engine handles the next
//! tier: instances whose invariant is a CONJUNCTION of the flag with simple
//! support lemmas over the predicate arguments (flag polarity literals,
//! variable/constant bounds, variable orderings).
//!
//! # Algorithm (classic Houdini, model-based dropping)
//!
//! 1. Extract the single-predicate transition system (init / transition /
//!    query over canonical state vars `v0..vN` and `v{i}_next`), inline
//!    clause-local definitional equalities, and equality-propagate the
//!    solver backgrounds.
//! 2. Build a finite candidate pool over the predicate arguments (ordered
//!    most-valuable-first; every class capped and deduped):
//!    - the query-flag literal (always),
//!    - atoms mined from init/transition/query (comparisons, Bool
//!      equivalences, guarded `or`/`implies` clauses, definitional
//!      `v_next = φ(state)` right-hand sides) plus their negations,
//!    - `b` and `¬b` for every Bool argument,
//!    - `x ≤ c` / `x ≥ c` for every Int argument and harvested constant,
//!    - `t ≤ c` / `t ≥ c` for mined linear terms (difference/sum bounds),
//!    - `xi ≤ xj` for Int argument pairs.
//! 3. Filter to the greatest inductive subset containing the flag:
//!    - A.1: prove `init ⇒ flag` (make-or-break; generous per-call cap);
//!    - A.2: while `init ∧ ¬(∧ pool)` is SAT, drop every candidate the
//!      model violates (one model prunes many; slow tail stops early);
//!    - A.3: time-capped per-candidate `init ∧ ¬cand` proofs; the
//!      unprocessed tail is dropped conservatively;
//!    - B: while `(∧ pool) ∧ trans ∧ ¬(∧ pool')` is SAT, drop every
//!      candidate the model violates in the POST-state; on a combined-query
//!      Unknown a definitive per-candidate sweep takes over.
//!
//!    Candidates whose value cannot be determined under a model are dropped
//!    conservatively (sound: dropping only weakens the conjunction).
//! 4. Answer `sat` iff the query-flag literal survives AND the surviving
//!    conjunction passes full validation against EVERY original clause via
//!    AY's executor-backed SMT (same standard as the query-flag prepass;
//!    fail-closed on Sat/Unknown/budget).
//!
//! All SMT calls go through AY's own executor (hermetic): the Houdini loop
//! uses `PersistentExecutorSmtContext` (init/transition asserted once as
//! background, per-query deltas), final validation uses `ay_says_unsat`.

use crate::adaptive::{ay_says_unsat, ay_says_unsat_with_dv_hint, AdaptivePortfolio};
use crate::adaptive_decision_log::DecisionEntry;
use crate::classifier::ProblemFeatures;
use crate::engine_result::ValidationEvidence;
use crate::expr::evaluate_expr;
use crate::pdr::{InvariantModel, PredicateInterpretation};
use crate::portfolio::PortfolioResult;
use crate::qual_mine::{qual_mine_enabled, qual_mixed_enabled, MinedQualifiers};
use crate::smt::{PersistentExecutorSmtContext, SmtResult, SmtValue};
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet};
use ay_core::time::Instant;
use std::time::Duration;

/// Cap on Int constants harvested from the init/transition formulas.
const HOUDINI_MAX_CONSTANTS: usize = 8;
/// Cap on candidate atoms mined syntactically from init/transition/query
/// (each is admitted with its negation, so the pool share is double this).
const HOUDINI_MAX_MINED_ATOMS: usize = 320;
/// Cap on linear terms mined from comparisons-with-constants; each term
/// gets `t ≤ c` / `t ≥ c` candidates for every harvested constant
/// (difference/sum bounds, e.g. metros' `h - f ≤ 30` beacon distance).
const HOUDINI_MAX_MINED_TERMS: usize = 48;
/// Max Int-arg count at which 2-variable sum/difference bound candidates
/// (`vi±vj ≤/≥ c`) are generated. Gated low so wide lustre predicates (~65
/// args) are not flooded with O(arity^2·|consts|) candidates (#9079).
const HOUDINI_SMALL_ARITY: usize = 6;
/// Cap on ordered Int argument pairs used for `xi ≤ xj` candidates.
/// Both orders of a pair are admitted, so surviving `xi ≤ xj ∧ xj ≤ xi`
/// captures variable equalities (common in lustre saved-value encodings).
const HOUDINI_MAX_VAR_PAIRS: usize = 256;
/// Overall candidate pool cap (keeps each SMT query tractable). Rounds are
/// cheap (model-based dropping prunes many candidates per model), so this
/// is sized for wide lustre predicates (~65 args).
const HOUDINI_MAX_POOL: usize = 2048;
/// Max transition-guard splitters tried by disjunctive (2-phase) synthesis.
const HOUDINI_MAX_SPLITTERS: usize = 6;
/// Bool-arg ↔ Int-bound guarded-implication rows (AY_CHC_GUARDED_IMPL_HINTS).
/// Base harvested constants (smallest |c| first) seeded into the guard
/// thresholds before ±1 expansion.
const GUARDED_IMPL_MAX_BASE_CONSTS: usize = 4;
/// Final cap on guard thresholds per (Bool arg, Int var) after ±1 expansion.
/// Covers the small contiguous threshold band lustre counters live in (e.g.
/// two_counters needs 0,1,2,3). Kept small so the pool stays under the cap.
const GUARDED_IMPL_MAX_CONSTS: usize = 6;
/// Max Int vars correlated against Bool args for the guarded rows.
const GUARDED_IMPL_MAX_INT_VARS: usize = 4;
/// Max Bool args correlated against Int bounds for the guarded rows.
const GUARDED_IMPL_MAX_BOOL_ARGS: usize = 16;
/// Inc-16 S3 (Stage-5 widening) caps. The widening adds, ABOVE
/// `HOUDINI_SMALL_ARITY` only (wide lustre predicates; aeval small-arity
/// pools are byte-identical), the ≤2-var inequality vocabulary the residual
/// attribution showed missing: `vi±vj ⋈ c` rows restricted to variable pairs
/// CO-OCCURRING in a transition linear term (not O(arity²)), guarded
/// `guard → (vi−vj ⋈ c)` rows from mined ITE guards, and the init-cube
/// 2-phase splitter (metros/MESI witness shape). Kill switch:
/// `AY_HOUDINI_STAGE5=0`. Sound regardless: every candidate still flows
/// through `validate_invariant_against_clauses`.
const STAGE5_MAX_PAIRS: usize = 32;
/// Constants (smallest |c| first) used for the co-occurring pair rows.
const STAGE5_MAX_CONSTS: usize = 4;
/// Mined ITE guards admitted for guarded rows.
const STAGE5_MAX_GUARDS: usize = 4;
/// Co-occurring pairs used per guard for guarded rows.
const STAGE5_MAX_GUARD_PAIRS: usize = 4;
/// Constants used per guarded row class.
const STAGE5_MAX_GUARD_CONSTS: usize = 2;
/// Pool cap when the stage-5 classes are active (wide predicates put
/// ~1800 var-const bound rows in the pool already; the widening needs
/// headroom so its rows are not truncated away).
const STAGE5_MAX_POOL: usize = 3072;
/// Phase-pool cap for the wide-arity disjunctive (init-cube) route: the
/// per-candidate phase init filter is sequential, so the wide route needs a
/// small most-valuable-first pool to fit the prepass window.
const STAGE5_PHASE_POOL: usize = 384;
/// Max init conjuncts admitted into the init-cube splitter.
const STAGE5_MAX_INIT_CUBE: usize = 256;
/// Slack on top of the pool-derived rounds cap. Every SAT round drops at
/// least one candidate (else the loop fails closed), so the loop needs at
/// most `pool + 2` rounds; the budget check per round is the anti-stall
/// guard. Empirically lustre instances converge in well under a second
/// (model-based dropping prunes ~10+ candidates per round).
const HOUDINI_ROUNDS_SLACK: usize = 8;
/// Hard per-SMT-call cap (each call also bounded by remaining/4).
const HOUDINI_PER_CALL_CAP: Duration = Duration::from_secs(5);
/// Phase-B fast-path: once the pool exceeds this width the monolithic combined
/// consecution query (`∧pool ∧ T ∧ ¬∧pool'`) reliably burns the full call cap
/// and returns Unknown (the negated-pool disjunction is too wide for the
/// executor). Above this width we skip straight to the per-candidate sweep,
/// which is fast (10-27ms/query) and definitive. The combined query is only an
/// optimization (it batch-drops via one model); the sweep computes the SAME
/// drops, so skipping it cannot change the inductive fixpoint.
const HOUDINI_PHASEB_COMBINED_POOL_LIMIT: usize = 64;

/// The safety literal that anchors the Houdini candidate pool, derived from the
/// single query clause (#9078).
enum HoudiniSeed {
    /// Bool "property-OK" flag at argument position `idx` (the original
    /// query-flag path): seed literal is `flag` when `positive`, else `¬flag`.
    Flag { idx: usize, positive: bool },
    /// Arithmetic query `state(args) ∧ φ ⇒ false`: the seed is the negated bad
    /// condition `¬φ` (the safe region), expressed over the query's predicate-
    /// argument vars paired with their arg positions, to be remapped onto the
    /// canonical state vars.
    Arith {
        safe: ChcExpr,
        pos_map: Vec<(ChcVar, usize)>,
    },
}

impl HoudiniSeed {
    /// Resolve the seed to a literal over the transition system's canonical
    /// state vars. SOUND for either variant: the produced literal is exactly
    /// the query's safety condition; Houdini still validates every survivor
    /// against the original clauses, so a mis-derived seed can only fail the
    /// route, never certify an unsafe system.
    fn resolve(&self, state_vars: &[ChcVar]) -> ChcExpr {
        match self {
            Self::Flag { idx, positive } => {
                let flag = ChcExpr::var(state_vars[*idx].clone());
                if *positive {
                    flag
                } else {
                    ChcExpr::not(flag)
                }
            }
            Self::Arith { safe, pos_map } => {
                let subst: Vec<(ChcVar, ChcExpr)> = pos_map
                    .iter()
                    .filter(|(_, i)| *i < state_vars.len())
                    .map(|(qv, i)| (qv.clone(), ChcExpr::var(state_vars[*i].clone())))
                    .collect();
                safe.substitute(&subst)
            }
        }
    }
}

impl AdaptivePortfolio {
    /// Conjunctive Houdini prepass (lustre-class tier 2).
    ///
    /// Runs AFTER `try_query_flag_invariant_prepass` fails, under the same
    /// gate: single predicate, no arrays/BV/datatypes, single query of the
    /// form `state(args) ∧ ¬flag ⇒ false` (or `∧ flag`) for a Bool argument.
    ///
    /// Returns `Some(Safe)` ONLY when the surviving conjunction (which must
    /// still contain the query-flag literal) is validated against every
    /// original clause. Fail-closed `None` on any budget/Unknown ambiguity.
    pub(crate) fn try_houdini_conjunctive_prepass(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        let route_start = Instant::now();
        let (pred_id, seed) = self.houdini_seed_gate(features)?;

        // Scaled with the global budget; fail fast when nearly exhausted.
        // BV problems get a wider slice (#11 QUAL-MINE): each consecution
        // query bit-blasts a 32-bit transition background, so the same
        // candidate pool needs ~2-3x the wall clock of the Int/lustre runs.
        // Pure scheduling (G2) — no verdict surface changes.
        let (percent, cap) = if self.problem.has_bv_sorts() {
            (33, Duration::from_mins(2))
        } else {
            (15, Duration::from_secs(90))
        };
        let route_budget =
            self.scaled_probe_budget(deadline, Duration::from_secs(10), percent, cap);
        if route_budget < Duration::from_millis(200) {
            return None;
        }

        let outcome = self.houdini_run(pred_id, &seed, route_start, route_budget);
        // Disjunctive (2-phase) fallback when the conjunctive run fails
        // (#disjunctive-houdini, default-OFF via AY_HOUDINI_DISJUNCTIVE). Sound:
        // its invariant is validated against every original clause.
        let outcome = match outcome {
            Ok(r) => Ok(r),
            Err(e) if disjunctive_enrichment_enabled() => self
                // Share the prepass window (`route_start`) so the conjunctive +
                // disjunctive attempts together stay within `route_budget` and
                // never starve the downstream portfolio of its wall-clock.
                .try_disjunctive_phase_houdini(pred_id, route_start, route_budget)
                .map_err(|de| format!("{e}; disjunctive: {de}")),
            Err(e) => Err(e),
        };

        let (validated, gate_reason, model) = match outcome {
            Ok((model, survivors, rounds)) => (
                true,
                format!(
                    "houdini fixpoint with {survivors} survivors after {rounds} rounds; \
                     validated on all original clauses"
                ),
                Some(model),
            ),
            Err(reason) => (false, reason, None),
        };
        if !validated && houdini_debug() {
            safe_eprintln!("houdini: prepass failure reason: {gate_reason}");
        }

        self.decision_log.log_decision(DecisionEntry {
            stage: "houdini_conjunctive_prepass",
            gate_result: validated,
            gate_reason,
            budget_secs: route_budget.as_secs_f64(),
            elapsed_secs: route_start.elapsed().as_secs_f64(),
            result: if validated { "safe" } else { "unknown" },
            lemmas_learned: 0,
            max_frame: 0,
        });
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: houdini conjunctive prepass {} in {:.2}s",
                if validated { "validated" } else { "failed" },
                route_start.elapsed().as_secs_f64()
            );
        }

        model.map(|model| {
            (
                PortfolioResult::Safe(model),
                ValidationEvidence::FullVerification,
            )
        })
    }

    /// Gate: same shape recognition as the query-flag prepass.
    ///
    /// Returns `(predicate, flag_arg_index, flag_polarity)` where
    /// `flag_polarity == true` means the candidate literal is `flag`
    /// (query constraint `¬flag`) and `false` means `¬flag`.
    fn houdini_query_flag_gate(
        &self,
        features: &ProblemFeatures,
    ) -> Option<(PredicateId, usize, bool)> {
        // #11 QUAL-MINE: pure-BV+Bool single-predicate problems (the vmt
        // shape) are no longer excluded — the mined BV candidate vocabulary
        // gives the drop-loop something to work with there. Sound regardless:
        // survivors are validated against every original clause.
        // `AY_CHC_DISABLE_HOUDINI_BV=1` restores the old exclusion.
        if !features.is_single_predicate
            || features.uses_arrays
            || features.uses_datatypes
            || (self.problem.has_bv_sorts() && !houdini_bv_enabled())
        {
            return None;
        }
        let mut queries = self.problem.queries();
        let query = queries.next()?;
        if queries.next().is_some() {
            return None;
        }
        let [(qpred, qargs)] = query.body.predicates.as_slice() else {
            return None;
        };
        let constraint = query.body.constraint.as_ref()?;
        let (flag_var, positive) = match constraint {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
                ChcExpr::Var(v) => (v.clone(), true),
                _ => return None,
            },
            ChcExpr::Var(v) => (v.clone(), false),
            _ => return None,
        };
        let flag_idx = qargs
            .iter()
            .position(|a| matches!(a, ChcExpr::Var(v) if *v == flag_var))?;
        let pred = self.problem.get_predicate(*qpred)?;
        if !matches!(pred.arg_sorts.get(flag_idx), Some(ChcSort::Bool)) {
            return None;
        }
        Some((*qpred, flag_idx, positive))
    }

    /// Seed gate: prefer the Bool query-flag shape (unchanged behaviour); fall
    /// back to the arithmetic-query shape (#9078).
    fn houdini_seed_gate(&self, features: &ProblemFeatures) -> Option<(PredicateId, HoudiniSeed)> {
        if let Some((pred, idx, positive)) = self.houdini_query_flag_gate(features) {
            return Some((pred, HoudiniSeed::Flag { idx, positive }));
        }
        self.houdini_arith_query_gate(features)
    }

    /// Gate for an ARITHMETIC single-predicate query (#9078).
    ///
    /// Recognises `state(args) ∧ φ ⇒ false` where `φ` is an arithmetic bad
    /// condition over the predicate's argument variables (e.g. aeval
    /// multi-phase `s_split`: `inv(A,B) ∧ ¬(B ≥ 0) ⇒ false`). The seed is the
    /// negated bad condition `safe = ¬φ` (the safe region). Houdini's existing
    /// candidate pool (bounds harvested from init/transition constants) plus
    /// this seed is exactly what such linear-conjunctive invariants need; the
    /// SMT engine already discharges the mod/ite consecution checks (verified
    /// fast). Requires each predicate argument to be a DISTINCT plain variable
    /// (clean position map) and `φ` to mention only those argument variables,
    /// so `safe` is expressible over the state. SOUND: the seed only steers the
    /// search; every survivor is validated against the original clauses.
    fn houdini_arith_query_gate(
        &self,
        features: &ProblemFeatures,
    ) -> Option<(PredicateId, HoudiniSeed)> {
        // #11 QUAL-MINE: BV un-gated here too (single-predicate by
        // construction below); see `houdini_query_flag_gate`.
        if features.uses_arrays
            || features.uses_datatypes
            || (self.problem.has_bv_sorts() && !houdini_bv_enabled())
        {
            return None;
        }
        // Exactly ONE real (arity > 0) predicate — the transition-system
        // invariant predicate. (A 0-arity Bool "fail" query marker is allowed
        // alongside it and unfolded below; aeval s_split uses exactly that.)
        let real_preds: Vec<&_> = self
            .problem
            .predicates()
            .iter()
            .filter(|p| p.arity() > 0)
            .collect();
        let [real_pred] = real_preds.as_slice() else {
            return None;
        };

        // The single goal clause (head = false).
        let mut goals = self.problem.queries();
        let goal = goals.next()?;
        if goals.next().is_some() {
            return None;
        }
        let [(gpred, gargs)] = goal.body.predicates.as_slice() else {
            return None;
        };

        // Resolve (pred_id, pred_args, bad_condition φ) — either directly when
        // the real predicate sits in the goal under an arithmetic constraint, or
        // by unfolding a 0-arity Bool marker predicate `M` whose single defining
        // clause is `P(args) ∧ φ ⇒ M` (the `fail` indirection). The unfold is an
        // exact equivalence: `M ⇒ false` ∧ `P ∧ φ ⇒ M`  ≡  `P ∧ φ ⇒ false`.
        let (pred_id, pred_args, bad): (PredicateId, Vec<ChcExpr>, ChcExpr) =
            match goal.body.constraint.as_ref() {
                Some(constraint) if gpred == &real_pred.id => {
                    (*gpred, gargs.clone(), constraint.clone())
                }
                _ if gargs.is_empty() => {
                    // Marker unfold: `M` must be 0-arity and defined by exactly
                    // one clause `P(args) ∧ φ ⇒ M` with P the real predicate.
                    let mut defs = self
                        .problem
                        .clauses()
                        .iter()
                        .filter(|cl| cl.head.predicate_id() == Some(*gpred));
                    let def = defs.next()?;
                    if defs.next().is_some() {
                        return None;
                    }
                    let [(ppred, pargs)] = def.body.predicates.as_slice() else {
                        return None;
                    };
                    if *ppred != real_pred.id {
                        return None;
                    }
                    let phi = def.body.constraint.as_ref()?.clone();
                    (*ppred, pargs.clone(), phi)
                }
                _ => return None,
            };

        // Each predicate argument must be a distinct plain variable.
        let mut pos_map: Vec<(ChcVar, usize)> = Vec::with_capacity(pred_args.len());
        let mut seen: DetHashSet<String> = DetHashSet::default();
        for (i, a) in pred_args.iter().enumerate() {
            match a {
                ChcExpr::Var(v) if seen.insert(v.name.clone()) => pos_map.push((v.clone(), i)),
                _ => return None,
            }
        }
        // safe = ¬(bad condition). It must mention only the argument variables.
        let safe = ChcExpr::not(bad);
        let arg_names: DetHashSet<String> = pos_map.iter().map(|(v, _)| v.name.clone()).collect();
        if !safe.vars().iter().all(|v| arg_names.contains(&v.name)) {
            return None;
        }
        Some((pred_id, HoudiniSeed::Arith { safe, pos_map }))
    }

    /// Run the Houdini loop and validate the survivors.
    ///
    /// Returns `(invariant model, surviving candidates, rounds)` on success,
    /// or a human-readable failure reason for the decision log.
    fn houdini_run(
        &self,
        pred_id: PredicateId,
        seed: &HoudiniSeed,
        route_start: Instant,
        route_budget: Duration,
    ) -> Result<(InvariantModel, usize, usize), String> {
        let ts = TransitionSystem::from_chc_problem(&self.problem)
            .map_err(|e| format!("transition system extraction failed: {e}"))?;
        let pred = self
            .problem
            .get_predicate(pred_id)
            .ok_or_else(|| "predicate lookup failed".to_string())?;
        let arity = pred.arity();
        // `TransitionSystem::new` may append mod-elimination aux vars AFTER
        // the canonical argument vars; candidates only range over the args.
        if ts.state_vars().len() < arity {
            return Err("state vars shorter than predicate arity".to_string());
        }
        let state_vars = &ts.state_vars()[..arity];
        // #9078: the seed is the safety literal to anchor the candidate pool —
        // a Bool property flag (the original query-flag path) OR the negated
        // arithmetic bad-condition `¬φ` from an arithmetic query, mapped onto
        // the canonical state vars.
        let seed_literal = seed.resolve(state_vars);

        // Inline clause-local definitional equalities (equivalent over the
        // state vars) so the candidate miner sees the relations hidden
        // behind locals and the solver backgrounds shrink.
        let next_names: Vec<String> = state_vars
            .iter()
            .map(|v| format!("{}_next", v.name))
            .collect();
        let allowed: DetHashSet<&str> = state_vars
            .iter()
            .map(|v| v.name.as_str())
            .chain(next_names.iter().map(String::as_str))
            .collect();
        let init_inlined = inline_local_definitions(&ts.init, &allowed);
        let trans_inlined = inline_local_definitions(&ts.transition, &allowed);
        let query_inlined = inline_local_definitions(&ts.query, &allowed);

        // #11 QUAL-MINE: problem-derived candidate vocabulary (per-clause
        // atoms propagated across argument-sharing predicates, difference
        // terms, BV wraparound distances, control clauses, guarded data rows,
        // loop templates). BV problems ONLY: the Int/lustre pools are already
        // tuned (their vocabulary classes above cover the same ground) and
        // measurably regress when the route budget is spent on the extra
        // rows (s_split_02: the disjunctive fallback starves); the BV pools
        // are otherwise nearly empty, so this is where the vocabulary pays.
        // Pure candidate content (G2) — every survivor still passes
        // per-clause validation.
        let mined = if qual_mine_enabled() && self.problem.has_bv_sorts() {
            MinedQualifiers::mine(&self.problem).for_predicate(pred_id, state_vars)
        } else {
            Vec::new()
        };
        let mut pool = build_candidate_pool(
            state_vars,
            &seed_literal,
            &init_inlined,
            &trans_inlined,
            &query_inlined,
            &mined,
        );
        let pool_size = pool.len();

        let budget = HoudiniBudget {
            route_start,
            route_budget,
        };

        // Phase A — init filtering: keep exactly the candidates with a
        // proven `init ⇒ cand`. The (equality-propagated) init formula is
        // asserted ONCE as solver background; all checks are small deltas.
        let init_bg = propagate_background(&init_inlined);
        let mut init_ctx = PersistentExecutorSmtContext::new();
        // Inc-21: this route's queries are SAT-direction-heavy over a large
        // guarded-eq background — the inc-14 EqDiffVar pass taxes every
        // check and defeats the model search (the inc-18 cliff). Seed the
        // sessions dv-off-first (the proven AY_EQ_DIFFVAR=0 behavior for
        // this route). See `prefer_dv_off_first`.
        init_ctx.prefer_dv_off_first();
        if !init_ctx.ensure_background(&init_bg, budget.call_cap()?) {
            return Err("init background setup failed".to_string());
        }
        let empty_model = FxHashMap::default();

        // A.1 — the flag's own init check is make-or-break for the whole
        // route: run it first with the full per-call cap. UNSAT is required;
        // SAT/Unknown means the flag is not (provably) init-implied.
        match init_ctx.check_query(
            &ChcExpr::not(seed_literal.clone()),
            &empty_model,
            budget.call_cap_generous()?,
        ) {
            res if res.is_unsat() => {
                if let Some(flag_cand) = pool.iter_mut().find(|c| c.expr == seed_literal) {
                    flag_cand.init_verified = true;
                }
            }
            SmtResult::Sat(_) => return Err("flag literal not implied by init".to_string()),
            _ => return Err("init check unknown on the flag literal".to_string()),
        }

        // A.2 — combined model-based init rounds for CHEAP bulk dropping:
        // while `init ∧ ¬(∧pool)` is SAT, one model kills every candidate it
        // violates; UNSAT proves `init ⇒ cand` for ALL survivors at once.
        // The tail of this loop degenerates into expensive near-UNSAT
        // searches, so slow rounds stop early — the per-candidate init
        // proofs run later, AFTER consecution pruning has shrunk the pool.
        let mut init_rounds = 0usize;
        let init_max_rounds = pool.len() + HOUDINI_ROUNDS_SLACK;
        let a2_cap = budget
            .remaining()?
            .div_f64(5.0)
            .min(Duration::from_millis(2500));
        let a2_start = Instant::now();
        loop {
            init_rounds += 1;
            if init_rounds > init_max_rounds || a2_start.elapsed() > a2_cap {
                break;
            }
            let call_cap = budget
                .call_cap()
                .map_err(|e| format!("{e} during init rounds (pool {})", pool.len()))?;
            let round_start = Instant::now();
            let delta = ChcExpr::not(ChcExpr::and_all(pool.iter().map(|c| c.expr.clone())));
            let round_result = init_ctx.check_query(&delta, &empty_model, call_cap);
            if houdini_debug() {
                let label = match &round_result {
                    SmtResult::Sat(_) => "sat",
                    r if r.is_unsat() => "unsat",
                    _ => "unknown",
                };
                safe_eprintln!(
                    "houdini: init round {init_rounds} {label}, pool {} ({:.2}s)",
                    pool.len(),
                    route_start.elapsed().as_secs_f64()
                );
            }
            match round_result {
                SmtResult::Sat(model) => {
                    let before = pool.len();
                    pool.retain(|cand| cand.init_verified || cand.holds_in(&model));
                    if !contains_flag(&pool, &seed_literal) {
                        return Err("flag literal not implied by init".to_string());
                    }
                    if pool.len() == before {
                        break;
                    }
                }
                res if res.is_unsat() => {
                    for cand in pool.iter_mut() {
                        cand.init_verified = true;
                    }
                    break;
                }
                _ => break,
            }
            if round_start.elapsed() > Duration::from_millis(800) {
                break; // grinding the tail; consecution pruning is cheaper
            }
        }

        // A.3 — time-capped per-candidate init proofs (`init ∧ ¬cand`):
        // UNSAT keeps, a SAT model drops the candidate plus everything else
        // it violates, Unknown drops just the candidate. The pool is ordered
        // most-valuable-first (flag, mined atoms, bool literals, bounds,
        // pairs), so when the time cap fires the UNPROCESSED tail is dropped
        // CONSERVATIVELY (sound: weakening) instead of stalling the route.
        // (A batched `init ⇒ ∧group` variant was tried and regressed:
        // group UNSAT proofs are far slower than singleton deltas here.)
        let mut init_calls = 0usize;
        let sweep_cap = budget.remaining()?.mul_f64(0.4);
        let sweep_start = Instant::now();
        let mut idx = 0;
        while idx < pool.len() {
            if pool[idx].init_verified {
                idx += 1;
                continue;
            }
            if sweep_start.elapsed() > sweep_cap {
                break;
            }
            let call_cap = budget
                .call_cap()
                .map_err(|e| format!("{e} during init sweep (pool {})", pool.len()))?;
            init_calls += 1;
            let delta = ChcExpr::not(pool[idx].expr.clone());
            match init_ctx.check_query(&delta, &empty_model, call_cap) {
                res if res.is_unsat() => {
                    pool[idx].init_verified = true;
                    idx += 1;
                }
                SmtResult::Sat(model) => {
                    // The SAT result itself proves init ⇏ pool[idx]; the
                    // model additionally batch-drops other violated ones.
                    let checked = pool[idx].expr.clone();
                    pool.retain(|cand| {
                        cand.expr != checked && (cand.init_verified || cand.holds_in(&model))
                    });
                }
                _ => {
                    // Unknown: drop only the candidate under test (the flag
                    // was verified in A.1, so it is never dropped here).
                    pool.remove(idx);
                }
            }
        }
        let before_truncation = pool.len();
        pool.retain(|cand| cand.init_verified);
        if houdini_debug() {
            safe_eprintln!(
                "houdini: init phase kept {} of {pool_size} candidates ({} truncated) in {init_calls} sweep calls ({:.2}s)",
                pool.len(),
                before_truncation - pool.len(),
                route_start.elapsed().as_secs_f64()
            );
        }
        if !contains_flag(&pool, &seed_literal) {
            return Err("flag literal lost during init filtering".to_string());
        }

        // Phase B — consecution filtering to the greatest inductive subset.
        // The transition formula is asserted ONCE as background; each round
        // queries `∧pool ∧ ¬(∧pool')` and batch-drops every candidate the
        // model violates in the POST-state. Dropping preserves the init
        // implication (init ⇒ each survivor individually). On a combined-
        // query Unknown, a definitive per-candidate sweep takes over.
        let trans_bg = propagate_background(&trans_inlined);
        let mut trans_ctx = PersistentExecutorSmtContext::new();
        // Inc-21: dv-off-first, same rationale as `init_ctx` above.
        trans_ctx.prefer_dv_off_first();
        if !trans_ctx.ensure_background(&trans_bg, budget.call_cap()?) {
            return Err("transition background setup failed".to_string());
        }
        let mut rounds = 0usize;
        let max_rounds = pool_size + HOUDINI_ROUNDS_SLACK;
        let phaseb_fast = houdini_phaseb_fast_enabled();
        // #11 QUAL-MINE: on BV problems the monolithic combined consecution
        // query is the CHEAP path (one bit-blasted solve whose model batch-
        // drops many candidates), while the per-candidate sweep pays the
        // bit-blast once per candidate — the opposite economics of the wide
        // lustre pools the 64-candidate limit was tuned for. Let BV pools use
        // the combined query up to the full pool cap; an Unknown still falls
        // back to the sweep exactly as before.
        let combined_pool_limit = if self.problem.has_bv_sorts() {
            HOUDINI_MAX_POOL
        } else {
            HOUDINI_PHASEB_COMBINED_POOL_LIMIT
        };
        // Phase-B fast-path state: once the monolithic combined query has burned
        // its call cap into an Unknown for this pool — or the pool is too wide to
        // bother — route every subsequent round straight to the per-candidate
        // sweep, which is fast and definitive. The combined query only ever
        // batch-drops what the sweep drops, so this preserves the fixpoint.
        let mut combined_doomed = false;
        loop {
            rounds += 1;
            if rounds > max_rounds {
                return Err(format!(
                    "round cap {max_rounds} exceeded (pool {pool_size} -> {})",
                    pool.len()
                ));
            }
            let call_cap = budget
                .call_cap()
                .map_err(|e| format!("{e} at consecution round {rounds}"))?;

            // Fast-path: skip the doomed combined query and full-drain the sweep.
            if phaseb_fast && (combined_doomed || pool.len() > combined_pool_limit) {
                if houdini_debug() {
                    safe_eprintln!(
                        "houdini: round {rounds} fast-path sweep (pool {}, combined_doomed={combined_doomed})",
                        pool.len()
                    );
                }
                if self.houdini_consecution_sweep(
                    &mut trans_ctx,
                    &mut pool,
                    &seed_literal,
                    state_vars,
                    &budget,
                    rounds,
                )? {
                    break;
                }
                continue;
            }

            let delta = ChcExpr::and(
                ChcExpr::and_all(pool.iter().map(|c| c.expr.clone())),
                ChcExpr::not(ChcExpr::and_all(pool.iter().map(|c| c.primed.clone()))),
            );
            match trans_ctx.check_query(&delta, &empty_model, call_cap) {
                SmtResult::Sat(model) => {
                    let post_view = post_state_view(&model, state_vars);
                    if houdini_debug() {
                        safe_eprintln!(
                            "houdini: round {rounds} consecution SAT, pool {}, post view {} of {} vars",
                            pool.len(),
                            post_view.len(),
                            state_vars.len()
                        );
                    }
                    let before = pool.len();
                    pool.retain(|cand| cand.holds_in(&post_view));
                    if !contains_flag(&pool, &seed_literal) {
                        if houdini_debug() {
                            safe_eprintln!("houdini: FLAG DROPPED; survivors: {pool:?}");
                        }
                        return Err(format!(
                            "flag literal violated by consecution model at round {rounds}"
                        ));
                    }
                    if pool.len() == before {
                        // Model claims ¬∧pool' but nothing evaluated false:
                        // cannot make progress; fail closed.
                        return Err(format!(
                            "consecution model produced no drops at round {rounds}"
                        ));
                    }
                }
                res if res.is_unsat() => break, // greatest inductive subset reached
                _ => {
                    // Combined query Unknown: per-candidate sweep. UNSAT for
                    // every candidate proves the fixpoint; SAT or Unknown
                    // drops and reruns (antecedent weakened). In fast mode mark
                    // the combined query doomed so later rounds skip it (it just
                    // burned the call cap and will keep doing so on this pool).
                    combined_doomed = true;
                    if self.houdini_consecution_sweep(
                        &mut trans_ctx,
                        &mut pool,
                        &seed_literal,
                        state_vars,
                        &budget,
                        rounds,
                    )? {
                        break;
                    }
                }
            }
        }
        if houdini_debug() {
            safe_eprintln!(
                "houdini: fixpoint with {} of {pool_size} candidates after {rounds} rounds ({:.2}s)",
                pool.len(),
                route_start.elapsed().as_secs_f64()
            );
        }

        // Fixpoint reached with the flag surviving: build the invariant model
        // over fresh per-predicate vars and validate it against EVERY original
        // clause (the soundness boundary; the loop above is only a heuristic).
        let model_vars: Vec<ChcVar> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("__hd{}_a{i}", pred_id.index()), sort.clone()))
            .collect();
        let to_model_vars: Vec<(ChcVar, ChcExpr)> = state_vars
            .iter()
            .zip(model_vars.iter())
            .map(|(sv, mv)| (sv.clone(), ChcExpr::var(mv.clone())))
            .collect();
        let formula = ChcExpr::and_all(pool.iter().map(|c| c.expr.substitute(&to_model_vars)));
        let mut model = InvariantModel::new();
        model.set(pred_id, PredicateInterpretation::new(model_vars, formula));

        let per_clause_cap =
            (route_budget / 3).clamp(Duration::from_secs(3), Duration::from_secs(20));
        for (idx, clause) in self.problem.clauses().iter().enumerate() {
            let remaining = route_budget
                .checked_sub(route_start.elapsed())
                .ok_or_else(|| format!("validation budget exhausted before clause {idx}"))?;
            let per_clause = remaining.min(per_clause_cap);
            if per_clause < Duration::from_millis(25) {
                return Err(format!("validation budget exhausted before clause {idx}"));
            }
            let violation = self
                .cruise_phase_clause_violation_query(&model, clause)
                .ok_or_else(|| format!("could not instantiate clause {idx} under survivors"))?;
            match violation.simplify_constants() {
                ChcExpr::Bool(false) => continue,
                ChcExpr::Bool(true) => {
                    return Err(format!("clause {idx} violation simplified to true"));
                }
                violation => {
                    // Equality propagation is equisatisfiable (pinned vars
                    // become unconstrained) and resolves the disjunctive
                    // case splits that stall the executor on lustre inits.
                    // Equality propagation can collapse the violation to a
                    // constant (e.g. init `A=1 ∧ B=0` propagated into the bound
                    // candidates makes `¬invariant` reduce to false). Re-check
                    // constants here: `ay_says_unsat` mishandles a literal
                    // `Bool(false)` input (returns false), so a trivially-unsat
                    // violation must be recognised directly (#9078).
                    let violation = violation.into_propagate_equalities().simplify_constants();
                    if matches!(violation, ChcExpr::Bool(false)) {
                        continue;
                    }
                    if matches!(violation, ChcExpr::Bool(true)) {
                        return Err(format!("clause {idx} violation simplified to true"));
                    }
                    // Inc-21: forward the sessions' learned dv preference so
                    // the validation backend puts the pass-OFF attempt first
                    // when the houdini queries themselves needed dv-off
                    // (car_all: the clause-1 violation is z3-trivially UNSAT,
                    // dv-off proves it in ~2s, dv-on is unknown at 30s).
                    let dv_off_first = init_ctx.dv_off_preferred() || trans_ctx.dv_off_preferred();
                    if !ay_says_unsat_with_dv_hint(&violation, per_clause, dv_off_first) {
                        return Err(format!(
                            "clause {idx} violation not proven unsat (sat or unknown)"
                        ));
                    }
                }
            }
        }

        Ok((model, pool.len(), rounds))
    }

    /// Disjunctive (2-phase) invariant synthesis via NESTED conjunctive Houdini
    /// (#disjunctive-houdini). For a transition ITE guard `S`, finds conjunctions
    /// `A` (phase S) and `B` (phase ¬S) with `Inv = (S→A) ∧ (¬S→B)` an inductive
    /// invariant excluding bad. Every consecution query is CONJUNCTIVE (S/¬S
    /// asserted as background, never as disjunctive pool candidates), so queries
    /// stay fast — the key difference from the ruled-out guarded-pool enrichment.
    /// Soundness: the final `Inv` is validated against every ORIGINAL clause.
    fn try_disjunctive_phase_houdini(
        &self,
        pred_id: PredicateId,
        route_start: Instant,
        route_budget: Duration,
    ) -> Result<(InvariantModel, usize, usize), String> {
        let ts = TransitionSystem::from_chc_problem(&self.problem)
            .map_err(|e| format!("transition system extraction failed: {e}"))?;
        let pred = self
            .problem
            .get_predicate(pred_id)
            .ok_or_else(|| "predicate lookup failed".to_string())?;
        let arity = pred.arity();
        if ts.state_vars().len() < arity {
            return Err("state vars shorter than predicate arity".to_string());
        }
        let state_vars = &ts.state_vars()[..arity];

        let next_names: Vec<String> = state_vars
            .iter()
            .map(|v| format!("{}_next", v.name))
            .collect();
        let allowed: DetHashSet<&str> = state_vars
            .iter()
            .map(|v| v.name.as_str())
            .chain(next_names.iter().map(String::as_str))
            .collect();
        let init_inlined = inline_local_definitions(&ts.init, &allowed);
        let trans_inlined = inline_local_definitions(&ts.transition, &allowed);
        let query_inlined = inline_local_definitions(&ts.query, &allowed);

        let next_subst: Vec<(ChcVar, ChcExpr)> = state_vars
            .iter()
            .map(|v| {
                (
                    v.clone(),
                    ChcExpr::var(ChcVar::new(format!("{}_next", v.name), v.sort.clone())),
                )
            })
            .collect();

        let mut guards: Vec<ChcExpr> = Vec::new();
        let mut gseen: DetHashSet<ChcExpr> = DetHashSet::default();
        mine_ite_guards(&trans_inlined, &mut guards, &mut gseen);
        let sv_names: DetHashSet<&str> = state_vars.iter().map(|v| v.name.as_str()).collect();
        guards.retain(|g| expr_vars_within(g, &sv_names));
        guards.truncate(HOUDINI_MAX_SPLITTERS);
        // Inc-16 S3c: init-cube splitter for WIDE predicates — the
        // metros/MESI/MOESI witness `flag ∧ (init-cube ∨ C)` is exactly the
        // 2-phase invariant `(S→A) ∧ (¬S→B)` with `S` = the init cube
        // (`A` ⊇ init-implied atoms, `B` = the conjunct set `C`). Prepended
        // so the wide route tries the witness shape first; the aeval
        // small-arity guard list is unchanged. Kill switch shares
        // `AY_HOUDINI_STAGE5`.
        // Fix #3 QUAL-MIX (b): count BV data args toward wideness too —
        // the pure-BV vmt predicates (pc_sfifo/mem_slave: 4 Bool + 35 BV32
        // args) have ZERO Int vars, so the Int-only count could never let
        // the init-cube splitter fire there and the disjunctive fallback
        // always died with "no phase splitters mined". Kill switch shared
        // with the mixed-CNF pool class (`--chc-no-qual-mixed`
        // restores the Int-only count).
        let wide_arity = state_vars
            .iter()
            .filter(|v| {
                v.sort == ChcSort::Int
                    || (qual_mixed_enabled() && matches!(v.sort, ChcSort::BitVec(_)))
            })
            .count()
            > HOUDINI_SMALL_ARITY;
        if stage5_widening_enabled() && wide_arity {
            let cube: Vec<ChcExpr> = init_inlined
                .conjuncts()
                .into_iter()
                .filter(|c| expr_vars_within(c, &sv_names))
                .take(STAGE5_MAX_INIT_CUBE)
                .cloned()
                .collect();
            if !cube.is_empty() {
                let cube_expr = ChcExpr::and_all(cube);
                if gseen.insert(cube_expr.clone()) {
                    guards.insert(0, cube_expr);
                }
            }
        }
        if guards.is_empty() {
            return Err("no phase splitters mined from transition guards".to_string());
        }

        let budget = HoudiniBudget {
            route_start,
            route_budget,
        };
        let base =
            build_phase_candidate_pool(state_vars, &init_inlined, &trans_inlined, &query_inlined);
        if houdini_debug() {
            safe_eprintln!(
                "disjunctive: {} guards, base pool {}, guards={:?}",
                guards.len(),
                base.len(),
                guards
            );
        }

        let empty_model = FxHashMap::default();
        let make_cands = |atoms: &[ChcExpr]| -> Vec<HoudiniCandidate> {
            atoms
                .iter()
                .map(|e| HoudiniCandidate {
                    primed: e.substitute(&next_subst),
                    expr: e.clone(),
                    init_verified: false,
                })
                .collect::<Vec<_>>()
        };

        for splitter in &guards {
            let s = splitter.clone();
            let ns = ChcExpr::not(s.clone());
            let s_prime = s.substitute(&next_subst);
            let ns_prime = ChcExpr::not(s_prime.clone());

            // Init filter: A keeps `a` with `(init∧S) ⇒ a`; B with `(init∧¬S) ⇒ b`.
            let init_s = propagate_background(&ChcExpr::and(init_inlined.clone(), s.clone()));
            let init_ns = propagate_background(&ChcExpr::and(init_inlined.clone(), ns.clone()));
            let mut a = match houdini_phase_init_filter(&make_cands(&base), &init_s, &budget) {
                Ok(v) => v,
                Err(_) => continue,
            };
            let mut b = match houdini_phase_init_filter(&make_cands(&base), &init_ns, &budget) {
                Ok(v) => v,
                Err(_) => continue,
            };

            // Nested consecution fixpoint — all queries conjunctive.
            let trans_bg = propagate_background(&trans_inlined);
            let mut tctx = PersistentExecutorSmtContext::new();
            let cap = match budget.call_cap() {
                Ok(c) => c,
                Err(_) => continue,
            };
            if !tctx.ensure_background(&trans_bg, cap) {
                continue;
            }
            let max_rounds = base.len() * 2 + HOUDINI_ROUNDS_SLACK;
            let mut rounds = 0usize;
            let mut stalled = false;
            loop {
                rounds += 1;
                if rounds > max_rounds {
                    stalled = true;
                    break;
                }
                let mut dropped = false;
                let mut sat_no_drop = false;
                let mut saw_unknown = false;
                // Drop from `$target` (post-phase `$post_phase`) every candidate
                // violated by a model of `$pre_phase ∧ (∧$pre) ∧ $post_phase ∧
                // ¬(∧$target')`. All operands are CONJUNCTIVE; the pre/post
                // conjunctions are materialized as owned exprs before the
                // in-place `retain`, so there is no aliasing borrow.
                macro_rules! phase_drop {
                    ($tag:expr, $target:expr, $pre_phase:expr, $pre:expr, $post_phase:expr) => {{
                        if !$target.is_empty() {
                            let pre_conj = ChcExpr::and_all($pre.iter().map(|c| c.expr.clone()));
                            let post_neg = ChcExpr::not(ChcExpr::and_all(
                                $target.iter().map(|c| c.primed.clone()),
                            ));
                            let delta = ChcExpr::and_all([
                                $pre_phase.clone(),
                                pre_conj.clone(),
                                $post_phase.clone(),
                                post_neg,
                            ]);
                            match budget.call_cap() {
                                Ok(cap) => {
                                    let res = tctx.check_query(&delta, &empty_model, cap);
                                    if let SmtResult::Sat(model) = res {
                                        let post_view = post_state_view(&model, state_vars);
                                        let before = $target.len();
                                        $target.retain(|c| c.holds_in(&post_view));
                                        if houdini_debug() && rounds <= 2 {
                                            safe_eprintln!(
                                                "  [{}] SAT drop {}->{} postview={:?}",
                                                $tag,
                                                before,
                                                $target.len(),
                                                post_view
                                            );
                                        }
                                        if $target.len() < before {
                                            dropped = true;
                                        } else {
                                            sat_no_drop = true;
                                        }
                                    } else if !res.is_unsat() {
                                        // Unknown combined query (the wide ¬(∧target')
                                        // disjunction can defeat the executor): resolve
                                        // with a per-candidate sweep — each
                                        // `… ∧ ¬c'` is small and decidable.
                                        let mut keep = Vec::with_capacity($target.len());
                                        for c in std::mem::take(&mut $target) {
                                            let q = ChcExpr::and_all([
                                                $pre_phase.clone(),
                                                pre_conj.clone(),
                                                $post_phase.clone(),
                                                ChcExpr::not(c.primed.clone()),
                                            ]);
                                            match budget.call_cap() {
                                                Ok(cap2) => {
                                                    let r =
                                                        tctx.check_query(&q, &empty_model, cap2);
                                                    if r.is_unsat() {
                                                        keep.push(c);
                                                    } else if r.is_sat() {
                                                        dropped = true;
                                                    } else {
                                                        saw_unknown = true;
                                                        keep.push(c);
                                                    }
                                                }
                                                Err(_) => {
                                                    stalled = true;
                                                    keep.push(c);
                                                }
                                            }
                                        }
                                        $target = keep;
                                    }
                                }
                                Err(_) => stalled = true,
                            }
                        }
                    }};
                }
                // A-update: post in S', from phase S (pre A) or ¬S (pre B).
                phase_drop!("A<-S", a, s, a, s_prime);
                phase_drop!("A<-nS", a, ns, b, s_prime);
                // B-update: post in ¬S', from phase S (pre A) or ¬S (pre B).
                phase_drop!("B<-nS", b, ns, b, ns_prime);
                phase_drop!("B<-S", b, s, a, ns_prime);
                if stalled {
                    break;
                }
                if !dropped {
                    if sat_no_drop || saw_unknown {
                        // A violating (sat-no-drop) or undecided (unknown) query
                        // remained: NOT a true fixpoint, so the resulting Inv is
                        // not provably inductive. Mark stalled rather than emit a
                        // spurious candidate (the original-clause validation would
                        // reject it anyway, but this avoids wasting that budget).
                        if houdini_debug() {
                            safe_eprintln!(
                                "disjunctive: non-fixpoint break (sat_no_drop={sat_no_drop} unknown={saw_unknown})"
                            );
                        }
                        stalled = true;
                    }
                    break; // mutual fixpoint reached
                }
            }
            if houdini_debug() {
                safe_eprintln!(
                    "disjunctive splitter {:?}: |A|={} |B|={} after {rounds} rounds (stalled={stalled})",
                    splitter,
                    a.len(),
                    b.len()
                );
                let has = |set: &[HoudiniCandidate], needle: &str| {
                    set.iter().any(|c| format!("{:?}", c.expr).contains(needle))
                };
                safe_eprintln!(
                    "  A: has(Mul)={} ; B: has(diff-le)={} (Mul atoms in A = bad-excluders)",
                    has(&a, "Mul"),
                    has(&b, "Mul")
                );
                for c in a.iter().filter(|c| format!("{:?}", c.expr).contains("Mul")) {
                    safe_eprintln!("    A-Mul-atom {:?}", c.expr);
                }
            }
            if stalled {
                continue;
            }

            // Minimize each phase conjunction to a minimal subset (drop atoms
            // implied by the rest WITHIN that phase). `phase ∧ A_min ≡ phase ∧ A`,
            // so Inv is unchanged in meaning (still inductive + bad-excluding) but
            // far smaller — which is what makes the monolithic original-clause
            // validation query decidable for the executor.
            let a = minimize_phase_conj(a, &s, &budget);
            let b = minimize_phase_conj(b, &ns, &budget);
            if houdini_debug() {
                safe_eprintln!(
                    "disjunctive splitter {:?}: minimized to |A|={} |B|={}",
                    splitter,
                    a.len(),
                    b.len()
                );
            }

            // Build Inv = (S→∧A) ∧ (¬S→∧B) over fresh per-predicate model vars,
            // then validate against EVERY original clause (the soundness gate).
            let model_vars: Vec<ChcVar> = state_vars
                .iter()
                .enumerate()
                .map(|(i, sv)| {
                    ChcVar::new(format!("__hdphz{}_a{i}", pred_id.index()), sv.sort.clone())
                })
                .collect();
            let to_model: Vec<(ChcVar, ChcExpr)> = state_vars
                .iter()
                .zip(model_vars.iter())
                .map(|(sv, mv)| (sv.clone(), ChcExpr::var(mv.clone())))
                .collect();
            let s_m = s.substitute(&to_model);
            let a_conj = ChcExpr::and_all(a.iter().map(|c| c.expr.substitute(&to_model)));
            let b_conj = ChcExpr::and_all(b.iter().map(|c| c.expr.substitute(&to_model)));
            let inv = ChcExpr::and(
                ChcExpr::or(ChcExpr::not(s_m.clone()), a_conj),
                ChcExpr::or(s_m, b_conj),
            );
            let mut model = InvariantModel::new();
            model.set(pred_id, PredicateInterpretation::new(model_vars, inv));

            let validated =
                self.validate_invariant_against_clauses(&model, route_start, route_budget);
            if houdini_debug() {
                safe_eprintln!("disjunctive splitter {:?}: validated={validated}", splitter);
            }
            if validated {
                return Ok((model, a.len() + b.len(), rounds));
            }
        }
        Err("no phase split produced a validated invariant".to_string())
    }

    /// Validate a candidate `InvariantModel` against EVERY original clause via
    /// the per-clause violation query (the same soundness gate `houdini_run`
    /// uses). Returns true only if every clause's violation is proven UNSAT.
    fn validate_invariant_against_clauses(
        &self,
        model: &InvariantModel,
        route_start: Instant,
        route_budget: Duration,
    ) -> bool {
        let per_clause_cap =
            (route_budget / 3).clamp(Duration::from_secs(3), Duration::from_secs(20));
        for (idx, clause) in self.problem.clauses().iter().enumerate() {
            let remaining = match route_budget.checked_sub(route_start.elapsed()) {
                Some(r) => r,
                None => return false,
            };
            let per_clause = remaining.min(per_clause_cap);
            if per_clause < Duration::from_millis(25) {
                return false;
            }
            let violation = match self.cruise_phase_clause_violation_query(model, clause) {
                Some(v) => v,
                None => {
                    if houdini_debug() {
                        safe_eprintln!("disjunctive validate: clause {idx} could not instantiate");
                    }
                    return false;
                }
            };
            match violation.simplify_constants() {
                ChcExpr::Bool(false) => continue,
                ChcExpr::Bool(true) => {
                    if houdini_debug() {
                        safe_eprintln!("disjunctive validate: clause {idx} simplified to true");
                    }
                    return false;
                }
                violation => {
                    let violation = violation.into_propagate_equalities().simplify_constants();
                    if matches!(violation, ChcExpr::Bool(false)) {
                        continue;
                    }
                    if matches!(violation, ChcExpr::Bool(true)) {
                        if houdini_debug() {
                            safe_eprintln!("disjunctive validate: clause {idx} (propagated) true");
                        }
                        return false;
                    }
                    if !ay_says_unsat(&violation, per_clause) {
                        if houdini_debug() {
                            let mut dctx = PersistentExecutorSmtContext::new();
                            let _ = dctx
                                .ensure_background(&ChcExpr::Bool(true), Duration::from_secs(1));
                            if let SmtResult::Sat(m) = dctx.check_query(
                                &violation,
                                &FxHashMap::default(),
                                Duration::from_secs(3),
                            ) {
                                safe_eprintln!(
                                    "disjunctive validate: clause {idx} NOT unsat; CEX={m:?}"
                                );
                            } else {
                                safe_eprintln!(
                                    "disjunctive validate: clause {idx} NOT unsat (no model)"
                                );
                            }
                        }
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Per-candidate consecution sweep (fallback when the combined query is
    /// Unknown). Checks `∧pool ∧ trans ∧ ¬cand'` for each candidate:
    /// UNSAT for ALL of them proves the fixpoint (returns `Ok(true)`); a SAT
    /// model or an Unknown drops the candidate (plus batch drops from the
    /// model's post-state) and returns `Ok(false)` so the caller restarts
    /// with the weakened antecedent. An Unknown on the FLAG itself is
    /// skipped (other drops may make its consecution provable later); the
    /// sweep only fails when a full pass neither drops nor proves the flag.
    ///
    /// With the Phase-B fast-path on (default), the sweep FULL-DRAINS: it makes
    /// ONE full pass over the pool, collecting EVERY non-inductive candidate
    /// (query SAT/Unknown, plus any candidate violated in a SAT post-state
    /// model), drops them all together, and returns `Ok(false)` — instead of
    /// returning on the first drop. This is sound by Houdini monotonicity: each
    /// query uses the FULL pool as antecedent, so a candidate found non-inductive
    /// here is non-inductive w.r.t. every subset reached later (dropping only
    /// weakens the antecedent). The greatest inductive subset is unchanged; only
    /// the number of expensive re-passes shrinks (N → ~1 per stratum).
    fn houdini_consecution_sweep(
        &self,
        trans_ctx: &mut PersistentExecutorSmtContext,
        pool: &mut Vec<HoudiniCandidate>,
        seed_literal: &ChcExpr,
        state_vars: &[ChcVar],
        budget: &HoudiniBudget,
        round: usize,
    ) -> Result<bool, String> {
        if houdini_phaseb_fast_enabled() {
            return self.houdini_consecution_sweep_full_drain(
                trans_ctx,
                pool,
                seed_literal,
                state_vars,
                budget,
                round,
            );
        }
        let empty_model = FxHashMap::default();
        let antecedent = ChcExpr::and_all(pool.iter().map(|c| c.expr.clone()));
        let mut flag_unknown = false;
        for idx in 0..pool.len() {
            let call_cap = budget
                .call_cap()
                .map_err(|e| format!("{e} during consecution sweep at round {round}"))?;
            let delta = ChcExpr::and(antecedent.clone(), ChcExpr::not(pool[idx].primed.clone()));
            match trans_ctx.check_query(&delta, &empty_model, call_cap) {
                res if res.is_unsat() => continue,
                SmtResult::Sat(model) => {
                    let checked = pool[idx].expr.clone();
                    let post_view = post_state_view(&model, state_vars);
                    pool.retain(|cand| cand.expr != checked && cand.holds_in(&post_view));
                    if !contains_flag(pool, seed_literal) {
                        return Err(format!(
                            "flag literal violated in consecution sweep at round {round}"
                        ));
                    }
                    return Ok(false);
                }
                _ => {
                    if pool[idx].expr == *seed_literal {
                        flag_unknown = true;
                        continue;
                    }
                    // Unknown: conservatively drop the candidate under test.
                    pool.remove(idx);
                    return Ok(false);
                }
            }
        }
        if flag_unknown {
            return Err(format!(
                "consecution sweep unknown on the flag literal at round {round}"
            ));
        }
        Ok(true)
    }

    /// Full-drain variant of [`Self::houdini_consecution_sweep`] used by the
    /// Phase-B fast-path. ONE pass over the pool collects every non-inductive
    /// candidate against the FIXED full antecedent `∧pool` and drops them all
    /// together, rather than returning on the first drop. Returns `Ok(true)`
    /// (fixpoint) when no candidate is droppable, `Ok(false)` when at least one
    /// was dropped (caller re-passes with the weakened pool).
    ///
    /// Soundness / fixpoint preservation: every per-candidate query uses the
    /// same full `∧pool` as antecedent. A candidate found non-inductive here
    /// (its `∧pool ∧ ¬cand'` is SAT/Unknown) is therefore non-inductive w.r.t.
    /// any subset reached on later passes (a weaker antecedent can only make
    /// `¬cand'` MORE satisfiable). Hence no candidate is ever dropped that would
    /// belong to the greatest inductive subset, and — because the GIS is unique
    /// and independent of drop order — the converged pool equals the baseline's.
    /// The flag literal is never query-dropped (UNSAT keeps it; a SAT/Unknown on
    /// the flag is handled exactly as the baseline: flag-SAT or all-else-passed
    /// flag-Unknown is a genuine consecution failure).
    fn houdini_consecution_sweep_full_drain(
        &self,
        trans_ctx: &mut PersistentExecutorSmtContext,
        pool: &mut Vec<HoudiniCandidate>,
        seed_literal: &ChcExpr,
        state_vars: &[ChcVar],
        budget: &HoudiniBudget,
        round: usize,
    ) -> Result<bool, String> {
        let empty_model = FxHashMap::default();
        // Fixed antecedent for the whole pass: the pool as it stands now.
        let antecedent = ChcExpr::and_all(pool.iter().map(|c| c.expr.clone()));
        // Expressions to drop after the pass (set-membership over canonical
        // ChcExpr). Includes the directly-non-inductive candidate AND, for SAT
        // results, every candidate the post-state model violates (a free batch
        // drop, all witnessed sound by that model). The flag is never inserted.
        let mut drop_set: DetHashSet<ChcExpr> = DetHashSet::default();
        let mut flag_unknown = false;
        for idx in 0..pool.len() {
            let cand_expr = pool[idx].expr.clone();
            // Already condemned via a prior candidate's post-state model: no need
            // to spend a solver call re-confirming it.
            if drop_set.contains(&cand_expr) {
                continue;
            }
            let call_cap = budget
                .call_cap()
                .map_err(|e| format!("{e} during consecution sweep at round {round}"))?;
            let delta = ChcExpr::and(antecedent.clone(), ChcExpr::not(pool[idx].primed.clone()));
            match trans_ctx.check_query(&delta, &empty_model, call_cap) {
                res if res.is_unsat() => continue,
                SmtResult::Sat(model) => {
                    if cand_expr == *seed_literal {
                        // Flag genuinely fails consecution against the full pool:
                        // parity with the baseline (which drops it then errors on
                        // the missing-flag check).
                        return Err(format!(
                            "flag literal violated in consecution sweep at round {round}"
                        ));
                    }
                    let post_view = post_state_view(&model, state_vars);
                    // Condemn the checked candidate plus every (non-flag)
                    // candidate the model's post-state violates.
                    drop_set.insert(cand_expr);
                    for cand in pool.iter() {
                        if cand.expr != *seed_literal && !cand.holds_in(&post_view) {
                            drop_set.insert(cand.expr.clone());
                        }
                    }
                }
                _ => {
                    if cand_expr == *seed_literal {
                        flag_unknown = true;
                        continue;
                    }
                    // Unknown: conservatively condemn the candidate under test.
                    drop_set.insert(cand_expr);
                }
            }
        }
        if drop_set.is_empty() {
            if flag_unknown {
                return Err(format!(
                    "consecution sweep unknown on the flag literal at round {round}"
                ));
            }
            return Ok(true);
        }
        pool.retain(|cand| !drop_set.contains(&cand.expr));
        if !contains_flag(pool, seed_literal) {
            return Err(format!(
                "flag literal violated in consecution sweep at round {round}"
            ));
        }
        Ok(false)
    }
}

/// A Houdini candidate: the unprimed atom, its primed (post-state) version,
/// and whether `init ⇒ cand` has been proven.
#[derive(Debug, Clone)]
struct HoudiniCandidate {
    expr: ChcExpr,
    primed: ChcExpr,
    init_verified: bool,
}

impl HoudiniCandidate {
    /// Evaluate the candidate under the model. `false` for violated AND for
    /// indeterminate values (missing/opaque): never keep a candidate that
    /// could not be verified — dropping only weakens the conjunction.
    fn holds_in(&self, model: &FxHashMap<String, SmtValue>) -> bool {
        matches!(evaluate_expr(&self.expr, model), Some(SmtValue::Bool(true)))
    }
}

/// Route budget tracking for the Houdini loop.
struct HoudiniBudget {
    route_start: Instant,
    route_budget: Duration,
}

impl HoudiniBudget {
    /// Per-call cap: remaining/4 bounded by [500ms, 5s] so late calls don't
    /// starve into avoidable Unknowns, while never overshooting the remaining
    /// route budget (minus a small reserve). Errors when exhausted.
    fn call_cap(&self) -> Result<Duration, String> {
        let remaining = self.remaining()?;
        Self::finish_cap(
            (remaining / 4)
                .max(Duration::from_millis(500))
                .min(HOUDINI_PER_CALL_CAP),
            remaining,
        )
    }

    /// Full per-call cap (no /4 slice) for make-or-break checks.
    fn call_cap_generous(&self) -> Result<Duration, String> {
        let remaining = self.remaining()?;
        Self::finish_cap(HOUDINI_PER_CALL_CAP, remaining)
    }

    fn remaining(&self) -> Result<Duration, String> {
        self.route_budget
            .checked_sub(self.route_start.elapsed())
            .ok_or_else(|| "route budget exhausted".to_string())
    }

    fn finish_cap(cap: Duration, remaining: Duration) -> Result<Duration, String> {
        let cap = cap.min(remaining.saturating_sub(Duration::from_millis(100)));
        if cap < Duration::from_millis(25) {
            return Err("route budget exhausted".to_string());
        }
        Ok(cap)
    }
}

/// Whether the flag literal is still in the pool.
fn contains_flag(pool: &[HoudiniCandidate], seed_literal: &ChcExpr) -> bool {
    pool.iter().any(|c| c.expr == *seed_literal)
}

/// Build the initial candidate pool over the canonical state vars.
///
/// Ordering matters for the pool cap: the flag literal first, then Bool
/// literals, then Int/constant atoms, then Int pair orderings.
/// Whether the disjunctive (2-phase) synthesis fallback is enabled. DEFAULT ON
/// (`AY_HOUDINI_DISJUNCTIVE=0` to disable). The nested `try_disjunctive_phase_houdini`
/// runs only when the conjunctive Houdini prepass fails on a single-predicate
/// small-arity problem whose transition has `ite()` guards, and bails fast
/// otherwise. Validated: +3 sound solves on the aeval multi-phase family @90s
/// (11→14), ZERO wrong, ZERO regression; oracle flag-on ≡ flag-off (45/15,
/// FLIPS=0); ay-chc suite green. Soundness is by construction — every candidate
/// invariant is validated against the original clauses.
fn disjunctive_enrichment_enabled() -> bool {
    // B27: CLI-owned; env retired.
    crate::ab_switches::get().houdini_disjunctive
}

/// Whether the Bool-arg ↔ Int-bound guarded-implication candidate class is
/// enabled (`AY_CHC_GUARDED_IMPL_HINTS`). DEFAULT ON; only the literal "0"
/// disables. These rows correlate a Bool control bit `b` with a counter bound
/// (`b ⟹ v⋈c`, `v⋈c ⟹ b`) — the missing lustre/VMT invariant shape (e.g.
/// two_counters: `a2 ⟹ a0≥1`, `a0≥3 ⟹ a1`). Sound by construction: every
/// candidate flows through the same model-based dropping + final
/// `validate_invariant_against_clauses` as all other Houdini candidates, so a
/// non-inductive row is simply discarded and can never produce a wrong `sat`.
fn guarded_impl_hints_enabled() -> bool {
    // B15: typed A/B switch (`ab_switches`); the never-set env read is gone.
    crate::ab_switches::get().guarded_impl_hints
}

/// Whether the inc-16 Stage-5 widening classes are enabled. DEFAULT ON;
/// `AY_HOUDINI_STAGE5=0` restores the pre-inc-16 pools byte-for-byte.
fn stage5_widening_enabled() -> bool {
    // B27: CLI-owned; env retired.
    crate::ab_switches::get().houdini_stage5
}

/// Int state-var pairs co-occurring in a `+`/`-` linear subterm of the
/// transition (inc-16 S3a). `_next` occurrences map back to the unprimed
/// state var, so `h_next = h - f` yields the (h, f) pair. Deduped (unordered)
/// and capped at [`STAGE5_MAX_PAIRS`]; pairs are returned in transition
/// traversal order (earlier terms first).
fn mine_cooccurring_int_pairs(
    transition: &ChcExpr,
    state_vars: &[ChcVar],
) -> Vec<(ChcVar, ChcVar)> {
    let mut index: FxHashMap<String, usize> = FxHashMap::default();
    for (i, v) in state_vars.iter().enumerate() {
        if v.sort == ChcSort::Int {
            index.insert(v.name.clone(), i);
            index.insert(format!("{}_next", v.name), i);
        }
    }
    let mut seen_pairs: DetHashSet<(usize, usize)> = DetHashSet::default();
    let mut pairs: Vec<(ChcVar, ChcVar)> = Vec::new();
    let mut stack: Vec<&ChcExpr> = vec![transition];
    while let Some(expr) = stack.pop() {
        if pairs.len() >= STAGE5_MAX_PAIRS {
            break;
        }
        match expr {
            ChcExpr::Op(op, args) => {
                if matches!(op, ChcOp::Add | ChcOp::Sub) {
                    let mut vars_in: Vec<usize> = Vec::new();
                    collect_linear_term_vars(expr, &index, &mut vars_in);
                    // 2..=4 distinct vars: difference/sum beacons (metros
                    // `h - f`) up to 4-var monitor sums (SYNAPSE `q+p-o-n`).
                    if (2..=4).contains(&vars_in.len()) {
                        for a in 0..vars_in.len() {
                            for b in (a + 1)..vars_in.len() {
                                let (lo, hi) = if vars_in[a] < vars_in[b] {
                                    (vars_in[a], vars_in[b])
                                } else {
                                    (vars_in[b], vars_in[a])
                                };
                                if seen_pairs.insert((lo, hi)) {
                                    pairs.push((state_vars[lo].clone(), state_vars[hi].clone()));
                                }
                            }
                        }
                    }
                }
                stack.extend(args.iter().map(|a| a.as_ref()));
            }
            ChcExpr::FuncApp(_, _, args) | ChcExpr::PredicateApp(_, _, args) => {
                stack.extend(args.iter().map(|a| a.as_ref()));
            }
            _ => {}
        }
    }
    pairs
}

/// Distinct Int state-var indices (via `index`) inside a linear subterm.
/// Walks only `+`/`-`/negation/scaling nodes; anything else (ite, bool ops)
/// ends the branch — those substructures are traversed separately by the
/// caller. Stops past 5 vars (the caller only uses 2..=4-var terms).
fn collect_linear_term_vars(
    expr: &ChcExpr,
    index: &FxHashMap<String, usize>,
    out: &mut Vec<usize>,
) {
    if out.len() > 4 {
        return;
    }
    match expr {
        ChcExpr::Var(v) => {
            if let Some(&i) = index.get(&v.name) {
                if !out.contains(&i) {
                    out.push(i);
                }
            }
        }
        ChcExpr::Op(op, args)
            if matches!(op, ChcOp::Add | ChcOp::Sub | ChcOp::Neg | ChcOp::Mul) =>
        {
            for a in args {
                collect_linear_term_vars(a, index, out);
            }
        }
        _ => {}
    }
}

/// Collect the guard conditions of `ite(cond, _, _)` subterms — candidate PHASE
/// SPLITTERS for disjunctive (2-phase) invariant synthesis (#disjunctive-houdini).
/// Multi-phase aeval transitions case-split on exactly these guards.
fn mine_ite_guards(expr: &ChcExpr, out: &mut Vec<ChcExpr>, seen: &mut DetHashSet<ChcExpr>) {
    match expr {
        ChcExpr::Op(op, args) => {
            if *op == ChcOp::Ite && args.len() == 3 {
                let cond = (*args[0]).clone();
                if seen.insert(cond.clone()) {
                    out.push(cond);
                }
            }
            for a in args {
                mine_ite_guards(a, out, seen);
            }
        }
        ChcExpr::FuncApp(_, _, args) | ChcExpr::PredicateApp(_, _, args) => {
            for a in args {
                mine_ite_guards(a, out, seen);
            }
        }
        _ => {}
    }
}

/// Whether every variable in `expr` is named in `allowed` (keeps only phase
/// splitters that range over the current state vars).
fn expr_vars_within(expr: &ChcExpr, allowed: &DetHashSet<&str>) -> bool {
    match expr {
        ChcExpr::Var(v) => allowed.contains(v.name.as_str()),
        ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) | ChcExpr::PredicateApp(_, _, args) => {
            args.iter().all(|a| expr_vars_within(a, allowed))
        }
        _ => true,
    }
}

/// Conjunctive candidate atoms for the nested 2-phase synthesizer: mined atoms,
/// per-variable constant bounds, and 1- and 2-coefficient difference bounds
/// (`vi − vj`, `vi − 2·vj`). Unlike `build_candidate_pool` these are plain
/// (non-guarded) atoms, and coefficient-2 terms are always included for small
/// arity (the per-phase pool is small, so they do not bloat it).
fn build_phase_candidate_pool(
    state_vars: &[ChcVar],
    init: &ChcExpr,
    transition: &ChcExpr,
    query: &ChcExpr,
) -> Vec<ChcExpr> {
    let mut seen: DetHashSet<ChcExpr> = DetHashSet::default();
    let mut pool: Vec<ChcExpr> = Vec::new();
    let mut push = |pool: &mut Vec<ChcExpr>, cand: ChcExpr| {
        if seen.insert(cand.clone()) {
            pool.push(cand);
        }
    };
    let (atoms, terms) = mine_atom_candidates(init, transition, query, state_vars);
    for atom in atoms {
        push(&mut pool, ChcExpr::not(atom.clone()));
        push(&mut pool, atom);
    }
    let constants = harvest_int_constants(&[init, transition]);
    let int_vars: Vec<&ChcVar> = state_vars
        .iter()
        .filter(|v| v.sort == ChcSort::Int)
        .collect();
    // Inc-16 S3: on WIDE predicates the phase pool gets the co-occurring
    // ≤2-var inequality rows (placed early — most-valuable-first under the
    // tighter wide cap below); small-arity pools keep their full vi±vj rows
    // below, byte-identical.
    let stage5_wide = stage5_widening_enabled() && int_vars.len() > HOUDINI_SMALL_ARITY;
    if stage5_wide {
        let consts5: Vec<i128> = constants.iter().copied().take(STAGE5_MAX_CONSTS).collect();
        for (vi, vj) in mine_cooccurring_int_pairs(transition, state_vars) {
            let xi = ChcExpr::var(vi.clone());
            let xj = ChcExpr::var(vj.clone());
            let diff = ChcExpr::sub(xi.clone(), xj.clone());
            let sum = ChcExpr::add(xi.clone(), xj.clone());
            push(&mut pool, ChcExpr::le(xi.clone(), xj.clone()));
            push(&mut pool, ChcExpr::le(xj, xi));
            for &c in &consts5 {
                push(&mut pool, ChcExpr::le(diff.clone(), ChcExpr::int(c)));
                push(&mut pool, ChcExpr::ge(diff.clone(), ChcExpr::int(c)));
                push(&mut pool, ChcExpr::le(sum.clone(), ChcExpr::int(c)));
                push(&mut pool, ChcExpr::ge(sum.clone(), ChcExpr::int(c)));
            }
        }
    }
    for v in &int_vars {
        let x = ChcExpr::var((*v).clone());
        for &c in &constants {
            push(&mut pool, ChcExpr::le(x.clone(), ChcExpr::int(c)));
            push(&mut pool, ChcExpr::ge(x.clone(), ChcExpr::int(c)));
        }
    }
    for term in &terms {
        for &c in &constants {
            push(&mut pool, ChcExpr::le(term.clone(), ChcExpr::int(c)));
            push(&mut pool, ChcExpr::ge(term.clone(), ChcExpr::int(c)));
        }
    }
    if int_vars.len() <= HOUDINI_SMALL_ARITY {
        for (i, vi) in int_vars.iter().enumerate() {
            for (j, vj) in int_vars.iter().enumerate() {
                if i == j {
                    continue;
                }
                let xi = ChcExpr::var((*vi).clone());
                let xj = ChcExpr::var((*vj).clone());
                let diff = ChcExpr::sub(xi.clone(), xj.clone());
                let coef2 = ChcExpr::sub(xi, ChcExpr::mul(ChcExpr::int(2), xj));
                for &c in &constants {
                    push(&mut pool, ChcExpr::le(diff.clone(), ChcExpr::int(c)));
                    push(&mut pool, ChcExpr::ge(diff.clone(), ChcExpr::int(c)));
                    push(&mut pool, ChcExpr::le(coef2.clone(), ChcExpr::int(c)));
                    push(&mut pool, ChcExpr::ge(coef2.clone(), ChcExpr::int(c)));
                }
            }
        }
    }
    // Wide predicates get a much tighter phase pool: the per-candidate phase
    // init filter is sequential, so a 2048-candidate pool cannot fit the
    // prepass window (inc-16 S3c). Small arity keeps the stock cap.
    pool.truncate(if stage5_wide {
        STAGE5_PHASE_POOL
    } else {
        HOUDINI_MAX_POOL
    });
    pool
}

/// Keep the candidates implied by a phase init background: `init_bg ⇒ cand`,
/// i.e. `init_bg ∧ ¬cand` UNSAT. An unsatisfiable/unsetupable `init_bg` (the
/// phase is unreachable at init) vacuously implies everything → keep all (still
/// sound: the final invariant is validated against the original clauses).
fn houdini_phase_init_filter(
    cands: &[HoudiniCandidate],
    init_bg: &ChcExpr,
    budget: &HoudiniBudget,
) -> Result<Vec<HoudiniCandidate>, String> {
    let mut ctx = PersistentExecutorSmtContext::new();
    if !ctx.ensure_background(init_bg, budget.call_cap()?) {
        return Ok(cands.to_vec());
    }
    let empty_model = FxHashMap::default();
    let mut kept = Vec::with_capacity(cands.len());
    for c in cands {
        let cap = budget.call_cap()?;
        if ctx
            .check_query(&ChcExpr::not(c.expr.clone()), &empty_model, cap)
            .is_unsat()
        {
            kept.push(c.clone());
        }
    }
    Ok(kept)
}

/// Greedily drop atoms implied by the rest of the conjunction within `phase`:
/// remove `cands[i]` when `phase ∧ (∧ cands\{i}) ⇒ cands[i]` (i.e.
/// `phase ∧ rest ∧ ¬cands[i]` is UNSAT). The result is logically equivalent to
/// the input under `phase`, so the phase-split invariant is unchanged in meaning
/// while becoming small enough for the monolithic original-clause validation to
/// decide. On any Unknown/setup failure the atom is conservatively kept.
fn minimize_phase_conj(
    cands: Vec<HoudiniCandidate>,
    phase: &ChcExpr,
    budget: &HoudiniBudget,
) -> Vec<HoudiniCandidate> {
    let cap0 = match budget.call_cap() {
        Ok(c) => c,
        Err(_) => return cands,
    };
    let mut ctx = PersistentExecutorSmtContext::new();
    if !ctx.ensure_background(phase, cap0) {
        return cands;
    }
    let empty = FxHashMap::default();
    let mut kept = cands;
    let mut i = 0;
    while i < kept.len() {
        let cap = match budget.call_cap() {
            Ok(c) => c,
            Err(_) => break,
        };
        let rest = ChcExpr::and_all(
            kept.iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, c)| c.expr.clone()),
        );
        let q = ChcExpr::and(rest, ChcExpr::not(kept[i].expr.clone()));
        if ctx.check_query(&q, &empty, cap).is_unsat() {
            kept.remove(i);
        } else {
            i += 1;
        }
    }
    kept
}

fn build_candidate_pool(
    state_vars: &[ChcVar],
    seed_literal: &ChcExpr,
    init: &ChcExpr,
    transition: &ChcExpr,
    query: &ChcExpr,
    mined_qualifiers: &[ChcExpr],
) -> Vec<HoudiniCandidate> {
    let mut seen: DetHashSet<ChcExpr> = DetHashSet::default();
    let mut pool: Vec<ChcExpr> = Vec::new();
    let mut push = |pool: &mut Vec<ChcExpr>, cand: ChcExpr| {
        if seen.insert(cand.clone()) {
            pool.push(cand);
        }
    };
    push(&mut pool, seed_literal.clone());

    // Atoms mined from the init/transition/query formulas themselves (and
    // their negations). The VMT/lustre encodings define monitor variables
    // through exactly the relations the inductive invariant needs (e.g.
    // multi-variable linear sums like `q + p - o - n ≤ 0` and Bool
    // equivalences like `x = (p ∧ q)`), which the generic bound/ordering
    // classes below cannot express.
    let (atoms, terms) = mine_atom_candidates(init, transition, query, state_vars);
    for atom in atoms {
        push(&mut pool, ChcExpr::not(atom.clone()));
        push(&mut pool, atom);
    }

    // Int/constant atoms from constants harvested in init and transition.
    // `x = c` is intentionally omitted: under Houdini's model-based dropping
    // it survives exactly when BOTH `x ≤ c` and `x ≥ c` survive (it is
    // violated by a model iff one of them is), so including it only inflates
    // the SMT queries without strengthening the final conjunction.
    let constants = harvest_int_constants(&[init, transition]);
    let int_vars: Vec<&ChcVar> = state_vars
        .iter()
        .filter(|v| v.sort == ChcSort::Int)
        .collect();

    // Inc-16 S3 (Stage-5 widening), WIDE predicates only (small-arity pools
    // already carry full vi±vj rows below and stay byte-identical). Placed
    // right after the mined atoms so the new vocabulary survives the pool
    // cap on wide predicates (var-const bound rows alone are ~2·arity·|c|).
    let stage5 = stage5_widening_enabled() && int_vars.len() > HOUDINI_SMALL_ARITY;
    if stage5 {
        let pairs = mine_cooccurring_int_pairs(transition, state_vars);
        let consts5: Vec<i128> = constants.iter().copied().take(STAGE5_MAX_CONSTS).collect();
        // (a) `vi−vj ⋈ c` / `vi+vj ⋈ c` rows for co-occurring pairs, plus
        // both orderings (`vi ≤ vj`, `vj ≤ vi` — i.e. diff against 0): the
        // generic ordering enumeration below truncates long before reaching
        // most pairs on a 44-113-arg predicate.
        for (vi, vj) in &pairs {
            let xi = ChcExpr::var(vi.clone());
            let xj = ChcExpr::var(vj.clone());
            let diff = ChcExpr::sub(xi.clone(), xj.clone());
            let sum = ChcExpr::add(xi.clone(), xj.clone());
            push(&mut pool, ChcExpr::le(xi.clone(), xj.clone()));
            push(&mut pool, ChcExpr::le(xj, xi));
            for &c in &consts5 {
                push(&mut pool, ChcExpr::le(diff.clone(), ChcExpr::int(c)));
                push(&mut pool, ChcExpr::ge(diff.clone(), ChcExpr::int(c)));
                push(&mut pool, ChcExpr::le(sum.clone(), ChcExpr::int(c)));
                push(&mut pool, ChcExpr::ge(sum.clone(), ChcExpr::int(c)));
            }
        }
        // (b) guarded rows `guard → (vi−vj ⋈ c)` from mined ITE guards over
        // state vars (both guard polarities). Tightly capped: disjunctive
        // candidates are SMT-costlier than plain atoms in the consecution
        // queries (the ruled-out aeval pool-enrichment lesson), but the
        // residual lustre invariants need exactly this guarded-inequality
        // shape (golem-imc closes them with it at k~2-4).
        let mut guards: Vec<ChcExpr> = Vec::new();
        let mut gseen: DetHashSet<ChcExpr> = DetHashSet::default();
        mine_ite_guards(transition, &mut guards, &mut gseen);
        let sv_names: DetHashSet<&str> = state_vars.iter().map(|v| v.name.as_str()).collect();
        guards.retain(|g| expr_vars_within(g, &sv_names));
        guards.truncate(STAGE5_MAX_GUARDS);
        let consts_g: Vec<i128> = constants
            .iter()
            .copied()
            .take(STAGE5_MAX_GUARD_CONSTS)
            .collect();
        for g in &guards {
            for (vi, vj) in pairs.iter().take(STAGE5_MAX_GUARD_PAIRS) {
                let diff = ChcExpr::sub(ChcExpr::var(vi.clone()), ChcExpr::var(vj.clone()));
                for &c in &consts_g {
                    for atom in [
                        ChcExpr::ge(diff.clone(), ChcExpr::int(c)),
                        ChcExpr::le(diff.clone(), ChcExpr::int(c)),
                    ] {
                        push(
                            &mut pool,
                            ChcExpr::or(ChcExpr::not(g.clone()), atom.clone()),
                        );
                        push(&mut pool, ChcExpr::or(g.clone(), atom));
                    }
                }
            }
        }
    }

    // Bool argument literals (both polarities; the wrong one drops out).
    for v in state_vars {
        if v.sort != ChcSort::Bool {
            continue;
        }
        push(&mut pool, ChcExpr::var(v.clone()));
        push(&mut pool, ChcExpr::not(ChcExpr::var(v.clone())));
    }
    for v in &int_vars {
        for &c in &constants {
            let x = ChcExpr::var((*v).clone());
            push(&mut pool, ChcExpr::le(x.clone(), ChcExpr::int(c)));
            push(&mut pool, ChcExpr::ge(x, ChcExpr::int(c)));
        }
    }

    // Bool-arg ↔ Int-bound guarded implications (AY_CHC_GUARDED_IMPL_HINTS).
    // The lustre/VMT control-bit invariants correlate a Bool argument `b` with
    // a counter threshold: `b ⟹ v⋈c` and `v⋈c ⟹ b`. The existing pool carries
    // bare Bool literals and bare Int bounds but never their guarded
    // combination, so the conjunctive Houdini drops the safety flag whenever
    // keeping it inductive requires such a guard (two_counters: the flag needs
    // `a2 ⟹ a0≥1`, `a0=1 ⟹ a2`, `a0≥3 ⟹ a1`, `a1 ⟹ a0≥2`). Restricted to
    // small-arity predicates (wide predicates already get the stage-5 guarded
    // diff rows and would flood the pool). Sound: model-based dropping +
    // final validation reject any non-inductive row.
    if guarded_impl_hints_enabled() && int_vars.len() <= HOUDINI_SMALL_ARITY {
        let bool_vars: Vec<&ChcVar> = state_vars
            .iter()
            .filter(|v| v.sort == ChcSort::Bool)
            .take(GUARDED_IMPL_MAX_BOOL_ARGS)
            .collect();
        // Counter-bit guards routinely need an OFF-BY-ONE threshold that is not
        // a syntactic literal of the rules (two_counters: `a2 ⟹ a0 ≥ 1` while
        // the rules only mention 0, 2, 3). Seed the guard thresholds from the
        // harvested constants AND their ±1 neighbours, smallest-magnitude
        // first, deduped.
        let g_consts: Vec<i128> = {
            let base: Vec<i128> = constants
                .iter()
                .copied()
                .take(GUARDED_IMPL_MAX_BASE_CONSTS)
                .collect();
            let mut expanded: Vec<i128> = Vec::new();
            let mut seen_c: DetHashSet<i128> = DetHashSet::default();
            for c in base {
                for cc in [c, c.saturating_sub(1), c.saturating_add(1)] {
                    if seen_c.insert(cc) {
                        expanded.push(cc);
                    }
                }
            }
            expanded.sort_by_key(|c| c.unsigned_abs());
            expanded.truncate(GUARDED_IMPL_MAX_CONSTS);
            expanded
        };
        for v in int_vars.iter().take(GUARDED_IMPL_MAX_INT_VARS) {
            let x = ChcExpr::var((*v).clone());
            for b in &bool_vars {
                let bv = ChcExpr::var((*b).clone());
                let not_b = ChcExpr::not(bv.clone());
                for &c in &g_consts {
                    let ge = ChcExpr::ge(x.clone(), ChcExpr::int(c));
                    let le = ChcExpr::le(x.clone(), ChcExpr::int(c));
                    let eq = ChcExpr::eq(x.clone(), ChcExpr::int(c));
                    // b ⟹ (v ≥ c) / b ⟹ (v ≤ c)
                    push(&mut pool, ChcExpr::or(not_b.clone(), ge.clone()));
                    push(&mut pool, ChcExpr::or(not_b.clone(), le.clone()));
                    // (v ≥ c) ⟹ b / (v ≤ c) ⟹ b
                    push(&mut pool, ChcExpr::or(bv.clone(), ChcExpr::not(ge)));
                    push(&mut pool, ChcExpr::or(bv.clone(), ChcExpr::not(le)));
                    // Equality guard/consequent (`v = c ⟹ b`, `b ⟹ v = c`):
                    // needed when the bit flips at exactly one counter value
                    // (two_counters C5: `a0 = 1 ⟹ a2`), unreachable from the
                    // one-sided bound guards alone.
                    push(&mut pool, ChcExpr::or(bv.clone(), ChcExpr::not(eq.clone())));
                    push(&mut pool, ChcExpr::or(not_b.clone(), eq));
                }
            }
        }
    }

    // Bounds over mined linear terms (difference/sum bounds): `t ≤ c` and
    // `t ≥ c` for every term compared against a constant somewhere in the
    // system and every harvested constant.
    for term in &terms {
        for &c in &constants {
            push(&mut pool, ChcExpr::le(term.clone(), ChcExpr::int(c)));
            push(&mut pool, ChcExpr::ge(term.clone(), ChcExpr::int(c)));
        }
    }

    // Int argument orderings: xi ≤ xj for ordered pairs, capped.
    let mut pairs = 0usize;
    'pairs: for (i, vi) in int_vars.iter().enumerate() {
        for (j, vj) in int_vars.iter().enumerate() {
            if i == j {
                continue;
            }
            if pairs >= HOUDINI_MAX_VAR_PAIRS {
                break 'pairs;
            }
            push(
                &mut pool,
                ChcExpr::le(ChcExpr::var((*vi).clone()), ChcExpr::var((*vj).clone())),
            );
            pairs += 1;
        }
    }

    // 2-variable sum/difference bounds (`vi+vj` and `vi-vj` against harvested
    // constants) — the linear multi-variable invariants many small-arity aeval
    // multi-phase problems need (e.g. `v0 - v1 ≤ 0`). Gated to few Int vars so
    // wide lustre predicates don't flood the pool (#9079). Sound: every
    // candidate is still validated against the original clauses.
    if int_vars.len() <= HOUDINI_SMALL_ARITY {
        for (i, vi) in int_vars.iter().enumerate() {
            for vj in int_vars.iter().skip(i + 1) {
                let xi = ChcExpr::var((*vi).clone());
                let xj = ChcExpr::var((*vj).clone());
                let sum = ChcExpr::add(xi.clone(), xj.clone());
                let diff = ChcExpr::sub(xi, xj);
                for &c in &constants {
                    push(&mut pool, ChcExpr::le(sum.clone(), ChcExpr::int(c)));
                    push(&mut pool, ChcExpr::ge(sum.clone(), ChcExpr::int(c)));
                    push(&mut pool, ChcExpr::le(diff.clone(), ChcExpr::int(c)));
                    push(&mut pool, ChcExpr::ge(diff.clone(), ChcExpr::int(c)));
                }
            }
        }
    }

    // #11 QUAL-MINE: problem-derived qualifier candidates (already expressed
    // over the state vars), appended LAST so the tuned classes above keep
    // their pool share on existing families; both polarities are admitted
    // (the wrong one drops out under the model-based filtering). On pure-BV
    // problems the classes above contribute almost nothing (no Int vars), so
    // this is the main vocabulary there.
    for qual in mined_qualifiers {
        push(&mut pool, qual.clone());
        push(&mut pool, ChcExpr::not(qual.clone()));
    }

    // Stage-5 widening needs cap headroom on wide predicates (see
    // `STAGE5_MAX_POOL`); the stock cap is byte-identical otherwise.
    pool.truncate(if stage5 {
        STAGE5_MAX_POOL
    } else {
        HOUDINI_MAX_POOL
    });

    // Pre-compute the primed (post-state) version of every candidate.
    let next_subst: Vec<(ChcVar, ChcExpr)> = state_vars
        .iter()
        .map(|v| {
            (
                v.clone(),
                ChcExpr::var(ChcVar::new(format!("{}_next", v.name), v.sort.clone())),
            )
        })
        .collect();
    pool.into_iter()
        .map(|expr| HoudiniCandidate {
            primed: expr.substitute(&next_subst),
            expr,
            init_verified: false,
        })
        .collect()
}

/// Harvest Int literals from the given formulas (iterative walk; dedup,
/// sorted by magnitude so small constants like 0/1 survive the cap).
fn harvest_int_constants(exprs: &[&ChcExpr]) -> Vec<i128> {
    let mut constants: Vec<i128> = Vec::new();
    let mut stack: Vec<&ChcExpr> = exprs.to_vec();
    while let Some(expr) = stack.pop() {
        match expr {
            ChcExpr::Int(n) if !constants.contains(n) => {
                constants.push(*n);
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                stack.extend(args.iter().map(|a| a.as_ref()));
            }
            ChcExpr::ConstArray(_, inner) => stack.push(inner.as_ref()),
            _ => {}
        }
    }
    constants.sort_by_key(|c| (c.unsigned_abs(), *c));
    constants.truncate(HOUDINI_MAX_CONSTANTS);
    constants
}

/// Mine candidate atoms from the init/transition/query formulas.
///
/// Walks the formulas and collects comparison/equivalence subterms
/// (`=`, `≤`, `<`, `≥`, `>`, `≠`, `iff`) whose free variables are either
/// all UNPRIMED canonical state vars (taken as-is) or all NEXT-state vars
/// (translated back to unprimed form). Atoms mentioning clause-local
/// variables or mixing pre/post state are skipped. Capped and deduped.
/// Returns `(atoms, linear_terms)`: candidate atoms, plus Int-sorted terms
/// that appear compared against a constant (for the term-bound class).
fn mine_atom_candidates(
    init: &ChcExpr,
    transition: &ChcExpr,
    query: &ChcExpr,
    state_vars: &[ChcVar],
) -> (Vec<ChcExpr>, Vec<ChcExpr>) {
    let unprimed: DetHashSet<&str> = state_vars.iter().map(|v| v.name.as_str()).collect();
    let next_names: Vec<String> = state_vars
        .iter()
        .map(|v| format!("{}_next", v.name))
        .collect();
    let next_to_unprimed: Vec<(ChcVar, ChcExpr)> = state_vars
        .iter()
        .zip(next_names.iter())
        .map(|(v, next)| {
            (
                ChcVar::new(next.clone(), v.sort.clone()),
                ChcExpr::var(v.clone()),
            )
        })
        .collect();
    let next_set: DetHashSet<&str> = next_names.iter().map(String::as_str).collect();

    let mut seen: DetHashSet<ChcExpr> = DetHashSet::default();
    let mut atoms: Vec<ChcExpr> = Vec::new();
    let mut seen_terms: DetHashSet<ChcExpr> = DetHashSet::default();
    let mut terms: Vec<ChcExpr> = Vec::new();
    let mut stack: Vec<&ChcExpr> = vec![init, transition, query];
    while let Some(expr) = stack.pop() {
        if atoms.len() >= HOUDINI_MAX_MINED_ATOMS {
            break;
        }
        let ChcExpr::Op(op, args) = expr else {
            continue;
        };
        // Keep walking inside every operator (atoms may be nested in
        // ite conditions or under boolean structure).
        stack.extend(args.iter().map(|a| a.as_ref()));

        // Linear terms compared against constants (`t ⋈ c`): collect `t`
        // for the term-bound candidate class (`t ≤ c'` / `t ≥ c'` over all
        // harvested constants), generalizing difference/sum bounds beyond
        // the exact constants that appear (e.g. metros' beacon distance).
        if matches!(
            op,
            ChcOp::Eq | ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt
        ) && args.len() == 2
            && terms.len() < HOUDINI_MAX_MINED_TERMS
        {
            for (side, other) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                if !matches!(other.as_ref(), ChcExpr::Int(_))
                    || matches!(side.as_ref(), ChcExpr::Var(_) | ChcExpr::Int(_))
                {
                    continue;
                }
                let side_vars = side.vars();
                if side_vars.is_empty() {
                    continue;
                }
                let all_unprimed = side_vars.iter().all(|v| unprimed.contains(v.name.as_str()));
                let all_next =
                    !all_unprimed && side_vars.iter().all(|v| next_set.contains(v.name.as_str()));
                let term = if all_unprimed {
                    side.as_ref().clone()
                } else if all_next {
                    side.substitute(&next_to_unprimed)
                } else {
                    continue;
                };
                if seen_terms.insert(term.clone()) {
                    terms.push(term);
                }
            }
        }

        // Definitional updates `(= v_next φ(current))` (Bool monitors in
        // lustre encodings, e.g. `ok' = ok ∧ guard`): mine the Bool
        // right-hand side φ as a candidate — it is the precondition that
        // keeps the monitor true across a step.
        if matches!(op, ChcOp::Eq | ChcOp::Iff) && args.len() == 2 {
            for (lhs, rhs) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                let ChcExpr::Var(lv) = lhs.as_ref() else {
                    continue;
                };
                if !next_set.contains(lv.name.as_str()) {
                    continue;
                }
                let rhs_vars = rhs.vars();
                if rhs_vars.is_empty()
                    || !rhs_vars.iter().all(|v| unprimed.contains(v.name.as_str()))
                {
                    continue;
                }
                if rhs.sort() != ChcSort::Bool {
                    continue;
                }
                let atom = rhs.as_ref().clone();
                if seen.insert(atom.clone()) {
                    atoms.push(atom);
                }
            }
        }

        // Comparison atoms and guarded clauses (`or` / `implies` keep their
        // disjunctive shape — Houdini cannot rebuild it from parts). BV
        // comparisons are included since the BV un-gate (#11 QUAL-MINE):
        // vmt-style BV transitions define their monitors through exactly
        // these word-level atoms.
        if !matches!(
            op,
            ChcOp::Eq
                | ChcOp::Ne
                | ChcOp::Le
                | ChcOp::Lt
                | ChcOp::Ge
                | ChcOp::Gt
                | ChcOp::Iff
                | ChcOp::Or
                | ChcOp::Implies
                | ChcOp::BvULe
                | ChcOp::BvULt
                | ChcOp::BvUGe
                | ChcOp::BvUGt
                | ChcOp::BvSLe
                | ChcOp::BvSLt
                | ChcOp::BvSGe
                | ChcOp::BvSGt
        ) {
            continue;
        }
        let vars = expr.vars();
        if vars.is_empty() {
            continue;
        }
        let all_unprimed = vars.iter().all(|v| unprimed.contains(v.name.as_str()));
        let all_next = !all_unprimed && vars.iter().all(|v| next_set.contains(v.name.as_str()));
        let atom = if all_unprimed {
            expr.clone()
        } else if all_next {
            expr.substitute(&next_to_unprimed)
        } else {
            continue;
        };
        if seen.insert(atom.clone()) {
            atoms.push(atom);
        }
    }
    (atoms, terms)
}

/// Inline top-level definitional equalities of clause-local variables.
///
/// TS extraction renames clause-local (existential) variables to
/// `__init0_*` / `__tr0_*` names; lustre encodings define the relations the
/// invariant needs through exactly these locals (`(= local φ(state))`).
/// Substituting the definitions (a) exposes φ to candidate mining (locals
/// cannot appear in candidates) and (b) shrinks the solver backgrounds.
/// Locals are existentially quantified, so the result is equivalent over
/// the allowed (state) variables. Only small, acyclic, top-level-conjunct
/// definitions are inlined; chains resolve across iterations.
fn inline_local_definitions(expr: &ChcExpr, allowed: &DetHashSet<&str>) -> ChcExpr {
    let mut current = expr.clone();
    for _ in 0..8 {
        let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        {
            let mut defined: DetHashSet<String> = DetHashSet::default();
            for conjunct in current.conjuncts() {
                let ChcExpr::Op(op, args) = conjunct else {
                    continue;
                };
                if !matches!(op, ChcOp::Eq | ChcOp::Iff) || args.len() != 2 {
                    continue;
                }
                for (lhs, rhs) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                    let ChcExpr::Var(v) = lhs.as_ref() else {
                        continue;
                    };
                    if allowed.contains(v.name.as_str()) || defined.contains(&v.name) {
                        continue;
                    }
                    let rhs_vars = rhs.vars();
                    if rhs_vars.iter().any(|rv| rv.name == v.name)
                        || !rhs_vars.iter().all(|rv| allowed.contains(rv.name.as_str()))
                        || expr_node_count(rhs, 48) > 40
                    {
                        continue;
                    }
                    defined.insert(v.name.clone());
                    subst.push((v.clone(), rhs.as_ref().clone()));
                    break;
                }
            }
        }
        if subst.is_empty() {
            break;
        }
        current = current.substitute(&subst).simplify_constants();
    }
    current
}

/// Count expression nodes up to `cap` (cheap blow-up guard for inlining).
fn expr_node_count(expr: &ChcExpr, cap: usize) -> usize {
    let mut count = 0usize;
    let mut stack = vec![expr];
    while let Some(e) = stack.pop() {
        count += 1;
        if count >= cap {
            return count;
        }
        match e {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => stack.extend(args.iter().map(|a| a.as_ref())),
            ChcExpr::ConstArray(_, inner) => stack.push(inner.as_ref()),
            _ => {}
        }
    }
    count
}

/// Equality-propagate a background formula while preserving EQUIVALENCE.
///
/// Lustre-style inits/transitions carry long `var = const` / `var = var`
/// equality chains feeding guarded case splits (e.g. abs-value encodings
/// `(or (≤ 0 z) (= (+ a z) 0))`). Substituting derived `var = const`
/// bindings and constant-folding resolves those splits syntactically,
/// turning multi-second executor queries into trivial ones. Unlike
/// `into_propagate_equalities` (equisatisfiable only), the extracted
/// bindings are re-conjoined so models still pin the substituted vars —
/// required because candidate dropping evaluates candidates under models.
fn propagate_background(expr: &ChcExpr) -> ChcExpr {
    let mut current = expr.clone();
    let mut bindings: Vec<ChcExpr> = Vec::new();
    for _ in 0..8 {
        let equalities = current.extract_var_const_equalities();
        if equalities.is_empty() {
            break;
        }
        let subst: Vec<(ChcVar, ChcExpr)> = equalities
            .iter()
            .map(|(v, c)| (v.clone(), ChcExpr::Int(*c)))
            .collect();
        bindings.extend(
            equalities
                .iter()
                .map(|(v, c)| ChcExpr::eq(ChcExpr::var(v.clone()), ChcExpr::Int(*c))),
        );
        let next = current.substitute(&subst).simplify_constants();
        let fixpoint = next == current;
        current = next;
        if fixpoint || matches!(current, ChcExpr::Bool(_)) {
            break;
        }
    }
    if bindings.is_empty() {
        current
    } else {
        ChcExpr::and_all(std::iter::once(current).chain(bindings))
    }
}

/// Env-gated debug tracing for Houdini refinement (`--chc-houdini-debug`).
fn houdini_debug() -> bool {
    ay_core::misc_cli_flags().chc_houdini_debug
}

/// Whether the Houdini prepass accepts single-predicate BV problems (#11
/// QUAL-MINE gate fix). DEFAULT ON; `AY_CHC_DISABLE_HOUDINI_BV=1` restores
/// the historical pure-Int/Bool-only gating. Read fresh (once per solve).
/// Sound either way: the gate only selects WHERE the drop-loop runs; every
/// surviving invariant is still validated against the original clauses.
fn houdini_bv_enabled() -> bool {
    crate::ab_switches::get().houdini_bv // B27: CLI-owned; env retired.
}

/// Whether the Phase-B fast-path is enabled (`AY_CHC_HOUDINI_PHASEB_FAST`).
/// DEFAULT ON; only the literal "0" disables (restoring the round-by-round
/// combined-query-then-first-drop-sweep behavior byte-for-byte).
///
/// The fast-path is a pure performance optimization that PRESERVES the inductive
/// fixpoint: (1) it short-circuits the monolithic combined consecution query
/// once that query has returned Unknown for the current pool (or once the pool
/// exceeds [`HOUDINI_PHASEB_COMBINED_POOL_LIMIT`]) — the combined query only ever
/// produces drops the per-candidate sweep produces too; and (2) it makes the
/// sweep FULL-DRAIN (drop every non-inductive candidate in one pass instead of
/// returning on the first drop). Both are sound by Houdini monotonicity: a
/// candidate found non-inductive w.r.t. the full pool stays non-inductive w.r.t.
/// any subset (dropping only weakens the antecedent), so the greatest inductive
/// subset reached is identical.
fn houdini_phaseb_fast_enabled() -> bool {
    // B15: typed A/B switch (`ab_switches`); the never-set env read is gone.
    crate::ab_switches::get().houdini_phaseb_fast
}

/// Project the post-state out of a consecution counterexample model:
/// map each state var name to the model value of its `_next` counterpart,
/// so candidates (over unprimed vars) can be evaluated in the post-state.
fn post_state_view(
    model: &FxHashMap<String, SmtValue>,
    state_vars: &[ChcVar],
) -> FxHashMap<String, SmtValue> {
    let mut post = FxHashMap::default();
    for v in state_vars {
        if let Some(value) = model.get(&format!("{}_next", v.name)) {
            post.insert(v.name.clone(), value.clone());
        }
    }
    post
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adaptive::AdaptiveConfig;
    use crate::classifier::ProblemClassifier;
    use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
    use ntest::timeout;

    /// P(x, ok):
    ///   init:  x = 0 ∧ ok                    ⇒ P(x, ok)
    ///   trans: P(x, ok)                      ⇒ P(x+1, ok ∧ x ≥ 0)
    ///   query: P(x, ok) ∧ ¬ok                ⇒ false
    ///
    /// The flag alone is NOT inductive (ok' = ok ∧ x ≥ 0 needs the support
    /// lemma x ≥ 0); Houdini must converge on {ok, x ≥ 0, ...} ⊇ {flag}.
    fn flag_with_support_lemma_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Bool]);
        let x = ChcVar::new("x", ChcSort::Int);
        let ok = ChcVar::new("ok", ChcSort::Bool);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                ChcExpr::var(ok.clone()),
            )),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())])],
                None,
            ),
            ClauseHead::Predicate(
                p,
                vec![
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ChcExpr::and(
                        ChcExpr::var(ok.clone()),
                        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                    ),
                ],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x), ChcExpr::var(ok.clone())])],
                Some(ChcExpr::not(ChcExpr::var(ok))),
            ),
            ClauseHead::False,
        ));
        problem
    }

    /// P(x, ok):
    ///   init:  x = 0 ∧ ok                    ⇒ P(x, ok)
    ///   trans: P(x, ok)                      ⇒ P(x+1, x ≤ 2)
    ///   query: P(x, ok) ∧ ¬ok                ⇒ false
    ///
    /// The flag is reachable-false (after x > 2 the next ok is false), so
    /// every Houdini refinement must eventually drop the flag ⇒ None.
    fn flag_eventually_falsified_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Bool]);
        let x = ChcVar::new("x", ChcSort::Int);
        let ok = ChcVar::new("ok", ChcSort::Bool);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                ChcExpr::var(ok.clone()),
            )),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())])],
                None,
            ),
            ClauseHead::Predicate(
                p,
                vec![
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(2)),
                ],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x), ChcExpr::var(ok.clone())])],
                Some(ChcExpr::not(ChcExpr::var(ok))),
            ),
            ClauseHead::False,
        ));
        problem
    }

    #[test]
    #[timeout(60000)]
    fn houdini_finds_flag_with_support_lemma_and_answers_sat() {
        let problem = flag_with_support_lemma_problem();
        let features = ProblemClassifier::classify(&problem);
        let portfolio = AdaptivePortfolio::new(problem, AdaptiveConfig::default());

        // The flag-only guess must fail (it is not inductive on its own)...
        assert!(
            portfolio
                .try_query_flag_invariant_prepass(&features, None)
                .is_none(),
            "flag-only prepass unexpectedly validated; Houdini test premise broken"
        );

        // ...while Houdini finds the {ok, x ≥ 0} conjunction and answers sat.
        let result = portfolio.try_houdini_conjunctive_prepass(&features, None);
        let Some((PortfolioResult::Safe(model), ValidationEvidence::FullVerification)) = result
        else {
            panic!("expected validated Safe result, got {result:?}");
        };
        let interp = model
            .get(&portfolio.problem.predicates()[0].id)
            .expect("invariant interpretation for the single predicate");
        // The surviving conjunction must contain the flag literal and an
        // x ≥ 0 / 0 ≤ x style support lemma.
        let formula = format!("{:?}", interp.formula);
        assert!(
            formula.contains("__hd0_a1"),
            "flag literal missing from surviving conjunction: {formula}"
        );
        assert!(
            formula.contains("__hd0_a0"),
            "integer support lemma missing from surviving conjunction: {formula}"
        );
    }

    #[test]
    #[timeout(60000)]
    fn houdini_drops_falsifiable_flag_and_returns_none() {
        let problem = flag_eventually_falsified_problem();
        let features = ProblemClassifier::classify(&problem);
        let portfolio = AdaptivePortfolio::new(problem, AdaptiveConfig::default());

        let result = portfolio.try_houdini_conjunctive_prepass(&features, None);
        assert!(
            result.is_none(),
            "flag is falsifiable; Houdini must fail closed, got {result:?}"
        );
    }

    /// P(x: BV8, ok: Bool)  (#11 QUAL-MINE BV un-gate):
    ///   init:  x = 0 ∧ ok                    ⇒ P(x, ok)
    ///   trans: P(x, ok) ⇒ P(ite(x ≤u 10, x+1, x), ok ∧ x ≤u 11)
    ///   query: P(x, ok) ∧ ¬ok                ⇒ false
    ///
    /// The flag alone is NOT inductive (ok' needs the support lemma
    /// x ≤u 11, a BV bound mined from the transition); before the BV
    /// un-gate this problem never reached the Houdini prepass at all.
    fn bv_flag_with_support_lemma_problem() -> ChcProblem {
        use std::sync::Arc;
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::BitVec(8), ChcSort::Bool]);
        let x = ChcVar::new("x", ChcSort::BitVec(8));
        let ok = ChcVar::new("ok", ChcSort::Bool);
        let bv = |v: u128| ChcExpr::BitVec(v, 8);
        let bvule = |a: ChcExpr, b: ChcExpr| ChcExpr::bv_ule(a, b);
        let bvadd =
            |a: ChcExpr, b: ChcExpr| ChcExpr::Op(ChcOp::BvAdd, vec![Arc::new(a), Arc::new(b)]);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(x.clone()), bv(0)),
                ChcExpr::var(ok.clone()),
            )),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())])],
                None,
            ),
            ClauseHead::Predicate(
                p,
                vec![
                    ChcExpr::ite(
                        bvule(ChcExpr::var(x.clone()), bv(10)),
                        bvadd(ChcExpr::var(x.clone()), bv(1)),
                        ChcExpr::var(x.clone()),
                    ),
                    ChcExpr::and(
                        ChcExpr::var(ok.clone()),
                        bvule(ChcExpr::var(x.clone()), bv(11)),
                    ),
                ],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x), ChcExpr::var(ok.clone())])],
                Some(ChcExpr::not(ChcExpr::var(ok))),
            ),
            ClauseHead::False,
        ));
        problem
    }

    /// P(x: BV8, ok: Bool) with a REACHABLE ¬ok (after 3 steps x >u 2 makes
    /// the next ok false): the naive move — trusting the mined BV vocabulary
    /// without validation — would emit a wrong `sat`; the prepass must fail
    /// closed to `None`.
    fn bv_flag_eventually_falsified_problem() -> ChcProblem {
        use std::sync::Arc;
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::BitVec(8), ChcSort::Bool]);
        let x = ChcVar::new("x", ChcSort::BitVec(8));
        let ok = ChcVar::new("ok", ChcSort::Bool);
        let bv = |v: u128| ChcExpr::BitVec(v, 8);
        let bvadd =
            |a: ChcExpr, b: ChcExpr| ChcExpr::Op(ChcOp::BvAdd, vec![Arc::new(a), Arc::new(b)]);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(x.clone()), bv(0)),
                ChcExpr::var(ok.clone()),
            )),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())])],
                None,
            ),
            ClauseHead::Predicate(
                p,
                vec![
                    bvadd(ChcExpr::var(x.clone()), bv(1)),
                    ChcExpr::bv_ule(ChcExpr::var(x.clone()), bv(2)),
                ],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x), ChcExpr::var(ok.clone())])],
                Some(ChcExpr::not(ChcExpr::var(ok))),
            ),
            ClauseHead::False,
        ));
        problem
    }

    #[test]
    #[timeout(120000)]
    fn houdini_bv_ungated_finds_flag_with_bv_support_lemma() {
        let problem = bv_flag_with_support_lemma_problem();
        let features = ProblemClassifier::classify(&problem);
        let portfolio = AdaptivePortfolio::new(problem, AdaptiveConfig::default());

        let result = portfolio.try_houdini_conjunctive_prepass(&features, None);
        let Some((PortfolioResult::Safe(model), ValidationEvidence::FullVerification)) = result
        else {
            panic!("expected validated Safe result on the BV vmt shape, got {result:?}");
        };
        let interp = model
            .get(&portfolio.problem.predicates()[0].id)
            .expect("invariant interpretation for the single predicate");
        let formula = format!("{:?}", interp.formula);
        assert!(
            formula.contains("__hd0_a1"),
            "flag literal missing from surviving conjunction: {formula}"
        );
        assert!(
            formula.contains("__hd0_a0"),
            "BV support lemma missing from surviving conjunction: {formula}"
        );
    }

    #[test]
    #[timeout(120000)]
    fn houdini_bv_falsifiable_flag_fails_closed() {
        let problem = bv_flag_eventually_falsified_problem();
        let features = ProblemClassifier::classify(&problem);
        let portfolio = AdaptivePortfolio::new(problem, AdaptiveConfig::default());

        let result = portfolio.try_houdini_conjunctive_prepass(&features, None);
        assert!(
            result.is_none(),
            "flag is falsifiable; BV Houdini must fail closed, got {result:?}"
        );
    }

    #[test]
    fn harvest_constants_prefers_small_magnitudes() {
        let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        let exprs: Vec<ChcExpr> = (0..20)
            .map(|i| ChcExpr::eq(x.clone(), ChcExpr::int(100 - 10 * i)))
            .collect();
        let conj = ChcExpr::and_all(exprs);
        let constants = harvest_int_constants(&[&conj]);
        assert_eq!(constants.len(), HOUDINI_MAX_CONSTANTS);
        assert!(constants.contains(&0));
        assert!(constants.contains(&10) || constants.contains(&-10));
        assert!(!constants.contains(&100));
    }
}
