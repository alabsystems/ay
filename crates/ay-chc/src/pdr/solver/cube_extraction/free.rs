// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Spacer lane's free child constructor (Workstream B R2,
//! the development design notes at `9598c4206`, §4.1.3; Spacer `create_children`,
//! `spacer_context.cpp:4043-4160`).
//!
//! A child POB for a linear clause `c` is the projection of `T_c ∧ post(head)`
//! onto the body predicate's canonical variables, under the model of the Q1
//! query that found the predecessor. The projection is the exact
//! under-approximating MBP of `mbp/exact.rs`, so the child is a subset of the
//! parent's pre-image that contains the model (INV-P); a variable that
//! `T_c ∧ post` does not constrain stays FREE (no augmentation pins, no
//! "every canonical variable must occur" gate, no minimised model). Point cubes
//! remain only as counted fallbacks: a variable with no usable model value
//! (`PointFallbackNoValue`), a canonical-name clash (`PointFallbackNonCanonical`)
//! and a cube the model falsifies (`PointFallbackMismatch`).
//!
//! Encoding: for every argument position `i` the equality `c_i = a_i`
//! (canonical variable = clause argument term) is conjoined, and every
//! non-canonical variable is eliminated. Repeated arguments (`P(x, x)`) and
//! expression arguments (`P(x + 1)`) are therefore handled exactly, with no
//! special case.

use super::super::{ChcExpr, ChcVar, FxHashMap, FxHashSet, PdrSolver, PredicateId, SmtValue};
use crate::mbp::exact::{ExactFail, ExactStats};
use crate::pdr::cube::literals::LitCube;
use crate::pdr::solver::spacer_core::stats::CubeSource;

/// Result of [`PdrSolver::child_cube_from_model`].
pub(in crate::pdr::solver) struct FreeChild {
    /// The child cube (`None` only when the point fallback also failed).
    pub(in crate::pdr::solver) cube: Option<LitCube>,
    /// Where it came from (`cube_source` board column).
    pub(in crate::pdr::solver) source: CubeSource,
    /// Variables eliminated by per-variable model substitution.
    pub(in crate::pdr::solver) substituted: usize,
    /// Exact-projection counters of the attempt(s) that ran.
    pub(in crate::pdr::solver) exact: ExactStats,
}

/// One construction attempt.
enum FreeAttempt {
    /// The free cube, the number of variables eliminated by model
    /// substitution, and the projection counters.
    Cube(LitCube, usize, ExactStats),
    /// No free cube; the reason becomes the point-fallback source.
    Fallback(CubeSource),
}

impl PdrSolver {
    /// Whether the Spacer lane builds the children of `pred`'s POBs with the
    /// free constructor (R2, `free_pob`): lane on, linear problem, linear
    /// predicate (`DESIGN` §3.7: `free_pob` additionally requires
    /// `problem_is_linear`).
    pub(in crate::pdr::solver) fn lane_free_pob(&self, pred: PredicateId) -> bool {
        self.spacer_core
            && self.config.spacer.free_pob
            && self.problem_is_linear
            && self.linear_pred(pred)
    }

    /// Spacer `create_children` for one linear clause (§4.1.3). `pred`/`args`:
    /// the child predicate and its argument terms in the clause (body
    /// arguments, or the head arguments for a fact clause of the POB's own
    /// predicate); `transition`: `T_c`; `state_on_head`: the parent POB on the
    /// clause head; `model`: the Q1 model (a model of `T_c ∧ state_on_head`).
    /// When the free cube equals a state already excluded at this parent level
    /// (`excluded_states`), it is recomputed once on `formula ∧ exclusion`.
    ///
    /// Takes `&self` (callers iterate `self.problem`); the caller records
    /// `FreeChild::source` with `SpacerCoreStats::record_cube_source`.
    /// `cube == None` only when even the point fallback fails (the caller's
    /// `had_sat_no_cube` path).
    #[allow(clippy::too_many_arguments)]
    pub(in crate::pdr::solver) fn child_cube_from_model(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        transition: &ChcExpr,
        state_on_head: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
        exclusion: Option<&ChcExpr>,
        excluded_states: &[ChcExpr],
    ) -> FreeChild {
        let formula = ChcExpr::and(transition.clone(), state_on_head.clone());
        let mut attempt = self.free_cube_attempt(pred, args, &formula, model);
        if let FreeAttempt::Cube(cube, _, _) = &attempt {
            let repeats_excluded = excluded_states.iter().any(|s| s == cube.expr());
            if repeats_excluded {
                if let Some(ex) = exclusion.filter(|e| !matches!(e, ChcExpr::Bool(true))) {
                    let with_exclusion = ChcExpr::and(formula.clone(), ex.clone());
                    attempt = self.free_cube_attempt(pred, args, &with_exclusion, model);
                }
            }
        }
        match attempt {
            FreeAttempt::Cube(cube, substituted, exact) => {
                let source = if cube.is_empty() {
                    CubeSource::MbpFreeTrue
                } else if substituted > 0 {
                    CubeSource::PerVarSubst
                } else {
                    CubeSource::MbpFree
                };
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR-SPACER: free child cube for pred {} ({} lits, {} substituted): {}",
                        pred.index(),
                        cube.len(),
                        substituted,
                        cube.expr()
                    );
                }
                FreeChild {
                    cube: Some(cube),
                    source,
                    substituted,
                    exact,
                }
            }
            FreeAttempt::Fallback(source) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR-SPACER: free child cube for pred {} fell back to a point cube ({source:?})",
                        pred.index()
                    );
                }
                FreeChild {
                    cube: self
                        .cube_from_model_or_constraints(pred, args, &formula, model)
                        .map(|c| LitCube::from_expr(&c)),
                    source,
                    substituted: 0,
                    exact: ExactStats::default(),
                }
            }
        }
    }

    fn free_cube_attempt(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        formula: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> FreeAttempt {
        let Some(canon) = self.canonical_vars(pred).map(<[ChcVar]>::to_vec) else {
            return FreeAttempt::Fallback(CubeSource::PointFallbackNonCanonical);
        };
        if canon.len() != args.len() {
            return FreeAttempt::Fallback(CubeSource::PointFallbackNonCanonical);
        }
        let canon_names: FxHashSet<&str> = canon.iter().map(|v| v.name.as_str()).collect();
        let clause_vars: Vec<ChcVar> = {
            let mut seen: FxHashSet<String> = FxHashSet::default();
            let mut vs = Vec::new();
            for v in args.iter().flat_map(ChcExpr::vars).chain(formula.vars()) {
                if seen.insert(v.name.clone()) {
                    vs.push(v);
                }
            }
            vs
        };
        if clause_vars
            .iter()
            .any(|v| canon_names.contains(v.name.as_str()))
        {
            // A clause variable carries a canonical name: the encoding below
            // would conflate the two.
            return FreeAttempt::Fallback(CubeSource::PointFallbackNonCanonical);
        }
        // c_i = a_i for every position; the model extended with c_i := a_i(M).
        let mut conjuncts = Vec::with_capacity(args.len() + 1);
        let mut extended = model.clone();
        for (c, a) in canon.iter().zip(args) {
            conjuncts.push(ChcExpr::eq(ChcExpr::var(c.clone()), a.clone()));
            if let Some(v) = crate::expr::evaluate_expr(a, model) {
                extended.insert(c.name.clone(), v);
            }
        }
        conjuncts.push(formula.clone());
        let encoded = ChcExpr::and_all(conjuncts);
        // Argument variables first: their `c_i = x` equalities rename them.
        let arg_names: FxHashSet<String> = args
            .iter()
            .flat_map(ChcExpr::vars)
            .map(|v| v.name)
            .collect();
        let (mut elim, rest): (Vec<ChcVar>, Vec<ChcVar>) = clause_vars
            .into_iter()
            .partition(|v| arg_names.contains(&v.name));
        elim.extend(rest);

        let mut exact = ExactStats::default();
        let (lits, mut substituted) = if self.config.spacer.mbp_exact_lia {
            match self.mbp.project_exact(&encoded, &elim, &extended) {
                Ok(p) => {
                    exact = p.stats;
                    (p.lits, p.substituted.len())
                }
                Err(ExactFail::NoValue(_)) => {
                    return FreeAttempt::Fallback(CubeSource::PointFallbackNoValue)
                }
            }
        } else {
            // A/B row (`mbp_exact_lia` off): the legacy projector (real shadow,
            // may over-approximate), residuals substituted per variable.
            let r = self.mbp.project_with_residuals(&encoded, &elim, &extended);
            let mut subst = Vec::with_capacity(r.residual_vars.len());
            for v in &r.residual_vars {
                match crate::mbp::Mbp::value_expr_for(v, &extended) {
                    Some(e) => subst.push((v.clone(), e)),
                    None => return FreeAttempt::Fallback(CubeSource::PointFallbackNoValue),
                }
            }
            let projected = r.formula.substitute(&subst).simplify_constants();
            (projected.collect_conjuncts_nontrivial(), subst.len())
        };

        // Defensive: nothing but canonical variables may remain.
        let mut out: Vec<ChcExpr> = Vec::with_capacity(lits.len());
        for lit in lits {
            let stray: Vec<ChcVar> = lit
                .vars()
                .into_iter()
                .filter(|v| !canon_names.contains(v.name.as_str()))
                .collect();
            if stray.is_empty() {
                out.push(lit);
                continue;
            }
            let mut subst = Vec::with_capacity(stray.len());
            for v in stray {
                match crate::mbp::Mbp::value_expr_for(&v, &extended) {
                    Some(e) => subst.push((v, e)),
                    None => return FreeAttempt::Fallback(CubeSource::PointFallbackNoValue),
                }
            }
            substituted += subst.len();
            out.push(lit.substitute(&subst).simplify_constants());
        }
        let cube = LitCube::from_lits(
            out.into_iter()
                .flat_map(|l| l.collect_conjuncts_nontrivial())
                .collect(),
        );
        if cube
            .lits()
            .iter()
            .any(|l| matches!(l, ChcExpr::Bool(false)))
        {
            return FreeAttempt::Fallback(CubeSource::PointFallbackMismatch);
        }
        // INV-P guard (step 5): the model must not falsify the cube. `None`
        // (opaque atoms) is accepted, as the legacy guard does.
        if self.mbp.eval_bool(cube.expr(), &extended) == Some(false) {
            return FreeAttempt::Fallback(CubeSource::PointFallbackMismatch);
        }
        FreeAttempt::Cube(cube, substituted, exact)
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::panic)]
#[path = "free_tests.rs"]
mod tests;
