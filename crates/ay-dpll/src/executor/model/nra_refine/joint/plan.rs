// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded equality-cluster discovery and affine-elimination planning.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{Sort, Symbol, TermData, TermId};
use num_rational::BigRational;

use super::math::is_arith_sort;
use super::{
    Equality, Plan, Solve, MAX_CLUSTER_EQS, MAX_CLUSTER_VARS, MAX_EQUALITIES, MAX_SCAN_NODES,
};
use crate::executor::model::{with_isolated_eval_memo, EvalValue};
use crate::executor::Executor;

struct Elimination {
    solves: Vec<Solve>,
    solved: DetHashSet<TermId>,
    used: DetHashSet<usize>,
}

struct ProbeContext<'a> {
    alpha: TermId,
    proxy: &'a BigRational,
    partners: &'a [TermId],
    values: &'a DetHashMap<TermId, BigRational>,
    solves: &'a [Solve],
    eqs: &'a [Equality],
}

/// Grow the equality cluster reachable from `alpha`, returning its equalities
/// and the other arithmetic variables in deterministic order.
fn equality_cluster(
    alpha: TermId,
    equalities: Vec<Equality>,
) -> Option<(Vec<Equality>, Vec<TermId>)> {
    let mut cluster_vars: DetHashSet<TermId> = DetHashSet::default();
    cluster_vars.insert(alpha);
    let mut chosen: Vec<usize> = Vec::new();
    loop {
        let mut grew = false;
        for (index, eq) in equalities.iter().enumerate() {
            if chosen.contains(&index) {
                continue;
            }
            if eq.vars.iter().any(|var| cluster_vars.contains(var)) {
                chosen.push(index);
                cluster_vars.extend(eq.vars.iter().copied());
                grew = true;
            }
        }
        if !grew {
            break;
        }
        if chosen.len() > MAX_CLUSTER_EQS || cluster_vars.len() > MAX_CLUSTER_VARS {
            return None;
        }
    }
    if chosen.is_empty() {
        return None;
    }
    let eqs = equalities
        .into_iter()
        .enumerate()
        .filter(|(index, _)| chosen.contains(index))
        .map(|(_, eq)| eq)
        .collect();
    let mut partners: Vec<TermId> = cluster_vars
        .into_iter()
        .filter(|var| *var != alpha)
        .collect();
    partners.sort_by_key(|term| term.0);
    Some((eqs, partners))
}

/// Return the sole live unsolved equality, or decline when the plan would
/// need to parametrize more than one residual curve.
fn live_residual(
    alpha: TermId,
    eqs: &[Equality],
    solved: &DetHashSet<TermId>,
    used: &DetHashSet<usize>,
) -> Option<Option<usize>> {
    let mut residuals: Vec<usize> = (0..eqs.len())
        .filter(|index| !used.contains(index))
        .filter(|index| {
            eqs[*index]
                .vars
                .iter()
                .any(|var| *var == alpha || solved.contains(var))
        })
        .collect();
    if residuals.len() > 1 {
        return None;
    }
    Some(residuals.pop())
}

impl Executor {
    /// Require every rational proposal to inhabit its declared sort. Exact
    /// assertion evaluation alone would accept `n = 3/2` for an `Int` term.
    pub(super) fn assignment_respects_sorts(&self, assignment: &[(TermId, BigRational)]) -> bool {
        assignment.iter().all(|(term, value)| {
            !matches!(self.ctx.terms.sort(*term), Sort::Int) || value.is_integer()
        })
    }

    /// Harvest every positive-polarity arithmetic equality: conjunctive
    /// positions only (`and` under positive polarity, `or` under negative,
    /// `not` flipping it). An equality under a positive disjunction is not
    /// harvested because it need not hold in the model.
    pub(in crate::executor::model::nra_refine) fn collect_positive_equalities(
        &self,
    ) -> Option<Vec<Equality>> {
        let mut out: Vec<Equality> = Vec::new();
        let mut seen: DetHashSet<(TermId, bool)> = DetHashSet::default();
        let mut stack: Vec<(TermId, bool)> = self
            .ctx
            .assertions
            .iter()
            .map(|&term| (term, true))
            .collect();
        let mut visited = 0usize;
        while let Some((term, polarity)) = stack.pop() {
            visited += 1;
            if visited > MAX_SCAN_NODES {
                return None;
            }
            if !seen.insert((term, polarity)) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::Not(inner) => stack.push((*inner, !polarity)),
                TermData::App(Symbol::Named(name), args) => match name.as_str() {
                    "not" if args.len() == 1 => stack.push((args[0], !polarity)),
                    "and" if polarity => stack.extend(args.iter().map(|&arg| (arg, polarity))),
                    "or" if !polarity => stack.extend(args.iter().map(|&arg| (arg, polarity))),
                    "=" if polarity && args.len() == 2 => {
                        self.harvest_equality(args[0], args[1], &mut out)?;
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        Some(out)
    }

    fn harvest_equality(&self, lhs: TermId, rhs: TermId, out: &mut Vec<Equality>) -> Option<()> {
        if !is_arith_sort(self.ctx.terms.sort(lhs)) {
            return Some(());
        }
        let mut vars = Vec::new();
        self.collect_arith_vars(lhs, &mut vars)?;
        self.collect_arith_vars(rhs, &mut vars)?;
        vars.sort_by_key(|term| term.0);
        vars.dedup();
        out.push(Equality { lhs, rhs, vars });
        (out.len() <= MAX_EQUALITIES).then_some(())
    }

    /// Append the arithmetic variables of `term` to `out`.
    pub(in crate::executor::model::nra_refine) fn collect_arith_vars(
        &self,
        term: TermId,
        out: &mut Vec<TermId>,
    ) -> Option<()> {
        let mut seen: DetHashSet<TermId> = DetHashSet::default();
        let mut stack = vec![term];
        let mut visited = 0usize;
        while let Some(next) = stack.pop() {
            visited += 1;
            if visited > MAX_SCAN_NODES {
                return None;
            }
            if !seen.insert(next) {
                continue;
            }
            match self.ctx.terms.get(next) {
                TermData::Var(_, _) if is_arith_sort(self.ctx.terms.sort(next)) => out.push(next),
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(cond, then_branch, else_branch) => {
                    stack.extend([*cond, *then_branch, *else_branch]);
                }
                _ => {}
            }
        }
        Some(())
    }

    /// Build the reachable cluster, its triangular affine solves, and at most
    /// one live residual curve. `proxy` is used only for structural probes.
    pub(super) fn build_plan(
        &mut self,
        alpha: TermId,
        equalities: Vec<Equality>,
        proxy: &BigRational,
    ) -> Option<Plan> {
        let (eqs, partners) = equality_cluster(alpha, equalities)?;
        let values = self.partner_model_values(&partners)?;
        let elimination = self.build_elimination(alpha, proxy, &partners, &values, &eqs);
        self.validate_solve_dependencies(&elimination.solves, &eqs)?;
        let residual = live_residual(alpha, &eqs, &elimination.solved, &elimination.used)?;
        let free = partners
            .iter()
            .copied()
            .filter(|var| !elimination.solved.contains(var))
            .collect();
        Some(Plan {
            alpha,
            eqs,
            solves: elimination.solves,
            free,
            values,
            residual,
        })
    }

    fn partner_model_values(&self, partners: &[TermId]) -> Option<DetHashMap<TermId, BigRational>> {
        let model = self.last_model.as_ref()?;
        let mut values = DetHashMap::default();
        for partner in partners {
            match with_isolated_eval_memo(|| self.evaluate_term(model, *partner)) {
                EvalValue::Rational(value) => {
                    values.insert(*partner, value);
                }
                _ => return None,
            }
        }
        Some(values)
    }

    /// Greedily eliminate partners through equalities confirmed affine in the
    /// chosen variable. Blocking keeps the resulting solve chain triangular.
    fn build_elimination(
        &mut self,
        alpha: TermId,
        proxy: &BigRational,
        partners: &[TermId],
        values: &DetHashMap<TermId, BigRational>,
        eqs: &[Equality],
    ) -> Elimination {
        let mut solves = Vec::new();
        let mut solved = DetHashSet::default();
        let mut blocked = DetHashSet::default();
        let mut used = DetHashSet::default();
        loop {
            let mut selected = None;
            'equalities: for (index, eq) in eqs.iter().enumerate() {
                if used.contains(&index) {
                    continue;
                }
                for var in
                    eq.vars.iter().copied().filter(|var| {
                        *var != alpha && !solved.contains(var) && !blocked.contains(var)
                    })
                {
                    let Some(base) = self.probe_base(
                        ProbeContext {
                            alpha,
                            proxy,
                            partners,
                            values,
                            solves: &solves,
                            eqs,
                        },
                        var,
                    ) else {
                        continue;
                    };
                    if self.solve_affine(&base, var, eq).is_some() {
                        selected = Some((index, var));
                        break 'equalities;
                    }
                }
            }
            let Some((index, var)) = selected else {
                break;
            };
            solves.push(Solve { var, eq: index });
            solved.insert(var);
            blocked.extend(eqs[index].vars.iter().copied());
            used.insert(index);
        }
        Elimination {
            solves,
            solved,
            used,
        }
    }

    fn validate_solve_dependencies(&self, solves: &[Solve], eqs: &[Equality]) -> Option<()> {
        for (position, solve) in solves.iter().enumerate() {
            let later: DetHashSet<TermId> = solves[position + 1..]
                .iter()
                .map(|later_solve| later_solve.var)
                .collect();
            if eqs[solve.eq].vars.iter().any(|var| later.contains(var)) {
                return None;
            }
        }
        Some(())
    }

    /// Assignment used only for structure probing, excluding the candidate
    /// variable so its affine samples can be installed independently.
    fn probe_base(
        &mut self,
        context: ProbeContext<'_>,
        exclude: TermId,
    ) -> Option<Vec<(TermId, BigRational)>> {
        let mut base = vec![(context.alpha, context.proxy.clone())];
        for partner in context.partners {
            if *partner == exclude || context.solves.iter().any(|solve| solve.var == *partner) {
                continue;
            }
            base.push((*partner, context.values.get(partner)?.clone()));
        }
        for solve in context.solves {
            if solve.var == exclude {
                continue;
            }
            let value = self.solve_affine(&base, solve.var, &context.eqs[solve.eq])?;
            base.push((solve.var, value));
        }
        Some(base)
    }
}
