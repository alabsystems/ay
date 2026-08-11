// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface roles and aggregate output bounds for trust surgery.

use ay_core::term::TermData;
use ay_core::{Proof, ProofStep, Symbol, TermId, TermStore};

use super::super::proof_trust_surgery_provenance::ProvenanceSurfaceAudit;
use super::{OrTautologyPlan, TautRoute};

pub(super) const MAX_LIVE_PROOF_EDGES: usize = 100_000;
pub(super) const MAX_EMITTED_CLAUSE_WIDTH: usize = 256;

fn eq_top_flip(terms: &TermStore, raw: TermId, canon: TermId) -> bool {
    let (raw, canon) = match (terms.get(raw), terms.get(canon)) {
        (TermData::Not(x), TermData::Not(y)) => (*x, *y),
        _ => (raw, canon),
    };
    match (terms.get(raw), terms.get(canon)) {
        (TermData::App(sa, xa), TermData::App(sb, xb)) => {
            matches!(sa, Symbol::Named(n) if n == "=")
                && sa == sb
                && xa.len() == 2
                && xb.len() == 2
                && xa[0] == xb[1]
                && xa[1] == xb[0]
        }
        _ => false,
    }
}

/// Match the bounded unique raw disjuncts to canonical literals by identity
/// or a top-level binary-equality orientation flip.
pub(super) fn or_perm_lits(
    terms: &TermStore,
    raw: TermId,
    canon: TermId,
) -> Option<Vec<(TermId, TermId)>> {
    if raw == canon {
        return None;
    }
    let (TermData::App(sr, rdis), TermData::App(sc, cdis)) = (terms.get(raw), terms.get(canon))
    else {
        return None;
    };
    if !matches!(sr, Symbol::Named(n) if n == "or")
        || sr != sc
        || rdis.len() > MAX_EMITTED_CLAUSE_WIDTH
        || cdis.len() > MAX_EMITTED_CLAUSE_WIDTH
    {
        return None;
    }
    let (rdis, cdis) = (rdis.clone(), cdis.clone());
    let mut unique = Vec::with_capacity(rdis.len());
    for &literal in &rdis {
        if !unique.contains(&literal) {
            unique.push(literal);
        }
    }
    if unique.len() != cdis.len() {
        return None;
    }
    let mut used = vec![false; cdis.len()];
    let mut aligned = Vec::with_capacity(unique.len());
    for &raw_literal in &unique {
        let slot = cdis
            .iter()
            .enumerate()
            .position(|(index, &canonical)| !used[index] && canonical == raw_literal)
            .or_else(|| {
                cdis.iter().enumerate().position(|(index, &canonical)| {
                    !used[index] && eq_top_flip(terms, raw_literal, canonical)
                })
            })?;
        used[slot] = true;
        aligned.push((raw_literal, cdis[slot]));
    }
    Some(aligned)
}

/// Reachability with an aggregate edge budget. This runs before the consumer
/// map, so no unbounded premise vector can be duplicated there first.
pub(super) fn live_steps(proof: &Proof) -> Option<Vec<bool>> {
    let step_count = proof.steps.len();
    if step_count > MAX_LIVE_PROOF_EDGES {
        return None;
    }
    let mut live = vec![false; step_count];
    let mut stack = Vec::new();
    for (index, step) in proof.steps.iter().enumerate() {
        let empty = match step {
            ProofStep::Step { clause, .. }
            | ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. } => clause.is_empty(),
            ProofStep::Assume(_) | ProofStep::Anchor { .. } => false,
            _ => false,
        };
        if empty && !live[index] {
            live[index] = true;
            stack.push(index);
        }
    }
    let mut edge_work = 0usize;
    while let Some(index) = stack.pop() {
        let mut visit = |premise: ay_core::ProofId| {
            let premise_index = premise.0 as usize;
            if premise_index < step_count && !live[premise_index] {
                live[premise_index] = true;
                stack.push(premise_index);
            }
        };
        match &proof.steps[index] {
            ProofStep::Step { premises, .. } => {
                edge_work = edge_work.checked_add(premises.len())?;
                if edge_work > MAX_LIVE_PROOF_EDGES {
                    return None;
                }
                premises.iter().copied().for_each(&mut visit);
            }
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                edge_work = edge_work.checked_add(2)?;
                if edge_work > MAX_LIVE_PROOF_EDGES {
                    return None;
                }
                visit(*clause1);
                visit(*clause2);
            }
            _ => {}
        }
    }
    Some(live)
}

impl OrTautologyPlan {
    pub(super) fn protect_surface_operands(
        &self,
        audit: &mut ProvenanceSurfaceAudit,
        terms: &mut TermStore,
    ) {
        audit.protect_rigid_operand(terms, self.term);
        audit.protect_rigid_operand(terms, self.eq);
        match &self.route {
            TautRoute::Plain { negs } => {
                for &negated_equality in negs {
                    audit.protect_rigid_operand(terms, negated_equality);
                }
            }
            TautRoute::And {
                and_term,
                conjs,
                per_conj_negs,
            } => {
                audit.protect_rigid_operand(terms, *and_term);
                for &conjunct in conjs {
                    audit.protect_rigid_operand(terms, conjunct);
                }
                for &negated_equality in per_conj_negs.iter().flatten() {
                    audit.protect_rigid_operand(terms, negated_equality);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ay_core::kani_compat::DetHashMap as HashMap;
    use ay_core::{AletheRule, Proof, Sort};
    use ay_frontend::command::Term as FrontendTerm;

    use super::{
        live_steps, OrTautologyPlan, ProvenanceSurfaceAudit, TautRoute, MAX_EMITTED_CLAUSE_WIDTH,
        MAX_LIVE_PROOF_EDGES,
    };
    use crate::executor::Executor;

    #[test]
    fn late_tautology_plan_audits_boolean_equality_surface() {
        let mut executor = Executor::new();
        let a = executor.ctx.terms.mk_var("late_taut_a", Sort::Int);
        let b = executor.ctx.terms.mk_var("late_taut_b", Sort::Int);
        let c = executor.ctx.terms.mk_var("late_taut_c", Sort::Int);
        let ab = executor.ctx.terms.mk_eq(a, b);
        let bc = executor.ctx.terms.mk_eq(b, c);
        let ac = executor.ctx.terms.mk_eq(a, c);
        let not_ab = executor.ctx.terms.mk_not_raw(ab);
        let not_bc = executor.ctx.terms.mk_not_raw(bc);
        let term = executor.ctx.terms.mk_or(vec![ac, not_ab, not_bc]);
        let plan = OrTautologyPlan {
            term,
            eq: ac,
            route: TautRoute::Plain {
                negs: vec![not_ab, not_bc],
            },
        };
        let mut audit = ProvenanceSurfaceAudit::default();
        plan.protect_surface_operands(&mut audit, &mut executor.ctx.terms);
        let mut active = HashMap::default();
        active.insert(not_ab, "(= (= late_taut_a late_taut_b) false)".to_string());
        assert!(!audit.validate_effective(&executor.ctx.terms, &active));
    }

    #[test]
    fn live_edge_budget_rejects_before_consumer_map_growth() {
        let mut executor = Executor::new();
        let atom = executor.ctx.terms.mk_bool(true);
        let mut proof = Proof::new();
        let premise = proof.add_assume(atom, None);
        proof.add_rule_step(
            AletheRule::Resolution,
            Vec::new(),
            vec![premise; MAX_LIVE_PROOF_EDGES + 1],
            Vec::new(),
        );
        assert!(live_steps(&proof).is_none());
    }

    #[test]
    fn transitivity_tautology_declines_wide_clause_before_cloning() {
        let mut executor = Executor::new();
        let vars: Vec<_> = (0..=MAX_EMITTED_CLAUSE_WIDTH)
            .map(|i| {
                executor
                    .ctx
                    .terms
                    .mk_var(format!("wide_taut_{i}"), Sort::Int)
            })
            .collect();
        let mut disjuncts = Vec::with_capacity(MAX_EMITTED_CLAUSE_WIDTH + 1);
        disjuncts.push(executor.ctx.terms.mk_eq(vars[0], vars[vars.len() - 1]));
        for pair in vars.windows(2) {
            let edge = executor.ctx.terms.mk_eq(pair[0], pair[1]);
            disjuncts.push(executor.ctx.terms.mk_not_raw(edge));
        }
        let term = executor.ctx.terms.mk_or(disjuncts);
        assert!(executor.plan_or_transitivity_tautology(&[term]).is_none());
    }

    #[test]
    fn and_distinct_declines_quadratic_pairwise_expansion() {
        let mut executor = Executor::new();
        let vars: Vec<_> = (0..24)
            .map(|i| {
                let name = format!("wide_distinct_{i}");
                executor.ctx.terms.mk_var(name, Sort::Int)
            })
            .collect();
        let mut conjs = Vec::new();
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                let equality = executor.ctx.terms.mk_eq(vars[i], vars[j]);
                conjs.push(executor.ctx.terms.mk_not_raw(equality));
            }
        }
        let term = executor.ctx.terms.mk_and(conjs);
        let operands = (0..vars.len())
            .map(|i| FrontendTerm::Symbol(format!("wide_distinct_{i}")))
            .collect();
        let parsed = FrontendTerm::App(
            "and".to_string(),
            vec![FrontendTerm::App("distinct".to_string(), operands)],
        );
        assert!(executor.classify_assume(term, &parsed, true).is_err());
    }
}
