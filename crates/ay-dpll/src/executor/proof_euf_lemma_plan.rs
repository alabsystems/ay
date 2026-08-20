// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded congruence-closure planning for EUF proof reconstruction.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Symbol, TermId, TermStore};
use std::mem::size_of;

use super::{
    decode_eq, CcForest, CcReason, EufConcl, EufJust, EufLemmaPlan, EufTarget, LemmaLits,
    RecipeBuilder,
};
use crate::executor::proof_trust_surgery_provenance::SurgeryPlanningBudget;
use crate::executor::Executor;

/// Congruence reconstruction is deliberately a small proof-repair lane.
const MAX_EUF_LEMMA_LITERALS: usize = 64;

const MAX_EUF_UNIVERSE_TERMS: usize = 4_096;
const MAX_EUF_UNIVERSE_EDGES: usize = 4_096;
const MAX_EUF_TERM_DEPTH: usize = 256;
const MAX_EUF_CC_WORK: usize = 262_144;

fn append_root(roots: &mut Vec<TermId>, term: TermId) -> bool {
    if roots.len() >= MAX_EUF_UNIVERSE_TERMS {
        return false;
    }
    roots.push(term);
    true
}

fn append_predicate_roots(terms: &TermStore, roots: &mut Vec<TermId>, atom: TermId) -> bool {
    let TermData::App(_, args) = terms.get(atom) else {
        return false;
    };
    if args.len() > MAX_EUF_UNIVERSE_TERMS.saturating_sub(roots.len()) {
        return false;
    }
    roots.extend(args.iter().copied());
    true
}

/// Bound every operation that can multiply inside `CcForest::close` before
/// the recursive universe builder or congruence fixpoint is entered.
fn euf_cc_work(terms: &TermStore, split: &LemmaLits) -> Option<usize> {
    let mut roots = Vec::new();
    for &(_, lhs, rhs) in split.hyps.iter().chain(&split.pos_eqs) {
        if !append_root(&mut roots, lhs) || !append_root(&mut roots, rhs) {
            return None;
        }
    }
    for &(_, atom) in &split.neg_preds {
        if !append_predicate_roots(terms, &mut roots, atom) {
            return None;
        }
    }
    for &atom in &split.pos_preds {
        if !append_predicate_roots(terms, &mut roots, atom) {
            return None;
        }
    }

    let root_calls = roots.len();
    let mut pending: Vec<(TermId, usize)> = roots.into_iter().map(|root| (root, 0)).collect();
    let mut seen = HashSet::default();
    let mut nodes = 0usize;
    let mut apps = 0usize;
    let mut edges = 0usize;
    let mut symbol_bytes = 0usize;
    while let Some((term, depth)) = pending.pop() {
        if depth > MAX_EUF_TERM_DEPTH {
            return None;
        }
        if !seen.insert(term) {
            continue;
        }
        nodes = match nodes.checked_add(1) {
            Some(nodes) if nodes <= MAX_EUF_UNIVERSE_TERMS => nodes,
            _ => return None,
        };
        let TermData::App(symbol, args) = terms.get(term) else {
            continue;
        };
        apps = match apps.checked_add(1) {
            Some(apps) if apps <= MAX_EUF_UNIVERSE_TERMS => apps,
            _ => return None,
        };
        edges = match edges.checked_add(args.len()) {
            Some(edges) if edges <= MAX_EUF_UNIVERSE_EDGES => edges,
            _ => return None,
        };
        let app_symbol_bytes = match symbol {
            Symbol::Named(name) => name.len(),
            Symbol::Indexed(name, indices) => name
                .len()
                .saturating_add(indices.len().saturating_mul(size_of::<u32>())),
            _ => return None,
        };
        symbol_bytes = match symbol_bytes.checked_add(app_symbol_bytes) {
            Some(bytes) if bytes <= MAX_EUF_CC_WORK => bytes,
            _ => return None,
        };
        for &child in args {
            pending.push((child, depth + 1));
        }
    }

    // `close` scans every application/argument signature once per fixpoint
    // pass. Each successful pass merges at least one application, so there
    // are at most `apps + 1` passes per hypothesis.
    let close_work = split
        .hyps
        .len()
        .checked_mul(apps.saturating_add(1))
        .and_then(|passes| {
            passes.checked_mul(apps.saturating_add(edges).saturating_add(symbol_bytes))
        })
        .unwrap_or(usize::MAX);
    // Explanation construction can visit a proof-forest path for each
    // application/argument participating in the planned recipe.
    let recipe_work = apps
        .saturating_add(edges)
        .saturating_add(symbol_bytes)
        .saturating_add(1)
        .saturating_mul(nodes.saturating_add(1));
    let union_work = split.hyps.len().saturating_mul(nodes);
    root_calls
        .checked_add(nodes)
        .and_then(|work| work.checked_add(edges))
        .and_then(|work| work.checked_add(close_work))
        .and_then(|work| work.checked_add(recipe_work))
        .and_then(|work| work.checked_add(union_work))
        .filter(|&work| work <= MAX_EUF_CC_WORK)
}

impl Executor {
    /// Recognize an EUF congruence/substitution-chain trust lemma and plan
    /// its certified derivation. `clause` is the trust step's clause; a
    /// single or-term literal is unwrapped to the `OrUnit` target, anything
    /// else is planned as a bare replacement. Fail-closed: `None` on any
    /// unrecognized literal or non-entailed conclusion.
    #[cfg(test)]
    pub(super) fn plan_euf_lemma(&mut self, clause: &[TermId]) -> Option<EufLemmaPlan> {
        self.plan_euf_lemma_inner(clause, None)
    }

    pub(in crate::executor) fn plan_euf_lemma_with_budget(
        &mut self,
        clause: &[TermId],
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<EufLemmaPlan> {
        self.plan_euf_lemma_inner(clause, Some(planning))
    }

    fn plan_euf_lemma_inner(
        &mut self,
        clause: &[TermId],
        planning: Option<&mut SurgeryPlanningBudget>,
    ) -> Option<EufLemmaPlan> {
        if clause.len() > MAX_EUF_LEMMA_LITERALS {
            return None;
        }
        let terms = &self.ctx.terms;
        let (lits, or_term): (Vec<TermId>, Option<TermId>) = if clause.len() == 1 {
            match terms.get(clause[0]) {
                TermData::App(Symbol::Named(op), disjuncts)
                    if op == "or" && disjuncts.len() >= 2 =>
                {
                    if disjuncts.len() > MAX_EUF_LEMMA_LITERALS {
                        return None;
                    }
                    (disjuncts.clone(), Some(clause[0]))
                }
                _ => (clause.to_vec(), None),
            }
        } else {
            (clause.to_vec(), None)
        };
        if lits.len() < 2 {
            return None;
        }
        // A bare replacement must reproduce a distinct-literal multiset.
        if or_term.is_none() {
            for (index, &literal) in lits.iter().enumerate() {
                if lits[index + 1..].contains(&literal) {
                    return None;
                }
            }
        }

        let mut split = LemmaLits {
            hyps: Vec::new(),
            pos_eqs: Vec::new(),
            neg_preds: Vec::new(),
            pos_preds: Vec::new(),
        };
        for &literal in &lits {
            match terms.get(literal) {
                TermData::Not(inner) => {
                    let inner = *inner;
                    if let Some((lhs, rhs)) = decode_eq(terms, inner) {
                        split.hyps.push((literal, lhs, rhs));
                    } else if matches!(terms.get(inner), TermData::App(_, _)) {
                        split.neg_preds.push((literal, inner));
                    } else {
                        return None;
                    }
                }
                _ => {
                    if let Some((lhs, rhs)) = decode_eq(terms, literal) {
                        split.pos_eqs.push((literal, lhs, rhs));
                    } else if matches!(terms.get(literal), TermData::App(_, _)) {
                        split.pos_preds.push(literal);
                    } else {
                        return None;
                    }
                }
            }
        }
        let cc_work = euf_cc_work(terms, &split)?;
        if planning.is_some_and(|budget| !budget.spend_work(cc_work)) {
            return None;
        }

        let mut cc = CcForest::new();
        for &(_, lhs, rhs) in &split.hyps {
            cc.add_universe(terms, lhs);
            cc.add_universe(terms, rhs);
        }
        for &(_, lhs, rhs) in &split.pos_eqs {
            cc.add_universe(terms, lhs);
            cc.add_universe(terms, rhs);
        }
        for &(_, atom) in &split.neg_preds {
            if let TermData::App(_, args) = terms.get(atom) {
                for arg in args.clone() {
                    cc.add_universe(terms, arg);
                }
            }
        }
        for &atom in &split.pos_preds {
            if let TermData::App(_, args) = terms.get(atom) {
                for arg in args.clone() {
                    cc.add_universe(terms, arg);
                }
            }
        }
        for &(literal, lhs, rhs) in &split.hyps {
            cc.union(lhs, rhs, CcReason::Hyp(literal));
            cc.close(terms);
        }

        enum Found {
            Eq(TermId, TermId, TermId),
            Pred(TermId, TermId, TermId, TermId),
        }
        let mut found = None;
        for &(literal, lhs, rhs) in &split.pos_eqs {
            if lhs == rhs || cc.find(lhs) == cc.find(rhs) {
                found = Some(Found::Eq(literal, lhs, rhs));
                break;
            }
        }
        if found.is_none() {
            'outer: for &(neg_literal, neg_atom) in &split.neg_preds {
                let (neg_symbol, neg_args) = match terms.get(neg_atom) {
                    TermData::App(symbol, args) => (symbol.clone(), args.clone()),
                    _ => continue,
                };
                for &pos_literal in &split.pos_preds {
                    let (pos_symbol, pos_args) = match terms.get(pos_literal) {
                        TermData::App(symbol, args) => (symbol.clone(), args.clone()),
                        _ => continue,
                    };
                    if neg_symbol != pos_symbol
                        || neg_args.len() != pos_args.len()
                        || neg_args.is_empty()
                    {
                        continue;
                    }
                    if neg_args
                        .iter()
                        .zip(pos_args.iter())
                        .all(|(&lhs, &rhs)| lhs == rhs || cc.find(lhs) == cc.find(rhs))
                    {
                        found = Some(Found::Pred(neg_literal, pos_literal, neg_atom, pos_literal));
                        break 'outer;
                    }
                }
            }
        }

        // (#ground-conflict-decomp) All-negated-equality conflict: no positive
        // conclusion exists, but the closure merges two DISTINCT integer
        // numerals (e.g. `s[1]=20 ∧ val=1 ∧ … ⊢ 1=20`). Derive the raw
        // numeral equality through the proof forest and refute it with a
        // solver-certified Farkas unit. Bounded: numeral scan over the
        // already-bounded universe.
        let mut const_clash: Option<(TermId, TermId)> = None;
        if found.is_none()
            && split.pos_eqs.is_empty()
            && split.neg_preds.is_empty()
            && split.pos_preds.is_empty()
            && !split.hyps.is_empty()
        {
            let mut numerals: Vec<TermId> = Vec::new();
            for &term in cc.rep.keys() {
                if matches!(terms.get(term), TermData::Const(ay_core::Constant::Int(_)))
                    && !numerals.contains(&term)
                {
                    numerals.push(term);
                }
            }
            'clash: for (index, &c1) in numerals.iter().enumerate() {
                for &c2 in &numerals[index + 1..] {
                    if cc.find(c1) == cc.find(c2) {
                        const_clash = Some((c1, c2));
                        break 'clash;
                    }
                }
            }
        }
        if found.is_none() && const_clash.is_none() {
            return None;
        }

        let mut builder = RecipeBuilder {
            terms: &mut self.ctx.terms,
            cc: &cc,
            derivs: Vec::new(),
            memo: HashMap::default(),
            used_hyps: Vec::new(),
        };
        if found.is_none() {
            let (c1, c2) = const_clash?;
            let EufJust::Derived(top) = builder.derive(c1, c2, None)? else {
                // A direct `(not (= c1 c2))` hypothesis needs no derivation
                // chain; unseen in practice, fail closed.
                return None;
            };
            let eq_term = match &builder.derivs[top] {
                super::EufDeriv::Cong { eq_term, .. } | super::EufDeriv::Chain { eq_term, .. } => {
                    *eq_term
                }
            };
            let unit_lit = builder.terms.mk_not_raw(eq_term);
            let kind = ay_core::TheoryLemmaKind::LiaGeneric;
            let farkas = Some(
                crate::executor::proof_farkas::constant_disequality_unit_farkas(
                    builder.terms,
                    unit_lit,
                )?,
            );
            let RecipeBuilder {
                derivs, used_hyps, ..
            } = builder;
            let target = match or_term {
                Some(term) => EufTarget::OrUnit { term },
                None => {
                    let extras = lits
                        .iter()
                        .copied()
                        .filter(|literal| !used_hyps.contains(literal))
                        .collect();
                    EufTarget::Bare { extras }
                }
            };
            return Some(EufLemmaPlan {
                derivs,
                concl: EufConcl::ConstClash {
                    top,
                    unit_lit,
                    farkas: farkas?,
                    kind,
                },
                target,
            });
        }
        let (conclusion, conclusion_literals) = match found? {
            Found::Eq(literal, lhs, rhs) => {
                if lhs == rhs {
                    (EufConcl::EqRefl { eq_term: literal }, vec![literal])
                } else {
                    let EufJust::Derived(top) = builder.derive(lhs, rhs, Some(literal))? else {
                        return None;
                    };
                    (EufConcl::Eq { top }, vec![literal])
                }
            }
            Found::Pred(neg_literal, pos_literal, neg_atom, pos_atom) => {
                let neg_args = match builder.terms.get(neg_atom) {
                    TermData::App(_, args) => args.clone(),
                    _ => return None,
                };
                let pos_args = match builder.terms.get(pos_atom) {
                    TermData::App(_, args) => args.clone(),
                    _ => return None,
                };
                let mut premises = Vec::with_capacity(neg_args.len());
                for (&lhs, &rhs) in neg_args.iter().zip(pos_args.iter()) {
                    premises.push(builder.derive(lhs, rhs, None)?);
                }
                (
                    EufConcl::Pred {
                        neg_lit: neg_literal,
                        pos_lit: pos_literal,
                        prems: premises,
                    },
                    vec![neg_literal, pos_literal],
                )
            }
        };
        let RecipeBuilder {
            derivs, used_hyps, ..
        } = builder;
        let target = match or_term {
            Some(term) => EufTarget::OrUnit { term },
            None => {
                let mut derived = used_hyps.clone();
                derived.extend(conclusion_literals.iter().copied());
                debug_assert!(derived.iter().all(|literal| lits.contains(literal)));
                let extras = lits
                    .iter()
                    .copied()
                    .filter(|literal| !derived.contains(literal))
                    .collect();
                EufTarget::Bare { extras }
            }
        };
        Some(EufLemmaPlan {
            derivs,
            concl: conclusion,
            target,
        })
    }
}

#[cfg(test)]
mod tests {
    use ay_core::{Sort, Symbol, TermStore};

    use super::{euf_cc_work, LemmaLits, MAX_EUF_LEMMA_LITERALS};
    use crate::executor::proof_trust_surgery_provenance::SurgeryPlanningBudget;
    use crate::executor::Executor;

    #[test]
    fn oversized_or_clause_is_declined_before_unwrap() {
        let mut executor = Executor::new();
        let mut literals = Vec::new();
        for index in 0..=MAX_EUF_LEMMA_LITERALS {
            literals.push(
                executor
                    .ctx
                    .terms
                    .mk_var(format!("euf_width_{index}"), Sort::Bool),
            );
        }
        let wrapped = executor.ctx.terms.mk_or(literals);
        assert!(executor.plan_euf_lemma(&[wrapped]).is_none());
    }

    #[test]
    fn repeated_closure_product_is_bounded() {
        let mut terms = TermStore::new();
        let mut chain = terms.mk_var("euf_work_chain", Sort::Int);
        for _ in 0..220 {
            chain = terms.mk_app(Symbol::named("euf_work_f"), [chain], Sort::Int);
        }
        let mut split = LemmaLits {
            hyps: Vec::new(),
            pos_eqs: Vec::new(),
            neg_preds: Vec::new(),
            pos_preds: Vec::new(),
        };
        for index in 0..4 {
            let rhs = terms.mk_var(format!("euf_work_rhs_{index}"), Sort::Int);
            let equality = terms.mk_eq(chain, rhs);
            let literal = terms.mk_not_raw(equality);
            split.hyps.push((literal, chain, rhs));
        }
        assert!(euf_cc_work(&terms, &split).is_none());
    }

    #[test]
    fn repeated_euf_plans_spend_one_shared_budget() {
        let mut executor = Executor::new();
        let a = executor.ctx.terms.mk_var("euf_budget_a", Sort::Int);
        let b = executor.ctx.terms.mk_var("euf_budget_b", Sort::Int);
        let c = executor.ctx.terms.mk_var("euf_budget_c", Sort::Int);
        let ab = executor.ctx.terms.mk_eq(a, b);
        let bc = executor.ctx.terms.mk_eq(b, c);
        let ac = executor.ctx.terms.mk_eq(a, c);
        let not_ab = executor.ctx.terms.mk_not_raw(ab);
        let not_bc = executor.ctx.terms.mk_not_raw(bc);
        let split = LemmaLits {
            hyps: vec![(not_ab, a, b), (not_bc, b, c)],
            pos_eqs: vec![(ac, a, c)],
            neg_preds: Vec::new(),
            pos_preds: Vec::new(),
        };
        let work = euf_cc_work(&executor.ctx.terms, &split).expect("small EUF work");
        let mut budget = SurgeryPlanningBudget::new();
        budget.set_remaining_work_for_test(work);
        let clause = [ac, not_ab, not_bc];
        assert!(executor
            .plan_euf_lemma_with_budget(&clause, &mut budget)
            .is_some());
        assert!(executor
            .plan_euf_lemma_with_budget(&clause, &mut budget)
            .is_none());
    }
}
