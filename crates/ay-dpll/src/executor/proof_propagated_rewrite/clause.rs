// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored-clause, instance-root, and conjunct replay.

use super::*;

pub(super) enum AndPath {
    Found(Vec<u32>),
    Missing,
}

impl PropagationChainPlanner<'_> {
    /// Derive `(cl t)` from authored roots, and-paths, sealed instance roots,
    /// or-fold survivors, or recorded rewrites. `None` fails the plan.
    pub(crate) fn plan_derive_clause(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
    ) -> Option<ProofId> {
        if let Some(&memoized) = cx.clause_memo.get(&term) {
            return Some(memoized);
        }
        cx.spend(1)?;
        if !cx.in_progress.insert(term) {
            return None;
        }
        let result = self.plan_derive_clause_inner(cx, term);
        cx.in_progress.remove(&term);
        if let Some(id) = result {
            cx.clause_memo.insert(term, id);
        }
        result
    }

    fn plan_derive_clause_inner(&mut self, cx: &mut PlanCx<'_>, term: TermId) -> Option<ProofId> {
        if cx.problem_set.contains(&term) {
            return Some(cx.chain.add_assume(term, None));
        }
        let roots = cx.problem_roots.to_vec();
        for root in roots {
            if let Some(id) = self.plan_base_conjunct(cx, root, term) {
                return Some(id);
            }
        }
        if let Some(id) = self.plan_instance_root_base(cx, term) {
            return Some(id);
        }
        let (before, stamp) = *cx.record_by_after.get(&term)?;
        if let Some(before_id) = self.plan_derive_clause(cx, before) {
            if let Some(id) = self.plan_record_bridge(cx, before, before_id, term, stamp) {
                return Some(id);
            }
        }
        let conjuncts = self.plan_collect_authored_conjuncts(cx)?;
        for authored in conjuncts {
            if authored == term {
                continue;
            }
            match self.plan_derive_eq(cx, authored, stamp) {
                Some(EqRes::Changed { to, eq_term, id }) if to == term => {
                    let authored_id = self.plan_derive_clause(cx, authored)?;
                    return Some(self.plan_equiv_bridge(
                        cx,
                        authored,
                        authored_id,
                        term,
                        eq_term,
                        id,
                    ));
                }
                _ => {}
            }
        }
        None
    }

    /// Derive a raw instance, its fold survivor, an and-path conjunct, or an
    /// exact binary-`=` argument swap from sealed instance-root evidence.
    fn plan_instance_root_base(&mut self, cx: &mut PlanCx<'_>, term: TermId) -> Option<ProofId> {
        if cx.instance_roots.is_empty() {
            return None;
        }
        let swapped = match self.terms.get(term) {
            TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2 => {
                let (left, right) = (args[0], args[1]);
                self.terms
                    .find_app_named("=", &[right, left])
                    .filter(|&candidate| candidate != term)
            }
            _ => None,
        };
        let roots = cx.instance_roots;
        for (index, root) in roots.iter().enumerate() {
            if !cx.problem_set.contains(&root.quantifier) {
                continue;
            }
            let (instance, survivor) = (root.instance, root.survivor);
            if term == instance {
                return self.plan_instance_root_clause(cx, index);
            }
            if let AndPath::Found(path) = Self::plan_find_and_path(self.terms, cx, survivor, term)?
            {
                let survivor_id = self.plan_instance_root_survivor(cx, index)?;
                return Some(self.plan_emit_and_pos_chain_from(cx, survivor_id, survivor, &path));
            }
            if let Some(raw) = swapped {
                if let AndPath::Found(path) =
                    Self::plan_find_and_path(self.terms, cx, survivor, raw)?
                {
                    let survivor_id = self.plan_instance_root_survivor(cx, index)?;
                    let raw_id =
                        self.plan_emit_and_pos_chain_from(cx, survivor_id, survivor, &path);
                    let raw_to_term =
                        self.terms
                            .mk_app(Symbol::named("="), [raw, term], Sort::Bool);
                    let symmetric = cx.chain.add_rule_step(
                        AletheRule::EqSymmetric,
                        vec![raw_to_term],
                        Vec::new(),
                        Vec::new(),
                    );
                    return Some(self.plan_equiv_bridge(
                        cx,
                        raw,
                        raw_id,
                        term,
                        raw_to_term,
                        symmetric,
                    ));
                }
            }
        }
        None
    }

    /// `(cl I)` for one sealed instance root via the exact c4 chain.
    fn plan_instance_root_clause(&mut self, cx: &mut PlanCx<'_>, index: usize) -> Option<ProofId> {
        let root = &cx.instance_roots[index];
        let (quantifier, instance) = (root.quantifier, root.instance);
        let values = root.values.clone();
        if let Some(&memoized) = cx.clause_memo.get(&instance) {
            return Some(memoized);
        }
        cx.spend(4)?;
        let source_id = self.plan_assume_root(cx, quantifier);
        let not_quantified = self.terms.mk_not_raw(quantifier);
        let implication =
            self.terms
                .mk_app(Symbol::named("or"), [not_quantified, instance], Sort::Bool);
        let forall_inst = cx.chain.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            Vec::new(),
            values,
        );
        let clausified = cx.chain.add_rule_step(
            AletheRule::Or,
            vec![not_quantified, instance],
            vec![forall_inst],
            Vec::new(),
        );
        let derived = cx
            .chain
            .add_resolution(vec![instance], quantifier, clausified, source_id);
        cx.clause_memo.insert(instance, derived);
        Some(derived)
    }

    /// Resolve every sealed refuted disjunct from a raw instance clause.
    fn plan_instance_root_survivor(
        &mut self,
        cx: &mut PlanCx<'_>,
        index: usize,
    ) -> Option<ProofId> {
        let root = &cx.instance_roots[index];
        let (instance, survivor) = (root.instance, root.survivor);
        let refuted = root.refuted_disjuncts.clone();
        if let Some(&memoized) = cx.clause_memo.get(&survivor) {
            return Some(memoized);
        }
        let instance_id = self.plan_instance_root_clause(cx, index)?;
        if survivor == instance {
            return Some(instance_id);
        }
        let TermData::App(Symbol::Named(name), disjuncts) = self.terms.get(instance) else {
            return None;
        };
        if name != "or" {
            return None;
        }
        let disjuncts = disjuncts.clone();
        let distinct: HashSet<TermId> = disjuncts.iter().copied().collect();
        if distinct.len() != disjuncts.len()
            || disjuncts
                .iter()
                .any(|term| *term != survivor && !refuted.contains(term))
            || !disjuncts.contains(&survivor)
        {
            return None;
        }
        cx.spend(disjuncts.len().checked_add(2 * refuted.len())?)?;
        let clausified = cx.chain.add_rule_step(
            AletheRule::Or,
            disjuncts.clone(),
            vec![instance_id],
            Vec::new(),
        );
        let mut clause = disjuncts;
        let mut current = clausified;
        for disjunct in refuted {
            if !clause.contains(&disjunct) {
                continue;
            }
            let not_disjunct = self.terms.mk_not_raw(disjunct);
            let lemma = cx.chain.add_step(ProofStep::TheoryLemma {
                theory: "theory".to_owned(),
                clause: vec![not_disjunct],
                farkas: None,
                kind: TheoryLemmaKind::BvBitBlast,
                lia: None,
            });
            clause.retain(|&literal| literal != disjunct);
            current = cx
                .chain
                .add_resolution(clause.clone(), disjunct, current, lemma);
        }
        if clause != vec![survivor] {
            return None;
        }
        cx.clause_memo.insert(survivor, current);
        Some(current)
    }

    /// Collect the bounded authored closure used by the respelling fallback.
    fn plan_collect_authored_conjuncts(&mut self, cx: &mut PlanCx<'_>) -> Option<Vec<TermId>> {
        const MAX_AUTHORED_CONJUNCTS: usize = 64;
        let mut out = Vec::new();
        let mut stack = cx.problem_roots.to_vec();
        for root in cx.instance_roots {
            if cx.problem_set.contains(&root.quantifier) {
                stack.push(root.survivor);
            }
        }
        let mut seen = HashSet::default();
        while let Some(term) = stack.pop() {
            cx.spend(1)?;
            if out.len() > MAX_AUTHORED_CONJUNCTS {
                return Some(out);
            }
            if !seen.insert(term) {
                continue;
            }
            if let Some(survivor) = self.plan_or_fold_survivor(cx, term) {
                stack.push(survivor);
            }
            let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
                out.push(term);
                continue;
            };
            if name == "and" {
                stack.extend(args.clone());
            } else {
                out.push(term);
            }
        }
        Some(out)
    }

    fn plan_base_conjunct(
        &mut self,
        cx: &mut PlanCx<'_>,
        root: TermId,
        term: TermId,
    ) -> Option<ProofId> {
        if let AndPath::Found(path) = Self::plan_find_and_path(self.terms, cx, root, term)? {
            let assume_id = self.plan_assume_root(cx, root);
            return Some(self.plan_emit_and_pos_chain(cx, assume_id, root, &path));
        }
        let survivor = self.plan_or_fold_survivor(cx, root)?;
        let AndPath::Found(path) = Self::plan_find_and_path(self.terms, cx, survivor, term)? else {
            return None;
        };
        let assume_id = self.plan_assume_root(cx, root);
        let TermData::App(_, disjuncts) = self.terms.get(root) else {
            return None;
        };
        let clausified = cx.chain.add_rule_step(
            AletheRule::Or,
            disjuncts.clone(),
            vec![assume_id],
            Vec::new(),
        );
        let false_term = self.terms.false_term();
        let false_taut = self.plan_false_taut(cx);
        let survivor_id =
            cx.chain
                .add_resolution(vec![survivor], false_term, clausified, false_taut);
        Some(self.plan_emit_and_pos_chain_from(cx, survivor_id, survivor, &path))
    }

    fn plan_assume_root(&mut self, cx: &mut PlanCx<'_>, root: TermId) -> ProofId {
        if let Some(&memoized) = cx.clause_memo.get(&root) {
            return memoized;
        }
        let id = cx.chain.add_assume(root, None);
        cx.clause_memo.insert(root, id);
        id
    }

    pub(super) fn plan_false_taut(&mut self, cx: &mut PlanCx<'_>) -> ProofId {
        if let Some(id) = cx.false_taut {
            return id;
        }
        let false_term = self.terms.false_term();
        let not_false = self.terms.mk_not_raw(false_term);
        let id = cx
            .chain
            .add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
        cx.false_taut = Some(id);
        id
    }

    fn plan_or_fold_survivor(&self, cx: &mut PlanCx<'_>, term: TermId) -> Option<TermId> {
        cx.spend(1)?;
        let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
            return None;
        };
        if name != "or" || args.len() < 2 {
            return None;
        }
        let mut survivor = None;
        let mut saw_false = false;
        for &arg in args {
            if matches!(self.terms.get(arg), TermData::Const(Constant::Bool(false))) {
                saw_false = true;
                continue;
            }
            match survivor {
                None => survivor = Some(arg),
                Some(existing) if existing == arg => {}
                Some(_) => return None,
            }
        }
        saw_false.then_some(survivor).flatten()
    }

    /// Return a positional and-path, distinguishable from budget exhaustion.
    pub(super) fn plan_find_and_path(
        terms: &TermStore,
        cx: &mut PlanCx<'_>,
        root: TermId,
        target: TermId,
    ) -> Option<AndPath> {
        if root == target {
            return Some(AndPath::Found(Vec::new()));
        }
        cx.spend(1)?;
        let TermData::App(Symbol::Named(name), args) = terms.get(root) else {
            return Some(AndPath::Missing);
        };
        if name != "and" {
            return Some(AndPath::Missing);
        }
        for (index, arg) in args.clone().into_iter().enumerate() {
            if let AndPath::Found(mut path) = Self::plan_find_and_path(terms, cx, arg, target)? {
                path.insert(0, u32::try_from(index).ok()?);
                return Some(AndPath::Found(path));
            }
        }
        Some(AndPath::Missing)
    }

    fn plan_emit_and_pos_chain(
        &mut self,
        cx: &mut PlanCx<'_>,
        assume_id: ProofId,
        root: TermId,
        path: &[u32],
    ) -> ProofId {
        self.plan_emit_and_pos_chain_from(cx, assume_id, root, path)
    }

    pub(super) fn plan_emit_and_pos_chain_from(
        &mut self,
        cx: &mut PlanCx<'_>,
        mut current_id: ProofId,
        mut current_term: TermId,
        path: &[u32],
    ) -> ProofId {
        for &position in path {
            let TermData::App(_, args) = self.terms.get(current_term) else {
                unreachable!("plan_find_and_path returned a non-and path segment");
            };
            let child = args[position as usize];
            let not_parent = self.terms.mk_not_raw(current_term);
            let and_pos = cx.chain.add_rule_step(
                AletheRule::AndPos(position),
                vec![not_parent, child],
                Vec::new(),
                vec![current_term],
            );
            current_id = cx.chain.add_rule_step(
                AletheRule::ThResolution,
                vec![child],
                vec![and_pos, current_id],
                Vec::new(),
            );
            current_term = child;
        }
        current_id
    }

    fn plan_record_bridge(
        &mut self,
        cx: &mut PlanCx<'_>,
        before: TermId,
        before_id: ProofId,
        after: TermId,
        stamp: u32,
    ) -> Option<ProofId> {
        if let Some(EqRes::Changed { to, eq_term, id }) = self.plan_derive_eq(cx, before, stamp) {
            if to == after {
                return Some(self.plan_equiv_bridge(cx, before, before_id, after, eq_term, id));
            }
        }
        if let Some(id) = self.plan_or_elimination_bridge(cx, before, before_id, after, stamp) {
            return Some(id);
        }
        self.plan_and_elimination_bridge(cx, before, before_id, after, stamp)
    }
}
