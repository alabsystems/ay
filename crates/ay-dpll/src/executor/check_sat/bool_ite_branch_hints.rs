// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `check_sat.rs` to preserve inherent method paths.

// Bool-valued ITE rewriting and authenticated branch-hint collection.

impl Executor {
    /// Rewrite each assertion that is a Bool-valued `(ite c t e)` — or a
    /// top-level `(and ...)` conjunct that is one — into the logically-identical
    /// `(and (=> c t) (=> (not c) e))`. See the call site in
    /// `check_sat_internal` (#A1-arr-lia561). The rewrite is semantically exact;
    /// it only changes the Boolean structure handed to the solver, never the
    /// formula's models.
    fn rewrite_assertion_bool_ites(&mut self) {
        let asserts = self.ctx.assertions.clone();
        let mut changed = false;
        let new_asserts: Vec<TermId> = asserts
            .iter()
            .map(|&a| match self.ctx.terms.get(a).clone() {
                TermData::Ite(c, t, e) => {
                    changed = true;
                    self.bool_ite_to_and_implies(c, t, e)
                }
                TermData::App(sym, args) if sym.name() == "and" => {
                    let mut conj_changed = false;
                    let new_args: Vec<TermId> = args
                        .iter()
                        .map(|&x| {
                            if let TermData::Ite(c, t, e) = self.ctx.terms.get(x).clone() {
                                conj_changed = true;
                                self.bool_ite_to_and_implies(c, t, e)
                            } else {
                                x
                            }
                        })
                        .collect();
                    if conj_changed {
                        changed = true;
                        self.ctx.terms.mk_and(new_args)
                    } else {
                        a
                    }
                }
                _ => a,
            })
            .collect();
        if changed {
            self.record_named_assert_rewrites(&asserts, &new_asserts);
            self.ctx.assertions = new_asserts;
        }
    }

    /// Build `(and (=> c t) (=> (not c) e))` for a Bool-valued ITE.
    fn bool_ite_to_and_implies(&mut self, c: TermId, t: TermId, e: TermId) -> TermId {
        let not_c = self.ctx.terms.mk_not(c);
        let imp_then = self.ctx.terms.mk_implies(c, t);
        let imp_else = self.ctx.terms.mk_implies(not_c, e);
        // #dt-context-derivation: hint-record the branch consequences so the
        // certification fragment can DERIVE the collapsed branch facts that
        // later surface as stripped level-0 premises. Records grant no
        // authority: sealing re-derives every hint through the bounded ground
        // refuter.
        self.record_bool_ite_branch_hints(c, t, e, imp_then, imp_else);
        self.ctx.terms.mk_and(vec![imp_then, imp_else])
    }

    /// Record authenticated candidates for every reachable branch fact.
    fn record_bool_ite_branch_hints(
        &mut self,
        c: TermId,
        t: TermId,
        e: TermId,
        imp_then: TermId,
        imp_else: TermId,
    ) {
        self.record_bool_ite_top_branch_hints(c, t, imp_then);

        // Each nested arm follows from its own positive guard facts plus the
        // asserted outer else implication. Skipped guards are discharged by
        // constructor clash in the ground refuter.
        let mut covered = self.bool_ite_guard_enum_equalities(c);
        let Some(final_else) = self.record_bool_ite_nested_else_hints(e, imp_else, &mut covered)
        else {
            return;
        };

        self.record_bool_ite_exclusion_hints(t, e, imp_then, imp_else);
        self.record_bool_ite_final_else_hints(final_else, imp_else, &covered);
    }

    fn bool_ite_conjunct_facts(terms: &TermStore, guard: TermId) -> Vec<TermId> {
        match terms.get(guard) {
            TermData::App(sym, args) if sym.name() == "and" && !args.is_empty() => args.clone(),
            _ => vec![guard],
        }
    }

    fn bool_ite_branch_facts(terms: &TermStore, branch: TermId) -> Vec<TermId> {
        let mut facts = vec![branch];
        if let TermData::App(sym, args) = terms.get(branch) {
            if sym.name() == "and" {
                facts.extend(args.iter().copied());
            }
        }
        facts
    }

    /// Recognize `(= C v)` or `(= v C)` for a registered nullary constructor.
    fn bool_ite_enum_equality(&self, conjunct: TermId) -> Option<(String, String, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(conjunct) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        for (constant, variable) in [(args[0], args[1]), (args[1], args[0])] {
            let name = match self.ctx.terms.get(constant) {
                TermData::Var(name, _) => name.clone(),
                TermData::App(inner, inner_args) if inner_args.is_empty() => {
                    inner.name().to_string()
                }
                _ => continue,
            };
            if let Some((datatype, ctor)) = self.ctx.is_constructor(&name) {
                return Some((ctor.to_string(), datatype.to_string(), variable));
            }
        }
        None
    }

    fn bool_ite_guard_enum_equalities(&self, guard: TermId) -> Vec<(String, String, TermId)> {
        Self::bool_ite_conjunct_facts(&self.ctx.terms, guard)
            .into_iter()
            .filter_map(|conjunct| self.bool_ite_enum_equality(conjunct))
            .collect()
    }

    fn record_bool_ite_top_branch_hints(&mut self, guard: TermId, branch: TermId, imply: TermId) {
        if matches!(self.ctx.terms.get(branch), TermData::Ite(_, _, _)) {
            return;
        }
        let guard_facts = Self::bool_ite_conjunct_facts(&self.ctx.terms, guard);
        for fact in Self::bool_ite_branch_facts(&self.ctx.terms, branch) {
            let mut premises = guard_facts.clone();
            premises.push(imply);
            self.record_dt_context_conflict(vec![fact], premises);
        }
    }

    /// Record nested then-arm hints and return the final else, if depth-bounded.
    fn record_bool_ite_nested_else_hints(
        &mut self,
        else_branch: TermId,
        imp_else: TermId,
        covered: &mut Vec<(String, String, TermId)>,
    ) -> Option<TermId> {
        const MAX_CHAIN_DEPTH: usize = 8;
        let mut cursor = else_branch;
        for _ in 0..MAX_CHAIN_DEPTH {
            let TermData::Ite(inner_c, inner_t, inner_e) = self.ctx.terms.get(cursor).clone()
            else {
                return Some(cursor);
            };
            let guard_facts = Self::bool_ite_conjunct_facts(&self.ctx.terms, inner_c);
            covered.extend(
                guard_facts
                    .iter()
                    .filter_map(|&fact| self.bool_ite_enum_equality(fact)),
            );
            if !matches!(self.ctx.terms.get(inner_t), TermData::Ite(_, _, _)) {
                for fact in Self::bool_ite_branch_facts(&self.ctx.terms, inner_t) {
                    let mut premises = guard_facts.clone();
                    premises.push(imp_else);
                    self.record_dt_context_conflict(vec![fact], premises);
                }
            }
            cursor = inner_e;
        }
        None
    }

    fn bool_ite_distinct_leaves(&self, then_branch: TermId, else_branch: TermId) -> Vec<TermId> {
        const MAX_CHAIN_DEPTH: usize = 8;
        let mut leaves = vec![then_branch];
        let mut cursor = else_branch;
        for _ in 0..MAX_CHAIN_DEPTH {
            match self.ctx.terms.get(cursor).clone() {
                TermData::Ite(_, inner_t, inner_e) => {
                    leaves.push(inner_t);
                    cursor = inner_e;
                }
                _ => {
                    leaves.push(cursor);
                    break;
                }
            }
        }
        leaves.dedup();
        let mut distinct = Vec::new();
        for leaf in leaves {
            if !distinct.contains(&leaf) {
                distinct.push(leaf);
            }
        }
        distinct
    }

    /// Record candidates derived by excluding every other distinct leaf.
    fn record_bool_ite_exclusion_hints(
        &mut self,
        then_branch: TermId,
        else_branch: TermId,
        imp_then: TermId,
        imp_else: TermId,
    ) {
        let distinct = self.bool_ite_distinct_leaves(then_branch, else_branch);
        if !(2..=8).contains(&distinct.len()) {
            return;
        }
        for &target in &distinct {
            if matches!(self.ctx.terms.get(target), TermData::Ite(_, _, _)) {
                continue;
            }
            let mut premises = Vec::new();
            for &other in &distinct {
                if other != target {
                    premises.push(self.ctx.terms.mk_not(other));
                }
            }
            premises.extend([imp_then, imp_else]);
            self.record_dt_context_conflict(vec![target], premises);
        }
    }

    /// Record final-else candidates using uncovered siblings of its move enum.
    fn record_bool_ite_final_else_hints(
        &mut self,
        final_else: TermId,
        imp_else: TermId,
        covered: &[(String, String, TermId)],
    ) {
        let Some((_, datatype, variable)) = covered.first() else {
            return;
        };
        let covered_ctors: Vec<&str> = covered.iter().map(|(ctor, _, _)| ctor.as_str()).collect();
        let siblings: Vec<String> = self
            .ctx
            .datatype_iter()
            .find(|(name, _)| *name == datatype.as_str())
            .map(|(_, ctors)| ctors.to_vec())
            .unwrap_or_default();
        let facts = Self::bool_ite_branch_facts(&self.ctx.terms, final_else);
        for sibling in siblings {
            if covered_ctors.contains(&sibling.as_str()) {
                continue;
            }
            let Some(constant) = self.ctx.terms.lookup(&sibling) else {
                continue;
            };
            if self.ctx.terms.sort(constant) != self.ctx.terms.sort(*variable) {
                continue;
            }
            let taken = self.ctx.terms.mk_eq(constant, *variable);
            for &fact in &facts {
                self.record_dt_context_conflict(vec![fact], vec![taken, imp_else]);
            }
        }
    }
}
