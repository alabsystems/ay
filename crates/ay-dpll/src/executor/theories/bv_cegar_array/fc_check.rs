// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Check array functional consistency against a concrete SAT model.
    ///
    /// For each same-array, same-concrete-index group with differing result
    /// values, generate a connected tree of currently violated FC axioms.
    /// Later SAT models are audited again because their indices may differ.
    ///
    /// `already_covered` tracks pairs that have had FC axioms generated
    /// in previous CEGAR iterations to avoid duplicate work.
    ///
    /// Violated read paths of arrays of arrays are refined as well
    /// (`nested_fc.rs`); [`Self::check_array_fc_violations_with`] can leave
    /// them out.
    pub(in crate::executor) fn check_array_fc_violations(
        &mut self,
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        cross_pairs: &[(TermId, TermId, TermId, Option<TermId>)],
        next_var_offset: usize,
        already_covered: &mut HashSet<FcCoverKey>,
    ) -> CegarArrayCheck {
        self.check_array_fc_violations_with(
            sat_model,
            lits,
            cross_pairs,
            next_var_offset,
            already_covered,
            NestedReadPaths::Refine,
        )
    }

    /// [`Self::check_array_fc_violations`], refining nested read paths only
    /// when `nested` asks for it. Their lemmas never decide the verdict on
    /// their own account: a budget stop drops them, and `Consistent` keeps
    /// meaning that the bit-level FC obligation holds.
    pub(in crate::executor) fn check_array_fc_violations_with(
        &mut self,
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        cross_pairs: &[(TermId, TermId, TermId, Option<TermId>)],
        next_var_offset: usize,
        already_covered: &mut HashSet<FcCoverKey>,
        nested: NestedReadPaths,
    ) -> CegarArrayCheck {
        let Some(select_terms) = self.collect_fc_select_terms(lits.term_bits()) else {
            return CegarArrayCheck::Incomplete;
        };
        if select_terms.is_empty() {
            return CegarArrayCheck::Consistent;
        }

        let selects_by_array = Self::group_fc_selects_by_direct_array(&select_terms);
        let Some(initial_next_var) = next_var_offset.checked_add(1) else {
            return CegarArrayCheck::Incomplete;
        };
        let Ok(next_var) = u32::try_from(initial_next_var) else {
            return CegarArrayCheck::Incomplete;
        };
        let mut build = CegarArrayBuild {
            clauses: Vec::new(),
            next_var,
            new_vars: 0,
            inspected_bits: 0,
            pair_attempts: 0,
            newly_covered: HashSet::default(),
            budget_exhausted: false,
        };

        if !self.append_same_base_fc_refinements(
            &selects_by_array,
            sat_model,
            lits,
            already_covered,
            &mut build,
        ) {
            return CegarArrayCheck::Incomplete;
        }

        if !self.append_cross_equality_fc_refinements(
            sat_model,
            lits,
            cross_pairs,
            &selects_by_array,
            already_covered,
            &mut build,
        ) {
            return CegarArrayCheck::Incomplete;
        }

        if nested == NestedReadPaths::Refine {
            self.append_nested_read_path_refinements(
                &select_terms,
                sat_model,
                lits,
                already_covered,
                &mut build,
            );
        }

        if build.clauses.is_empty() {
            // Skipped pairs with nothing emitted: the candidate is
            // NOT audited clean, fail closed. With clauses in hand
            // a budget stop is a partial refinement (below).
            if build.budget_exhausted {
                return CegarArrayCheck::Incomplete;
            }
            return CegarArrayCheck::Consistent;
        }

        already_covered.extend(build.newly_covered);
        CegarArrayCheck::Refinement(CegarArrayResult {
            clauses: build.clauses,
            num_new_vars: build.new_vars,
        })
    }

    /// Unguarded same-direct-operand congruence: selects sharing
    /// one syntactic array root at one concrete index must agree.
    fn append_same_base_fc_refinements(
        &mut self,
        selects_by_array: &HashMap<TermId, Vec<(TermId, TermId)>>,
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        already_covered: &HashSet<FcCoverKey>,
        build: &mut CegarArrayBuild,
    ) -> bool {
        for selects in selects_by_array.values() {
            if selects.len() < 2 {
                continue;
            }

            let Some(concrete_selects) = self.collect_concrete_fc_selects(
                selects,
                sat_model,
                lits,
                &mut build.inspected_bits,
            ) else {
                return false;
            };

            // Group by concrete index value, find violations.
            let mut by_index: HashMap<BigInt, Vec<FcConcreteSelect>> = HashMap::default();
            for concrete in concrete_selects {
                by_index
                    .entry(concrete.index_value.clone())
                    .or_default()
                    .push(concrete);
            }

            for group in by_index.values() {
                if group.len() < 2 {
                    continue;
                }
                let first_value = &group[0].value;
                let has_violation = group
                    .iter()
                    .skip(1)
                    .any(|entry| entry.value != *first_value);
                if !has_violation {
                    continue;
                }

                if !self.append_fc_group_refinement(group, already_covered, build) {
                    return false;
                }
            }
        }
        true
    }

    /// Cross-array congruence through array equalities the candidate
    /// makes true. Reads on two arrays joined by a candidate-true
    /// (possibly nested/reified) equality are never compared by the
    /// direct-operand grouping above, so a candidate can satisfy
    /// the bit-blasted encoding while its own asserted reads
    /// disagree through the equality (the dwp mem-generation idiom:
    /// `(ite (= mem_a mem_b) (= t #b1) (= t #b0))` plus loads on
    /// both). Equality is transitive, so comparison happens per
    /// equality CLASS (union-find over candidate-true edges), not
    /// per edge: in a star `a = b`, `a = c` with no reads on `a` at
    /// the disagreeing index, both edge-wise checks pass while `b`
    /// and `c` disagree. A disagreeing pair refines with the
    /// conditional congruence guarded by every equality atom on a
    /// path between the two arrays. Opportunistic: an equality
    /// whose atom has no literal view is skipped, exactly the
    /// pre-existing behavior.
    fn append_cross_equality_fc_refinements(
        &mut self,
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        cross_pairs: &[(TermId, TermId, TermId, Option<TermId>)],
        selects_by_array: &HashMap<TermId, Vec<(TermId, TermId)>>,
        already_covered: &HashSet<FcCoverKey>,
        build: &mut CegarArrayBuild,
    ) -> bool {
        let edges = self.model_true_array_equalities(sat_model, lits, cross_pairs);
        let (classes, adjacency) = Self::equality_classes(&edges);
        for members in classes {
            let mut merged: Vec<(TermId, TermId)> = Vec::new();
            let mut owner_of: HashMap<TermId, TermId> = HashMap::default();
            for member in &members {
                if let Some(sels) = selects_by_array.get(member) {
                    for &(select, index) in sels {
                        owner_of.insert(select, *member);
                        merged.push((select, index));
                    }
                }
            }
            if owner_of.values().collect::<HashSet<_>>().len() < 2 {
                continue;
            }
            let Some(concrete) = self.collect_concrete_fc_selects(
                &merged,
                sat_model,
                lits,
                &mut build.inspected_bits,
            ) else {
                return false;
            };
            let mut by_index: HashMap<BigInt, Vec<FcConcreteSelect>> = HashMap::default();
            for entry in concrete {
                by_index
                    .entry(entry.index_value.clone())
                    .or_default()
                    .push(entry);
            }
            for (index_value, group) in &by_index {
                if group.len() < 2 {
                    continue;
                }
                if !self.append_fc_class_group_refinement(
                    group,
                    index_value,
                    sat_model,
                    lits,
                    &owner_of,
                    &adjacency,
                    already_covered,
                    build,
                ) {
                    return false;
                }
            }
            if !self.append_fc_stored_value_refinements(
                &by_index,
                &members,
                &edges,
                sat_model,
                lits,
                &owner_of,
                &adjacency,
                already_covered,
                build,
            ) {
                return false;
            }
        }
        true
    }

    /// Union-find classes plus the guard-labeled adjacency of the
    /// candidate-true equality graph. A definition edge carries
    /// its store chain (`Some`) so path refinements can avoid the
    /// chain's stored indices.
    fn equality_classes(
        edges: &[(TermId, TermId, i32, Option<TermId>)],
    ) -> (
        Vec<Vec<TermId>>,
        HashMap<TermId, Vec<(TermId, i32, Option<TermId>)>>,
    ) {
        fn find(parent: &mut HashMap<TermId, TermId>, mut x: TermId) -> TermId {
            let mut root = x;
            while parent[&root] != root {
                root = parent[&root];
            }
            while parent[&x] != root {
                let next = parent[&x];
                parent.insert(x, root);
                x = next;
            }
            root
        }
        let mut parent: HashMap<TermId, TermId> = HashMap::default();
        let mut adjacency: HashMap<TermId, Vec<(TermId, i32, Option<TermId>)>> = HashMap::default();
        for &(a, b, guard, def) in edges {
            parent.entry(a).or_insert(a);
            parent.entry(b).or_insert(b);
            adjacency.entry(a).or_default().push((b, guard, def));
            adjacency.entry(b).or_default().push((a, guard, def));
            let (ra, rb) = (find(&mut parent, a), find(&mut parent, b));
            if ra != rb {
                parent.insert(ra, rb);
            }
        }
        let mut by_root: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for node in adjacency.keys().copied().collect::<Vec<_>>() {
            let root = find(&mut parent, node);
            by_root.entry(root).or_default().push(node);
        }
        (by_root.into_values().collect(), adjacency)
    }

    /// Guard literals (deduplicated) and definition store chains
    /// on a shortest path between two arrays in the equality
    /// graph; `None` when disconnected. `avoid` excludes one edge
    /// (a definition edge whose store is being read over).
    pub(super) fn equality_path_guards(
        adjacency: &HashMap<TermId, Vec<(TermId, i32, Option<TermId>)>>,
        from: TermId,
        to: TermId,
        avoid: Option<(TermId, TermId, Option<TermId>)>,
    ) -> Option<(Vec<i32>, Vec<TermId>)> {
        if from == to {
            return Some((Vec::new(), Vec::new()));
        }
        let mut prev: HashMap<TermId, (TermId, i32, Option<TermId>)> = HashMap::default();
        let mut frontier = vec![from];
        prev.insert(from, (from, 0, None));
        while let Some(node) = frontier.pop() {
            for &(next, guard, def) in adjacency.get(&node)? {
                if avoid.is_some_and(|(x, y, d)| {
                    d == def && ((x == node && y == next) || (x == next && y == node))
                }) {
                    continue;
                }
                if prev.contains_key(&next) {
                    continue;
                }
                prev.insert(next, (node, guard, def));
                if next == to {
                    let mut guards = Vec::new();
                    let mut defs = Vec::new();
                    let mut cur = to;
                    while cur != from {
                        let (p, g, d) = prev[&cur];
                        if !guards.contains(&g) {
                            guards.push(g);
                        }
                        if let Some(chain) = d {
                            if !defs.contains(&chain) {
                                defs.push(chain);
                            }
                        }
                        cur = p;
                    }
                    return Some((guards, defs));
                }
                frontier.push(next);
            }
        }
        None
    }

    /// Class variant of the group refinement: only pairs owned by
    /// different arrays are refined (same-owner pairs are the
    /// direct-operand pass's unguarded business), with value
    /// clauses guarded by the equality path between the owners.
    /// A path through a store-chain definition edge only justifies
    /// congruence AWAY from the chain's stored indices, so such
    /// refinements carry symbolic `idx != stored` guards for every
    /// store on the path (the stored indices are terms whose
    /// values vary across candidates; a concrete-only check would
    /// be unsound).
    fn append_fc_class_group_refinement(
        &mut self,
        group: &[FcConcreteSelect],
        index_value: &BigInt,
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        owner_of: &HashMap<TermId, TermId>,
        adjacency: &HashMap<TermId, Vec<(TermId, i32, Option<TermId>)>>,
        already_covered: &HashSet<FcCoverKey>,
        build: &mut CegarArrayBuild,
    ) -> bool {
        for a in 0..group.len() {
            for b in (a + 1)..group.len() {
                if !self.count_pair_attempt(build) {
                    return false;
                }
                let (left, right) = (&group[a], &group[b]);
                if left.value == right.value || left.select == right.select {
                    continue;
                }
                let (Some(&left_owner), Some(&right_owner)) =
                    (owner_of.get(&left.select), owner_of.get(&right.select))
                else {
                    continue;
                };
                if left_owner == right_owner {
                    continue;
                }
                let Some((guards, defs)) =
                    Self::equality_path_guards(adjacency, left_owner, right_owner, None)
                else {
                    continue;
                };
                let stored_bits = if defs.is_empty() {
                    Vec::new()
                } else {
                    let Some(bits) = self.def_path_stored_bits(
                        sat_model,
                        lits,
                        &defs,
                        index_value,
                        left.index_lits.len(),
                        &mut build.inspected_bits,
                    ) else {
                        continue;
                    };
                    bits
                };
                if !self.append_fc_pair_refinement(
                    left,
                    right,
                    &guards,
                    &stored_bits,
                    already_covered,
                    build,
                ) {
                    return false;
                }
            }
        }
        true
    }

    /// For a refinement whose equality path crosses store-chain
    /// definitions: the stored index bit vectors of every chain
    /// on the path (for symbolic `idx != stored` guards), or
    /// `None` when the group's concrete index IS one of those
    /// stored indices in this candidate (the pair's disagreement
    /// is then legitimate read-over-write, and emitting a dead
    /// instance would poison `already_covered`) or a stored index
    /// has no literal view / concrete value.
    pub(super) fn def_path_stored_bits(
        &mut self,
        sat_model: &[bool],
        lits: &FcAuditLits<'_>,
        defs: &[TermId],
        index_value: &BigInt,
        index_width: usize,
        inspected_bits: &mut usize,
    ) -> Option<Vec<BvBits>> {
        let mut out = Vec::new();
        for &chain in defs {
            for idx_term in Self::fc_store_chain_indices(&self.ctx.terms, chain) {
                let idx_lits = lits.scalar_lits(&self.ctx.terms, idx_term)?;
                if idx_lits.len() != index_width {
                    return None;
                }
                let stored = self.concrete_value_bounded(sat_model, &idx_lits, inspected_bits)?;
                if stored == *index_value {
                    return None;
                }
                out.push(idx_lits);
            }
        }
        Some(out)
    }
}
