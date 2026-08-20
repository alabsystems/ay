// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Derive the unit clause `(cl (= left right))` inside `candidate` and
    /// return the step together with the EXACT equality term it proves.
    ///
    /// Four lanes, each closed by a rule `ay-proof` re-derives from the clause
    /// alone — nothing here is taken on the producer's word:
    ///
    /// 1. the same term on both sides: [`TheoryLemmaKind::EufReflexive`];
    /// 2. an exact authored equality: an `assume` inside the authored scope;
    /// 3. two authored equalities meeting at one shared term:
    ///    [`TheoryLemmaKind::EufTransitive`], whose validator searches the
    ///    premise graph for a path from the conclusion's lhs to its rhs ITSELF,
    ///    so a chain that does not actually connect is rejected there;
    /// 4. a bitvector identity: [`TheoryLemmaKind::BvBitBlast`], whose
    ///    validator re-derives the unit by exhaustive bounded evaluation or by
    ///    replaying a surfaced bit-blast/LRAT refutation — a near-miss whose
    ///    two sides CAN differ is falsified by some assignment and rejected;
    /// 5. CONGRUENCE over the two sides' shared symbol, recursively (bounded
    ///    depth): [`TheoryLemmaKind::EufCongruent`].
    fn derive_equality_unit(
        &mut self,
        candidate: &mut Proof,
        left: TermId,
        right: TermId,
        authored_equalities: &[(TermId, TermId, TermId)],
    ) -> Option<DerivedUnit> {
        self.derive_equality_unit_at_depth(candidate, left, right, authored_equalities, 0)
    }

    /// [`Self::derive_equality_unit`] with the congruence-recursion depth made
    /// explicit. `depth` bounds how many nested `EufCongruent` lifts one
    /// derivation may stack (`f(select(a, x))` vs `f(select(a, y))` needs two).
    fn derive_equality_unit_at_depth(
        &mut self,
        candidate: &mut Proof,
        left: TermId,
        right: TermId,
        authored_equalities: &[(TermId, TermId, TermId)],
        depth: u32,
    ) -> Option<DerivedUnit> {
        /// Work bound on lane 5's recursion.
        const MAX_CONGRUENCE_DEPTH: u32 = 2;

        if self.ctx.terms.sort(left) != self.ctx.terms.sort(right) {
            return None;
        }
        if left == right {
            let equality = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [left, right], Sort::Bool);
            let step = candidate.add_theory_lemma_with_kind(
                "euf",
                vec![equality],
                TheoryLemmaKind::EufReflexive,
            );
            return Some(DerivedUnit {
                step,
                literal: equality,
            });
        }
        if let Some(&(root, _, _)) = authored_equalities
            .iter()
            .find(|&&(_, a, b)| (a == left && b == right) || (a == right && b == left))
        {
            let step = candidate.add_assume(root, None);
            return Some(DerivedUnit {
                step,
                literal: root,
            });
        }
        for &(left_root, left_a, left_b) in authored_equalities {
            let Some(shared) = pair_other_side_local(left_a, left_b, left) else {
                continue;
            };
            if shared == left || shared == right {
                continue;
            }
            for &(right_root, right_a, right_b) in authored_equalities {
                if right_root == left_root
                    || pair_other_side_local(right_a, right_b, right) != Some(shared)
                {
                    continue;
                }
                let equality = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), [left, right], Sort::Bool);
                let left_negated = self.ctx.terms.mk_not_raw(left_root);
                let right_negated = self.ctx.terms.mk_not_raw(right_root);
                let lemma = candidate.add_theory_lemma_with_kind(
                    "euf",
                    vec![left_negated, right_negated, equality],
                    TheoryLemmaKind::EufTransitive,
                );
                let left_assume = candidate.add_assume(left_root, None);
                let partial = candidate.add_resolution(
                    vec![right_negated, equality],
                    left_root,
                    lemma,
                    left_assume,
                );
                let right_assume = candidate.add_assume(right_root, None);
                let step =
                    candidate.add_resolution(vec![equality], right_root, partial, right_assume);
                return Some(DerivedUnit {
                    step,
                    literal: equality,
                });
            }
        }
        if matches!(self.ctx.terms.sort(left), Sort::BitVec(_)) {
            let equality = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [left, right], Sort::Bool);
            if ay_proof::recognize_bv_bitblast(&self.ctx.terms, &[equality]) {
                let step = candidate.add_theory_lemma_with_kind(
                    "bv",
                    vec![equality],
                    TheoryLemmaKind::BvBitBlast,
                );
                return Some(DerivedUnit {
                    step,
                    literal: equality,
                });
            }
        }
        if depth < MAX_CONGRUENCE_DEPTH {
            return self.derive_congruence_unit_at_depth(
                candidate,
                left,
                right,
                authored_equalities,
                depth + 1,
            );
        }
        None
    }

    /// Derive the unit clause `(cl (not (= left right)))` inside `candidate`
    /// and return the step together with the EXACT negated-equality term it
    /// proves.
    ///
    /// Three lanes, each closed by a rule `ay-proof` re-derives from the clause
    /// alone:
    ///
    /// 1. an exact authored disequality: an `assume` inside the authored scope;
    /// 2. a bitvector disequality [`TheoryLemmaKind::BvBitBlast`] re-derives
    ///    directly (two ground constants, or two terms no assignment equates);
    /// 3. one or both sides pinned by an authored equality to a bitvector
    ///    CONSTANT the recognizer can separate: the
    ///    [`TheoryLemmaKind::EufTransitive`] chain
    ///    `anchor_l — left — right — anchor_r` reduces the goal to the constant
    ///    disequality, which [`TheoryLemmaKind::BvBitBlast`] closes. A
    ///    near-miss whose anchors CAN be equal is falsified there.
    pub(super) fn derive_disequality_unit(
        &mut self,
        candidate: &mut Proof,
        left: TermId,
        right: TermId,
        authored: &[TermId],
        authored_equalities: &[(TermId, TermId, TermId)],
    ) -> Option<DerivedUnit> {
        /// Work bound on lane 4. Each authored disequality it considers costs
        /// one bounded bit-blast decision; declining the rest leaves today's
        /// behaviour exactly as it is.
        const MAX_IMPLYING_DISEQUALITIES: usize = 8;

        if left == right || self.ctx.terms.sort(left) != self.ctx.terms.sort(right) {
            return None;
        }
        for &root in authored {
            let TermData::Not(inner) = self.ctx.terms.get(root).clone() else {
                continue;
            };
            if equality_matches_pair_local(&self.ctx.terms, inner, left, right) {
                let step = candidate.add_assume(root, None);
                return Some(DerivedUnit {
                    step,
                    literal: root,
                });
            }
        }
        // Every remaining lane is closed by the bit-blast recognizer, which
        // only decides Bool/BV clauses.
        if !matches!(self.ctx.terms.sort(left), Sort::BitVec(_)) {
            return None;
        }
        let equality = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [left, right], Sort::Bool);
        let disequality = self.ctx.terms.mk_not_raw(equality);
        if ay_proof::recognize_bv_bitblast(&self.ctx.terms, &[disequality]) {
            let step = candidate.add_theory_lemma_with_kind(
                "bv",
                vec![disequality],
                TheoryLemmaKind::BvBitBlast,
            );
            return Some(DerivedUnit {
                step,
                literal: disequality,
            });
        }
        // Anchor each side to a bitvector CONSTANT the problem pins it to. The
        // constant filter is a cheap NECESSARY condition that bounds how much
        // recognizer work one candidate can buy; it decides nothing about the
        // schema, which `ay-proof` re-derives from the clause.
        'anchor: {
            let anchor_of = |terms: &TermStore, side: TermId| -> Option<(TermId, TermId)> {
                authored_equalities.iter().find_map(|&(root, a, b)| {
                    let other = pair_other_side_local(a, b, side)?;
                    Self::is_bitvec_constant(terms, other).then_some((root, other))
                })
            };
            let left_anchor = if Self::is_bitvec_constant(&self.ctx.terms, left) {
                None
            } else {
                anchor_of(&self.ctx.terms, left)
            };
            let right_anchor = if Self::is_bitvec_constant(&self.ctx.terms, right) {
                None
            } else {
                anchor_of(&self.ctx.terms, right)
            };
            if left_anchor.is_none() && right_anchor.is_none() {
                // No authored edge to add: lane 2 already decided this pair.
                break 'anchor;
            }
            if let (Some((left_root, _)), Some((right_root, _))) = (left_anchor, right_anchor) {
                if left_root == right_root {
                    break 'anchor;
                }
            }
            let anchor_left = left_anchor.map_or(left, |(_, constant)| constant);
            let anchor_right = right_anchor.map_or(right, |(_, constant)| constant);
            let anchor_equality =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [anchor_left, anchor_right], Sort::Bool);
            let anchor_disequality = self.ctx.terms.mk_not_raw(anchor_equality);
            if !ay_proof::recognize_bv_bitblast(&self.ctx.terms, &[anchor_disequality]) {
                break 'anchor;
            }

            let mut clause = Vec::with_capacity(4);
            if let Some((root, _)) = left_anchor {
                clause.push(self.ctx.terms.mk_not_raw(root));
            }
            clause.push(disequality);
            if let Some((root, _)) = right_anchor {
                clause.push(self.ctx.terms.mk_not_raw(root));
            }
            clause.push(anchor_equality);
            let mut chain = candidate.add_theory_lemma_with_kind(
                "euf",
                clause.clone(),
                TheoryLemmaKind::EufTransitive,
            );
            let mut remaining = clause;
            for anchor in [left_anchor, right_anchor] {
                let Some((root, _)) = anchor else {
                    continue;
                };
                let negated = self.ctx.terms.mk_not_raw(root);
                let position = remaining.iter().position(|&literal| literal == negated)?;
                let _ = remaining.remove(position);
                let assume = candidate.add_assume(root, None);
                chain = candidate.add_resolution(remaining.clone(), root, chain, assume);
            }
            if remaining != vec![disequality, anchor_equality] {
                return None;
            }
            let constant_lemma = candidate.add_theory_lemma_with_kind(
                "bv",
                vec![anchor_disequality],
                TheoryLemmaKind::BvBitBlast,
            );
            let step =
                candidate.add_resolution(vec![disequality], anchor_equality, chain, constant_lemma);
            return Some(DerivedUnit {
                step,
                literal: disequality,
            });
        }
        // LANE 4 — an authored BITVECTOR disequality that IMPLIES this one, as
        // a two-literal clause the bit-blast recognizer re-derives:
        // `(cl (= len #x00000000) (not (= ((_ zero_extend 32) len) #x0…0)))`
        // is a tautology, so `len != 0` yields `zext(len) != 0`. The recognizer
        // decides the implication; nothing about it is asserted here.
        for &root in authored.iter().take(MAX_IMPLYING_DISEQUALITIES) {
            let TermData::Not(inner) = self.ctx.terms.get(root).clone() else {
                continue;
            };
            let Some((inner_lhs, inner_rhs)) = decode_eq_local(&self.ctx.terms, inner) else {
                continue;
            };
            if !matches!(self.ctx.terms.sort(inner_lhs), Sort::BitVec(_))
                || self.ctx.terms.sort(inner_lhs) != self.ctx.terms.sort(inner_rhs)
                || inner == equality
            {
                continue;
            }
            if !ay_proof::recognize_bv_bitblast(&self.ctx.terms, &[inner, disequality]) {
                continue;
            }
            let lemma = candidate.add_theory_lemma_with_kind(
                "bv",
                vec![inner, disequality],
                TheoryLemmaKind::BvBitBlast,
            );
            let assume = candidate.add_assume(root, None);
            let step = candidate.add_resolution(vec![disequality], inner, lemma, assume);
            return Some(DerivedUnit {
                step,
                literal: disequality,
            });
        }
        None
    }

    /// Derive the unit clause `(cl (= lhs rhs))` by CONGRUENCE inside
    /// `candidate`, discharging each argument position with
    /// [`Self::derive_equality_unit`].
    ///
    /// The sibling of [`Self::derive_authored_congruence_unit`], which only
    /// accepts an EXACT authored equality (or syntactic identity) per position.
    /// This one also admits the transitive and bit-blast lanes, so a read whose
    /// index is `(bvadd j #x00)` can be lifted onto the same read at `j`. The
    /// emitted clause is re-decided by the strict `EufCongruent` validator,
    /// which requires exactly one negated-equality premise per argument
    /// position, each connecting that position's two arguments.
    pub(super) fn derive_congruence_unit(
        &mut self,
        candidate: &mut Proof,
        lhs: TermId,
        rhs: TermId,
        authored_equalities: &[(TermId, TermId, TermId)],
    ) -> Option<DerivedUnit> {
        self.derive_congruence_unit_at_depth(candidate, lhs, rhs, authored_equalities, 0)
    }

    /// [`Self::derive_congruence_unit`] with the recursion depth made explicit.
    fn derive_congruence_unit_at_depth(
        &mut self,
        candidate: &mut Proof,
        lhs: TermId,
        rhs: TermId,
        authored_equalities: &[(TermId, TermId, TermId)],
        depth: u32,
    ) -> Option<DerivedUnit> {
        /// Work bound. Each position costs one derivation attempt; declining an
        /// oversized application leaves the verdict exactly as it is today.
        const MAX_CONGRUENCE_ARITY: usize = 8;

        if lhs == rhs {
            return None;
        }
        let (lhs_symbol, lhs_args) = as_app_local(&self.ctx.terms, lhs)?;
        let (rhs_symbol, rhs_args) = as_app_local(&self.ctx.terms, rhs)?;
        if lhs_symbol != rhs_symbol
            || lhs_args.len() != rhs_args.len()
            || lhs_args.is_empty()
            || lhs_args.len() > MAX_CONGRUENCE_ARITY
        {
            return None;
        }
        let mut premises: Vec<DerivedUnit> = Vec::with_capacity(lhs_args.len());
        for (&left_arg, &right_arg) in lhs_args.iter().zip(rhs_args.iter()) {
            premises.push(self.derive_equality_unit_at_depth(
                candidate,
                left_arg,
                right_arg,
                authored_equalities,
                depth,
            )?);
        }
        let congruence_equality = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
        let mut clause: Vec<TermId> = premises
            .iter()
            .map(|premise| self.ctx.terms.mk_not_raw(premise.literal))
            .collect();
        clause.push(congruence_equality);
        let mut current = candidate.add_theory_lemma_with_kind(
            "euf",
            clause.clone(),
            TheoryLemmaKind::EufCongruent,
        );
        let mut remaining = clause;
        for premise in &premises {
            let negated = self.ctx.terms.mk_not_raw(premise.literal);
            let position = remaining.iter().position(|&literal| literal == negated)?;
            let _ = remaining.remove(position);
            current =
                candidate.add_resolution(remaining.clone(), premise.literal, current, premise.step);
        }
        if remaining != vec![congruence_equality] {
            return None;
        }
        Some(DerivedUnit {
            step: current,
            literal: congruence_equality,
        })
    }

    /// Rebuild an ARRAY READ-OVER-WRITE VALUE-CONFLICT refutation directly from
    /// exact authored roots (#trust-count→0, the QF_ABV/QF_AUFBV
    /// store-then-read family).
    ///
    /// The problem writes one cell and then reads a cell whose address it pins
    /// — equal to the written address, or provably different from it — and
    /// contradicts what the write forces there, e.g.
    ///
    /// ```text
    /// (assert (= i #x05)) (assert (= j #x06))
    /// (assert (= (select a j) #xAA))
    /// (assert (= (select (store a i v) j) #xBB))
    /// ```
    ///
    /// z3 5.0.0 answers `unsat` and AY computes that verdict every time. The
    /// eager array lane closes the search by level-0 propagation, so no
    /// clause-level conflict reaches the SAT trace,
    /// `derive_empty_via_level0_rup` declines with `RupNoConflict`, and the
    /// reconstruction falls through to the whole-problem `trust` closer.
    /// Discharging THAT clause is re-proving the problem, so the deferred-trust
    /// rescue cannot help either, and the mandatory certification gate turns a
    /// correct `unsat` into `unknown`.
    ///
    /// [`Self::replace_with_exact_authored_array_row2_refutation`] covers only
    /// the shape whose index disequality AND whose two read indices are
    /// authored VERBATIM (`base_read_index != read_index` → continue). This
    /// pass derives them instead, and every fact it uses is a rule `ay-proof`
    /// re-derives from the clause alone:
    ///
    /// * [`TheoryLemmaKind::ArraySelectStore`] — the ROW1/ROW2 axiom, matched
    ///   by the checker's own `validate_array_select_store` (the exact
    ///   two-literal guarded schema, or the unit whose write and read indices
    ///   are the SAME term);
    /// * [`TheoryLemmaKind::EufCongruent`] / [`TheoryLemmaKind::EufReflexive`]
    ///   to lift a read from an array VARIABLE onto the store term the problem
    ///   asserts it equal to, and to lift the base read onto an index ALIAS;
    /// * [`TheoryLemmaKind::EufTransitive`], whose validator searches the
    ///   premise graph for a path from the conclusion's lhs to its rhs ITSELF;
    /// * [`TheoryLemmaKind::BvBitBlast`], whose validator re-derives an index
    ///   identity or a value disequality by exhaustive bounded evaluation or by
    ///   replaying a surfaced bit-blast/LRAT refutation.
    ///
    /// Fail-closed at every step, mirroring
    /// [`Self::replace_with_exact_authored_store_permutation_refutation`]: it
    /// runs only on a proof the strict checker already rejects; every `assume`
    /// is an exact authored root; and [`Self::commit_if_strictly_checked`]
    /// requires `validate_reachable_assumes_in_problem_scope`,
    /// `proof_derives_empty_clause` AND the plain
    /// `check_proof_strict_with_datatypes` before anything is replaced. A
    /// mis-recognition therefore costs completeness (the verdict stays
    /// `unknown`) and can never cost soundness.
    pub(super) fn replace_with_exact_authored_array_row_value_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        /// Work bound on the authored-equality scan. Declining an oversized
        /// problem leaves today's behaviour exactly as it is.
        const MAX_AUTHORED_EQUALITIES: usize = 64;
        /// Work bound on the `select` subterms one problem contributes.
        const MAX_SELECT_TERMS: usize = 32;
        /// Work bound on candidate rebuilds. Only a candidate that survives
        /// every derivation reaches the (expensive) strict replay.
        const MAX_CANDIDATES: usize = 128;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        let reads = collect_select_terms_local(&self.ctx.terms, &authored, MAX_SELECT_TERMS);
        if reads.is_empty() {
            return;
        }
        let authored_equalities: Vec<(TermId, TermId, TermId)> = authored
            .iter()
            .filter_map(|&root| {
                decode_eq_local(&self.ctx.terms, root).map(|(lhs, rhs)| (root, lhs, rhs))
            })
            .collect();
        if authored_equalities.len() > MAX_AUTHORED_EQUALITIES {
            return;
        }

        let mut attempts = 0_usize;
        for &read in &reads {
            attempts += 1;
            if attempts > MAX_CANDIDATES {
                return;
            }
            if self.try_authored_array_row_candidate(
                proof,
                &authored,
                &authored_equalities,
                &reads,
                read,
            ) {
                return;
            }
        }
    }

    /// Walk the store chain under ONE authored read, trying after every step to
    /// close the refutation, for
    /// [`Self::replace_with_exact_authored_array_row_value_refutation`].
    ///
    /// The walk is greedy and deterministic: at each `(select A K)` it finds a
    /// `store` for `A` (named directly, or reached through one authored array
    /// equality), and takes the ROW1 step when `K` is provably the written
    /// index and the ROW2 step when it is provably not. ROW1 ends the walk at
    /// the written VALUE; ROW2 continues at the base array's read.
    ///
    /// Returns `false` — leaving `proof` and the verdict exactly as they were —
    /// when no prefix of the walk yields a refutation the strict checker
    /// accepts.
    fn try_authored_array_row_candidate(
        &mut self,
        proof: &mut Proof,
        authored: &[TermId],
        authored_equalities: &[(TermId, TermId, TermId)],
        reads: &[TermId],
        read: TermId,
    ) -> bool {
        /// Work bound on the store-chain walk. A longer chain simply leaves the
        /// verdict as it is.
        const MAX_ROW_STEPS: usize = 8;

        let mut candidate = Proof::new();
        // Equality edges connecting the authored read to the term the writes
        // force it to equal, in read-to-value order.
        let mut edges: Vec<(TermId, ProofId)> = Vec::new();
        let mut current = read;
        let mut visited: Vec<TermId> = vec![read];

        for _ in 0..=MAX_ROW_STEPS {
            if self.close_authored_array_row_chain(
                proof,
                &candidate,
                &edges,
                authored,
                authored_equalities,
                reads,
                read,
                current,
            ) {
                return true;
            }
            let Some(next) = self.extend_authored_array_row_chain(
                &mut candidate,
                &mut edges,
                authored,
                authored_equalities,
                current,
            ) else {
                // The index comparison at `current` is INDETERMINATE — neither
                // provably equal nor provably distinct. The chain can still
                // close when BOTH read-over-write branches reach the same
                // authored-refuted target (the ghost-pair shape:
                // `a2 = store(a, n, 0)`, `select(a, k) = 0`,
                // `not (select(a2, k) = 0)` with `k` vs `n` unconstrained).
                return self.close_authored_array_row_case_split(
                    proof,
                    &candidate,
                    &edges,
                    authored,
                    authored_equalities,
                    read,
                    current,
                );
            };
            if visited.contains(&next) {
                return false;
            }
            visited.push(next);
            current = next;
        }
        false
    }

    /// Take ONE read-over-write step from `current`, appending its equality
    /// edge (and any congruence lift onto the store term) to `edges`, and
    /// return the term the step reaches.
    ///
    /// The ROW1/ROW2 choice is made by the checker-side recognizers reached
    /// through [`Self::derive_equality_unit`] /
    /// [`Self::derive_disequality_unit`]: an index the problem cannot separate
    /// from — or identify with — the written one ends the walk.
    fn extend_authored_array_row_chain(
        &mut self,
        candidate: &mut Proof,
        edges: &mut Vec<(TermId, ProofId)>,
        authored: &[TermId],
        authored_equalities: &[(TermId, TermId, TermId)],
        current: TermId,
    ) -> Option<TermId> {
        let (array, index) = select_parts_local(&self.ctx.terms, current)?;
        // The array under the read reaches a `store` either directly or through
        // ONE authored array equality.
        let mut routes: Vec<TermId> = Vec::new();
        if store_parts_local(&self.ctx.terms, array).is_some() {
            routes.push(array);
        }
        for &(_, lhs, rhs) in authored_equalities {
            for (alias, store_term) in [(lhs, rhs), (rhs, lhs)] {
                if alias == array
                    && alias != store_term
                    && store_parts_local(&self.ctx.terms, store_term).is_some()
                    && !routes.contains(&store_term)
                {
                    routes.push(store_term);
                }
            }
        }

        for store_term in routes {
            let Some((base, store_index, store_value)) =
                store_parts_local(&self.ctx.terms, store_term)
            else {
                continue;
            };
            // Staged so a route that fails half-way leaves the CHAIN intact;
            // the unreferenced steps it added stay valid and unused.
            let mut staged: Vec<(TermId, ProofId)> = Vec::with_capacity(2);
            let value_sort = self.ctx.terms.sort(current).clone();
            let store_read = self.ctx.terms.mk_app(
                Symbol::named("select"),
                [store_term, index],
                value_sort.clone(),
            );
            if store_read != current {
                let Some(lift) = self.derive_congruence_unit(
                    candidate,
                    current,
                    store_read,
                    authored_equalities,
                ) else {
                    continue;
                };
                staged.push((lift.literal, lift.step));
            }

            // ROW1 — the read address is provably the written one.
            let row1_equality =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [store_read, store_value], Sort::Bool);
            if store_index == index {
                let step = candidate.add_theory_lemma_with_kind(
                    "array",
                    vec![row1_equality],
                    TheoryLemmaKind::ArraySelectStore { index_eq: true },
                );
                staged.push((row1_equality, step));
                edges.extend(staged);
                return Some(store_value);
            }
            if let Some(index_unit) =
                self.derive_equality_unit(candidate, store_index, index, authored_equalities)
            {
                let guard = self.ctx.terms.mk_not_raw(index_unit.literal);
                let lemma = candidate.add_theory_lemma_with_kind(
                    "array",
                    vec![guard, row1_equality],
                    TheoryLemmaKind::ArraySelectStore { index_eq: true },
                );
                let step = candidate.add_resolution(
                    vec![row1_equality],
                    index_unit.literal,
                    lemma,
                    index_unit.step,
                );
                staged.push((row1_equality, step));
                edges.extend(staged);
                return Some(store_value);
            }

            // ROW2 — the read address is provably NOT the written one.
            let Some(index_unit) = self.derive_disequality_unit(
                candidate,
                store_index,
                index,
                authored,
                authored_equalities,
            ) else {
                continue;
            };
            let TermData::Not(index_equality) = self.ctx.terms.get(index_unit.literal).clone()
            else {
                continue;
            };
            let base_read =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("select"), [base, index], value_sort);
            let row2_equality =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [store_read, base_read], Sort::Bool);
            let lemma = candidate.add_theory_lemma_with_kind(
                "array",
                vec![index_equality, row2_equality],
                TheoryLemmaKind::ArraySelectStore { index_eq: false },
            );
            let step = candidate.add_resolution(
                vec![row2_equality],
                index_equality,
                lemma,
                index_unit.step,
            );
            staged.push((row2_equality, step));
            edges.extend(staged);
            return Some(base_read);
        }
        None
    }

    /// Close the chain built so far: state `(= read final)` by
    /// [`TheoryLemmaKind::EufTransitive`] over `edges` and refute it.
    ///
    /// `final` is `current` itself, or any authored read of the SAME array at
    /// an ALIASING index, reached by one more congruence lift. Each attempt
    /// works on a CLONE of the chain, so a failed close leaves the walk exactly
    /// as it was.
    #[allow(clippy::too_many_arguments)]
    fn close_authored_array_row_chain(
        &mut self,
        proof: &mut Proof,
        chain: &Proof,
        edges: &[(TermId, ProofId)],
        authored: &[TermId],
        authored_equalities: &[(TermId, TermId, TermId)],
        reads: &[TermId],
        read: TermId,
        current: TermId,
    ) -> bool {
        let mut finals: Vec<TermId> = vec![current];
        if let Some((current_array, _)) = select_parts_local(&self.ctx.terms, current) {
            for &alias in reads {
                if alias != current
                    && select_parts_local(&self.ctx.terms, alias)
                        .is_some_and(|(alias_array, _)| alias_array == current_array)
                {
                    finals.push(alias);
                }
            }
        }

        for final_term in finals {
            let mut candidate = chain.clone();
            let mut candidate_edges = edges.to_vec();
            if final_term != current {
                let Some(alias) = self.derive_congruence_unit(
                    &mut candidate,
                    current,
                    final_term,
                    authored_equalities,
                ) else {
                    continue;
                };
                candidate_edges.push((alias.literal, alias.step));
            }
            if candidate_edges.is_empty() {
                continue;
            }
            let Some(conflict) = self.derive_disequality_unit(
                &mut candidate,
                read,
                final_term,
                authored,
                authored_equalities,
            ) else {
                continue;
            };
            let TermData::Not(conflict_equality) = self.ctx.terms.get(conflict.literal).clone()
            else {
                continue;
            };

            let mut clause: Vec<TermId> = candidate_edges
                .iter()
                .map(|&(equality, _)| self.ctx.terms.mk_not_raw(equality))
                .collect();
            clause.push(conflict_equality);
            let mut resolved = candidate.add_theory_lemma_with_kind(
                "euf",
                clause.clone(),
                TheoryLemmaKind::EufTransitive,
            );
            let mut remaining = clause;
            let mut discharged = true;
            for &(equality, support) in &candidate_edges {
                let negated = self.ctx.terms.mk_not_raw(equality);
                let Some(position) = remaining.iter().position(|&literal| literal == negated)
                else {
                    discharged = false;
                    break;
                };
                let _ = remaining.remove(position);
                resolved = candidate.add_resolution(remaining.clone(), equality, resolved, support);
            }
            if !discharged || remaining != vec![conflict_equality] {
                continue;
            }
            candidate.add_resolution(Vec::new(), conflict_equality, resolved, conflict.step);

            if self.commit_if_strictly_checked(proof, candidate, authored) {
                return true;
            }
        }
        false
    }

    /// Close an indeterminate-index read-over-write by CASE SPLIT: both ROW
    /// branches must chain to one authored-refuted target.
    ///
    /// For `current = select(A0, k)` with `A0` reaching `store(base, w, v)`
    /// (directly or through one authored array equality) and `(= w k)`
    /// underivable in either direction, derive per branch:
    ///
    /// - TRUE  (`w = k`): `select(store, k) = v`   and `v = t`;
    /// - FALSE (`w != k`): `select(store, k) = select(base, k)` and
    ///   `select(base, k) = t`;
    ///
    /// with `t` drawn from an authored disequality against `read`. Each branch
    /// then resolves through an [`TheoryLemmaKind::EufTransitive`] chain and
    /// the guarded [`TheoryLemmaKind::ArraySelectStore`] lemma to the unit
    /// `[not (w = k)]` / `[(w = k)]`, and the two units resolve to the empty
    /// clause. Nothing is taken on the producer's word: every lemma kind here
    /// is re-derived by `ay-proof` from its clause alone, and only
    /// [`Self::commit_if_strictly_checked`] can publish the candidate.
    #[allow(clippy::too_many_arguments)]
    fn close_authored_array_row_case_split(
        &mut self,
        proof: &mut Proof,
        chain: &Proof,
        edges: &[(TermId, ProofId)],
        authored: &[TermId],
        authored_equalities: &[(TermId, TermId, TermId)],
        read: TermId,
        current: TermId,
    ) -> bool {
        /// Work bound on authored-disequality targets per store route.
        const MAX_SPLIT_TARGETS: usize = 8;

        let Some((array, index)) = select_parts_local(&self.ctx.terms, current) else {
            return false;
        };
        let mut routes: Vec<TermId> = Vec::new();
        if store_parts_local(&self.ctx.terms, array).is_some() {
            routes.push(array);
        }
        for &(_, lhs, rhs) in authored_equalities {
            for (alias, store_term) in [(lhs, rhs), (rhs, lhs)] {
                if alias == array
                    && alias != store_term
                    && store_parts_local(&self.ctx.terms, store_term).is_some()
                    && !routes.contains(&store_term)
                {
                    routes.push(store_term);
                }
            }
        }

        // Targets: the other side of an authored disequality against `read`.
        let mut targets: Vec<TermId> = Vec::new();
        for &root in authored {
            let TermData::Not(inner) = self.ctx.terms.get(root).clone() else {
                continue;
            };
            let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, inner) else {
                continue;
            };
            let Some(other) = pair_other_side_local(lhs, rhs, read) else {
                continue;
            };
            if !targets.contains(&other) {
                targets.push(other);
            }
            if targets.len() >= MAX_SPLIT_TARGETS {
                break;
            }
        }
        if targets.is_empty() {
            return false;
        }

        for store_term in routes {
            let Some((base, store_index, store_value)) =
                store_parts_local(&self.ctx.terms, store_term)
            else {
                continue;
            };
            let value_sort = self.ctx.terms.sort(current).clone();
            let store_read = self.ctx.terms.mk_app(
                Symbol::named("select"),
                [store_term, index],
                value_sort.clone(),
            );
            let base_read =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("select"), [base, index], value_sort.clone());
            let split = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [store_index, index], Sort::Bool);
            let not_split = self.ctx.terms.mk_not_raw(split);
            let row1_equality =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [store_read, store_value], Sort::Bool);
            let row2_equality =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [store_read, base_read], Sort::Bool);

            for &target in &targets {
                let mut candidate = chain.clone();
                let mut shared_edges = edges.to_vec();
                if store_read != current {
                    let Some(lift) = self.derive_congruence_unit(
                        &mut candidate,
                        current,
                        store_read,
                        authored_equalities,
                    ) else {
                        break;
                    };
                    shared_edges.push((lift.literal, lift.step));
                }
                let Some(conflict) = self.derive_disequality_unit(
                    &mut candidate,
                    read,
                    target,
                    authored,
                    authored_equalities,
                ) else {
                    continue;
                };
                let TermData::Not(conflict_equality) = self.ctx.terms.get(conflict.literal).clone()
                else {
                    continue;
                };
                // A branch endpoint that IS the target needs no bridge —
                // and must not get one: the EufTransitive validator rejects
                // redundant premise equalities.
                let value_unit = if store_value == target {
                    None
                } else {
                    match self.derive_equality_unit(
                        &mut candidate,
                        store_value,
                        target,
                        authored_equalities,
                    ) {
                        Some(unit) => Some(unit),
                        None => continue,
                    }
                };
                let base_unit = if base_read == target {
                    None
                } else {
                    match self.derive_equality_unit(
                        &mut candidate,
                        base_read,
                        target,
                        authored_equalities,
                    ) {
                        Some(unit) => Some(unit),
                        None => continue,
                    }
                };

                let row1_lemma = candidate.add_theory_lemma_with_kind(
                    "array",
                    vec![not_split, row1_equality],
                    TheoryLemmaKind::ArraySelectStore { index_eq: true },
                );
                let row2_lemma = candidate.add_theory_lemma_with_kind(
                    "array",
                    vec![split, row2_equality],
                    TheoryLemmaKind::ArraySelectStore { index_eq: false },
                );

                // One branch: transitive chain read = .. = store_read,
                // store_read = branch_read, branch_read .. = target, refuted
                // by the authored conflict, discharged down to the bare split
                // guard unit.
                let mut branch = |row_equality: TermId,
                                  row_lemma: ProofId,
                                  bridge: Option<&DerivedUnit>,
                                  guard: TermId,
                                  candidate: &mut Proof|
                 -> Option<ProofId> {
                    let mut clause: Vec<TermId> = shared_edges
                        .iter()
                        .map(|&(equality, _)| self.ctx.terms.mk_not_raw(equality))
                        .collect();
                    clause.push(self.ctx.terms.mk_not_raw(row_equality));
                    if let Some(bridge) = bridge {
                        clause.push(self.ctx.terms.mk_not_raw(bridge.literal));
                    }
                    clause.push(conflict_equality);
                    let mut resolved = candidate.add_theory_lemma_with_kind(
                        "euf",
                        clause.clone(),
                        TheoryLemmaKind::EufTransitive,
                    );
                    let mut remaining = clause;
                    for &(equality, support) in &shared_edges {
                        let negated = self.ctx.terms.mk_not_raw(equality);
                        let position = remaining.iter().position(|&literal| literal == negated)?;
                        let _ = remaining.remove(position);
                        resolved = candidate.add_resolution(
                            remaining.clone(),
                            equality,
                            resolved,
                            support,
                        );
                    }
                    if let Some(bridge) = bridge {
                        let negated_bridge = self.ctx.terms.mk_not_raw(bridge.literal);
                        let position = remaining
                            .iter()
                            .position(|&literal| literal == negated_bridge)?;
                        let _ = remaining.remove(position);
                        resolved = candidate.add_resolution(
                            remaining.clone(),
                            bridge.literal,
                            resolved,
                            bridge.step,
                        );
                    }
                    // Discharge the row equality against the guarded lemma:
                    // [.. not(row_eq) .. conflict_eq] x [guard, row_eq].
                    let negated_row = self.ctx.terms.mk_not_raw(row_equality);
                    let position = remaining
                        .iter()
                        .position(|&literal| literal == negated_row)?;
                    let _ = remaining.remove(position);
                    let mut with_guard = remaining.clone();
                    with_guard.insert(0, guard);
                    resolved = candidate.add_resolution(
                        with_guard.clone(),
                        row_equality,
                        resolved,
                        row_lemma,
                    );
                    // Refute the conclusion with the authored conflict.
                    let position = with_guard
                        .iter()
                        .position(|&literal| literal == conflict_equality)?;
                    let mut guard_only = with_guard;
                    let _ = guard_only.remove(position);
                    Some(candidate.add_resolution(
                        guard_only,
                        conflict_equality,
                        conflict.step,
                        resolved,
                    ))
                };

                let Some(true_unit) = branch(
                    row1_equality,
                    row1_lemma,
                    value_unit.as_ref(),
                    not_split,
                    &mut candidate,
                ) else {
                    continue;
                };
                let Some(false_unit) = branch(
                    row2_equality,
                    row2_lemma,
                    base_unit.as_ref(),
                    split,
                    &mut candidate,
                ) else {
                    continue;
                };
                candidate.add_resolution(Vec::new(), split, true_unit, false_unit);

                if self.commit_if_strictly_checked(proof, candidate, authored) {
                    return true;
                }
            }
        }
        false
    }
}
