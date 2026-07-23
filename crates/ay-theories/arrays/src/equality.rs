// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality graph management for the array theory solver.
//!
//! Handles equality adjacency graph construction, incremental updates,
//! affine integer expression parsing, equivalence class caching, and
//! assignment recording.
//!
//! Query methods (known_equal, known_distinct, explanation generation)
//! are in `equality_query`.

use super::*;

impl ArraySolver<'_> {
    /// Return canonically ordered pair (min, max) for symmetric lookups
    pub(crate) fn ordered_pair(a: TermId, b: TermId) -> (TermId, TermId) {
        if a.0 <= b.0 {
            (a, b)
        } else {
            (b, a)
        }
    }

    pub(crate) fn is_equality_term(&self, term: TermId) -> bool {
        matches!(self.terms.get(term), TermData::App(sym, args) if sym.name() == "=" && args.len() == 2)
    }

    pub(crate) fn equality_assignment_affects_eq_graph(
        prev: Option<bool>,
        next: Option<bool>,
    ) -> bool {
        prev == Some(true) || next == Some(true)
    }

    fn warm_assignment_indices_ready(&self, term: TermId) -> bool {
        // The incremental equality-index update (`update_assignment_indices_
        // incrementally`) only touches THIS atom's own `eq_adj`/`shadow_uf`/
        // `diseq_set` entries, keyed by its already-cached `(lhs, rhs)`. It is
        // therefore correct whenever the atom itself is registered (present in
        // `equality_cache`), independent of whether OTHER, higher-id terms are
        // still pending registration (`populated_terms < terms.len()`).
        //
        // Dropping the old `populated_terms == terms.len()` requirement is the
        // delta win (POST-LANDING-REPROFILE §2, i_6): during the lazy Nelson-
        // Oppen loop, lemma instantiation continually appends new terms, so at
        // most `notify_equality()` calls `populated_terms < terms.len()` holds.
        // Under the old guard, EVERY assignment of an OLD (already-registered)
        // equality atom in that window fell to the `assign_dirty` fallback,
        // forcing a full O(#equality-atoms) `rebuild_assign_indices()` on the
        // next `populate_caches()` (measured ~287 µs/call at 4 k atoms, the
        // dominant per-notification cost). Routing it through the incremental
        // path collapses that to an O(1) edge update.
        //
        // Newly-created equality atoms (`term.index() >= populated_terms`) are
        // NOT yet in `equality_cache`, so this still returns false for them and
        // they continue to take the `queue_pending_registered_equality` path,
        // which `populate_caches()` drains via `apply_pending_registered_
        // equalities()` (also incremental). Soundness is guarded byte-for-byte
        // by `debug_assignment_layer_matches_full_rebuild()`, asserted on every
        // mutating `populate_caches()` under `cfg(debug_assertions)`.
        !self.dirty && !self.assign_dirty && self.equality_cache.contains_key(&term)
    }

    pub(crate) fn queue_pending_registered_equality(&mut self, term: TermId) {
        if !self.pending_registered_equalities.contains(&term) {
            self.pending_registered_equalities.push(term);
        }
    }

    pub(crate) fn apply_pending_registered_equalities(&mut self) {
        if self.assign_dirty || self.pending_registered_equalities.is_empty() {
            return;
        }

        let pending = std::mem::take(&mut self.pending_registered_equalities);
        for term in pending {
            debug_assert!(
                self.equality_cache.contains_key(&term),
                "arrays: pending late-registered equality missing from equality_cache"
            );
            if let Some(value) = self.assigns.get(&term).copied() {
                self.update_assignment_indices_incrementally(term, None, Some(value));
            }
        }
    }

    fn remove_eq_adj_edge(
        adj: &mut HashMap<TermId, Vec<(TermId, TermId)>>,
        from: TermId,
        to: TermId,
        eq_term: TermId,
    ) {
        let remove_entry = if let Some(neighbors) = adj.get_mut(&from) {
            neighbors.retain(|&(other, existing_term)| !(other == to && existing_term == eq_term));
            neighbors.is_empty()
        } else {
            false
        };
        if remove_entry {
            adj.remove(&from);
        }
    }

    fn replace_eq_adj_edge(
        adj: &mut HashMap<TermId, Vec<(TermId, TermId)>>,
        from: TermId,
        to: TermId,
        old_eq_term: TermId,
        new_eq_term: TermId,
    ) {
        let Some(neighbors) = adj.get_mut(&from) else {
            return;
        };
        for entry in neighbors.iter_mut() {
            if *entry == (to, old_eq_term) {
                *entry = (to, new_eq_term);
                return;
            }
        }
    }

    fn find_alternative_equality_term(
        &self,
        lhs: TermId,
        rhs: TermId,
        value: bool,
        exclude: TermId,
    ) -> Option<TermId> {
        // Consult the reverse index instead of scanning the whole
        // `equality_cache`: this runs on EVERY equality (un)assignment via
        // `update_assignment_indices_incrementally`, and the full scan was
        // O(#equality atoms) per SAT assignment — 18% of the QF_ALIA
        // pointer-safe-10 solve (2026-07-11 sample profile).
        // `term_to_equalities` is populated/cleared in lockstep with
        // `equality_cache` (see `register_term` / `clear_term_caches`).
        let key = Self::ordered_pair(lhs, rhs);
        let candidates = self.term_to_equalities.get(&lhs)?;
        candidates.iter().copied().find(|&eq_term| {
            eq_term != exclude
                && self.assigns.get(&eq_term) == Some(&value)
                && self
                    .equality_cache
                    .get(&eq_term)
                    .is_some_and(|&(eq_lhs, eq_rhs)| Self::ordered_pair(eq_lhs, eq_rhs) == key)
        })
    }

    pub(crate) fn add_true_equality_edge(&mut self, lhs: TermId, rhs: TermId, eq_term: TermId) {
        self.eq_adj.entry(lhs).or_default().push((rhs, eq_term));
        self.eq_adj.entry(rhs).or_default().push((lhs, eq_term));
        // M1 shadow union-find: mirror every eq_adj edge insertion.
        self.shadow_uf
            .union(lhs, rhs, union_find::EqJustification::Asserted { eq_term });
    }

    fn update_assignment_indices_incrementally(
        &mut self,
        term: TermId,
        prev: Option<bool>,
        next: Option<bool>,
    ) {
        let Some(&(lhs, rhs)) = self.equality_cache.get(&term) else {
            return;
        };
        let key = Self::ordered_pair(lhs, rhs);

        match prev {
            Some(true) if next != Some(true) => {
                // Out-of-order retraction: union-find cannot un-merge outside
                // trail order (and an edge replacement changes the proof-forest
                // justification), so the M1 shadow is rebuilt lazily from the
                // current assignment before its next consistency check.
                self.shadow_uf_stale = true;
                if let Some(replacement) = self.find_alternative_equality_term(lhs, rhs, true, term)
                {
                    Self::replace_eq_adj_edge(&mut self.eq_adj, lhs, rhs, term, replacement);
                    Self::replace_eq_adj_edge(&mut self.eq_adj, rhs, lhs, term, replacement);
                } else {
                    Self::remove_eq_adj_edge(&mut self.eq_adj, lhs, rhs, term);
                    Self::remove_eq_adj_edge(&mut self.eq_adj, rhs, lhs, term);
                }
            }
            Some(false) if next != Some(false) => {
                let has_alternative_false = self
                    .find_alternative_equality_term(lhs, rhs, false, term)
                    .is_some();
                if !has_alternative_false && !self.external_diseqs.contains(&key) {
                    self.diseq_set.remove(&key);
                }
            }
            _ => {}
        }

        match next {
            Some(true)
                if prev != Some(true)
                    && self
                        .find_alternative_equality_term(lhs, rhs, true, term)
                        .is_none() =>
            {
                self.add_true_equality_edge(lhs, rhs, term);
            }
            Some(false) if prev != Some(false) => {
                self.diseq_set.insert(key);
            }
            _ => {}
        }

        if Self::equality_assignment_affects_eq_graph(prev, next) {
            // ROW2 dirty-entry scan: an eq-graph edge at (lhs, rhs) was
            // added/removed/relabeled — wake entries whose select/store views
            // consult the adjacency of either endpoint.
            self.row2_wake_edge_term(lhs);
            self.row2_wake_edge_term(rhs);
            self.note_eq_graph_changed();
        }
        #[cfg(debug_assertions)]
        {
            self.eq_layer_touched_since_populate = true;
        }
    }

    /// M2 read gate: whether the union-find currently mirrors `eq_adj`'s
    /// connected components and may serve equality read paths.
    ///
    /// - `assign_dirty`: the whole equality index set (including `eq_adj`) is
    ///   stale until `rebuild_assign_indices()`; readers that still consult
    ///   `eq_adj` in that state must see the same (stale) picture, so the
    ///   union-find — cleared/rebuilt on a different schedule — stays out.
    /// - `shadow_uf_stale`: an out-of-order retraction removed/replaced an
    ///   `eq_adj` edge that the union-find cannot un-merge; re-synced at the
    ///   next `rebuild_assign_indices()` entry point.
    pub(crate) fn shadow_uf_ready(&self) -> bool {
        !self.assign_dirty && !self.shadow_uf_stale
    }

    pub(crate) fn note_eq_graph_changed(&mut self) {
        self.eq_adj_version = self.eq_adj_version.wrapping_add(1);
        self.equiv_class_cache_version = None;
        self.bump_propagate_state_version();
    }

    /// Invalidate the `propagate_impl()` no-change fast path (see
    /// `last_full_scan_version`). Must be called from EVERY mutation of state
    /// that `propagate_impl` reads: assignments (`record_assignment`),
    /// eq-graph edges (`note_eq_graph_changed`), external (dis)equality and
    /// reason injection (`bridge.rs`), and term-cache rebuilds
    /// (`populate_caches`). Missing a bump risks skipping a scan that would
    /// have produced NEW propagations (a completeness — not soundness —
    /// hazard); when in doubt, bump.
    pub(crate) fn bump_propagate_state_version(&mut self) {
        self.propagate_state_version = self.propagate_state_version.wrapping_add(1);
    }

    fn merge_affine_terms(
        lhs: &mut HashMap<TermId, BigInt>,
        rhs: &HashMap<TermId, BigInt>,
        sign: i32,
    ) {
        for (symbol, coeff) in rhs {
            let signed = if sign >= 0 {
                coeff.clone()
            } else {
                -coeff.clone()
            };
            let entry = lhs.entry(*symbol).or_insert_with(|| BigInt::from(0));
            *entry += signed;
            if *entry == BigInt::from(0) {
                lhs.remove(symbol);
            }
        }
    }

    fn scale_affine(expr: &mut AffineIntExpr, factor: &BigInt) {
        expr.1 *= factor;
        for coeff in expr.0.values_mut() {
            *coeff *= factor;
        }
        expr.0.retain(|_, coeff| *coeff != BigInt::from(0));
    }

    fn parse_affine_int_expr(&self, term: TermId) -> Option<Rc<AffineIntExpr>> {
        if let Some(cached) = self.affine_cache.parse.borrow().get(&term).cloned() {
            return cached;
        }

        let parsed = match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some((HashMap::default(), n.clone())),
            TermData::Var(_, _) => {
                let mut vars = HashMap::default();
                // Variable identity includes the internal declaration
                // identity, not just the user-visible name. In particular,
                // `mk_fresh_named_var` intentionally creates distinct terms
                // when a scoped symbol name is redeclared.
                vars.insert(term, BigInt::from(1));
                Some((vars, BigInt::from(0)))
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    let mut vars = HashMap::default();
                    let mut constant = BigInt::from(0);
                    for &arg in args {
                        let parsed_arg = self.parse_affine_int_expr(arg)?;
                        let (arg_vars, arg_const) = parsed_arg.as_ref();
                        Self::merge_affine_terms(&mut vars, arg_vars, 1);
                        constant += arg_const;
                    }
                    Some((vars, constant))
                }
                "-" if args.len() == 1 => {
                    let mut expr = self.parse_affine_int_expr(args[0])?.as_ref().clone();
                    Self::scale_affine(&mut expr, &BigInt::from(-1));
                    Some(expr)
                }
                "-" if args.len() >= 2 => {
                    let mut expr = self.parse_affine_int_expr(args[0])?.as_ref().clone();
                    for &arg in &args[1..] {
                        let parsed_arg = self.parse_affine_int_expr(arg)?;
                        let (arg_vars, arg_const) = parsed_arg.as_ref();
                        Self::merge_affine_terms(&mut expr.0, arg_vars, -1);
                        expr.1 -= arg_const;
                    }
                    Some(expr)
                }
                "*" => {
                    let mut const_factor = BigInt::from(1);
                    let mut non_constant: Option<AffineIntExpr> = None;
                    for &arg in args {
                        let parsed_arg = self.parse_affine_int_expr(arg)?;
                        let parsed = parsed_arg.as_ref();
                        if parsed.0.is_empty() {
                            const_factor *= &parsed.1;
                        } else if non_constant.is_none() {
                            non_constant = Some(parsed.clone());
                        } else {
                            return None;
                        }
                    }
                    let mut expr = non_constant.unwrap_or((HashMap::default(), BigInt::from(1)));
                    Self::scale_affine(&mut expr, &const_factor);
                    Some(expr)
                }
                _ => None,
            },
            _ => None,
        }
        .map(Rc::new);

        self.affine_cache
            .parse
            .borrow_mut()
            .insert(term, parsed.clone());
        parsed
    }

    /// Intern a canonical affine variable-map to a dense `u32` id.
    ///
    /// The canonical key is the variable/coefficient pairs sorted by exact
    /// variable `TermId` (zero coefficients are already dropped during
    /// parsing by `merge_affine_terms`/`scale_affine`). Interner-key equality
    /// is exact `HashMap` key comparison, so two maps get the same id **iff**
    /// they are structurally equal — collision-free, no hash-digest fallback
    /// needed.
    fn intern_affine_varmap(&self, vars: &HashMap<TermId, BigInt>) -> u32 {
        let mut key: Vec<(TermId, BigInt)> = vars
            .iter()
            .map(|(&term, coeff)| (term, coeff.clone()))
            .collect();
        key.sort_unstable_by_key(|(term, _)| term.0);
        let mut interner = self.affine_cache.interner.borrow_mut();
        if let Some(&id) = interner.get(&key) {
            return id;
        }
        let id = u32::try_from(interner.len()).expect("affine interner id overflow");
        interner.insert(key, id);
        id
    }

    /// Parse `term` to its affine normal form and return `(varmap_id, form)`,
    /// where `varmap_id` is the interned id of the affine variable-part. The id
    /// is memoized per `TermId` so a term is interned at most once. Returns
    /// `None` when `term` is not an affine Int expression.
    fn affine_canonical(&self, term: TermId) -> Option<(u32, Rc<AffineIntExpr>)> {
        let parsed = self.parse_affine_int_expr(term);
        // Read the memoized id in a borrow that ends before any `borrow_mut`
        // below: an `if let ... borrow()` guard would hold the shared borrow
        // across the `else` arm's `borrow_mut`, panicking on re-entrancy.
        let cached = self.affine_cache.varmap_ids.borrow().get(&term).copied();
        let id = if let Some(cached) = cached {
            cached
        } else {
            let id = parsed.as_ref().map(|p| self.intern_affine_varmap(&p.0));
            self.affine_cache.varmap_ids.borrow_mut().insert(term, id);
            id
        };
        match (id, parsed) {
            (Some(id), Some(form)) => Some((id, form)),
            _ => None,
        }
    }

    /// Detect tautological disequalities from affine offset structure:
    /// two affine forms with identical variable coefficients but different
    /// constants (for example `i` vs `i + 1`, `(+ i 1)` vs `(+ i 2)`).
    ///
    /// This is O(1) per call (cached parse) and is needed in the propagation
    /// path where the arithmetic theory may not have propagated disequalities
    /// yet.  The expensive affine BFS (`affine_forms_with_reasons`,
    /// `distinct_by_equality_substituted_affine`) was removed in #6820.
    pub(crate) fn distinct_by_affine_offset(&self, t1: TermId, t2: TermId) -> bool {
        // Pair-result memo: a pure function of the immutable term DAG, probed
        // millions of times by the ROW2 scan on the same few pairs.
        let key = Self::ordered_pair(t1, t2);
        if let Some(&cached) = self.affine_cache.distinct_offset_pairs.borrow().get(&key) {
            return cached;
        }
        let result = 'compute: {
            let Some((id1, lhs)) = self.affine_canonical(t1) else {
                break 'compute false;
            };
            let Some((id2, rhs)) = self.affine_canonical(t2) else {
                break 'compute false;
            };
            // Interned id equality on the variable-part replaces the pairwise
            // `HashMap<TermId, BigInt>` structural walk (`lhs.0 == rhs.0`).
            #[cfg(debug_assertions)]
            Self::debug_assert_affine_intern(id1, id2, lhs.as_ref(), rhs.as_ref());
            id1 == id2 && lhs.1 != rhs.1
        };
        self.affine_cache
            .distinct_offset_pairs
            .borrow_mut()
            .insert(key, result);
        result
    }

    /// Reference oracle (debug builds only): the interned variable-map id
    /// equality must agree byte-for-byte with the structural `HashMap` compare
    /// it replaces. Asserting id-eq ⟺ structural-eq on every affine comparison
    /// call site guarantees the interning introduces no soundness change.
    #[cfg(debug_assertions)]
    fn debug_assert_affine_intern(id1: u32, id2: u32, lhs: &AffineIntExpr, rhs: &AffineIntExpr) {
        debug_assert_eq!(
            id1 == id2,
            lhs.0 == rhs.0,
            "affine varmap interning diverged from structural equality: \
             id-eq {} but structural-eq {}",
            id1 == id2,
            lhs.0 == rhs.0
        );
    }

    /// Detect arithmetic equalities that hold by affine normalization.
    ///
    /// This lets array ROW reasoning treat duplicated arithmetic expressions
    /// (for example two independent `(+ i 1)` terms) as equal even when they
    /// were parsed into distinct TermIds.
    pub(crate) fn equal_by_affine_form(&self, t1: TermId, t2: TermId) -> bool {
        let Some((id1, lhs)) = self.affine_canonical(t1) else {
            return false;
        };
        let Some((id2, rhs)) = self.affine_canonical(t2) else {
            return false;
        };
        // Interned id equality on the variable-part replaces the pairwise
        // `HashMap<TermId, BigInt>` structural walk (`lhs.0 == rhs.0`).
        let result = id1 == id2 && lhs.1 == rhs.1;
        #[cfg(debug_assertions)]
        Self::debug_assert_affine_intern(id1, id2, lhs.as_ref(), rhs.as_ref());
        result
    }

    /// Parse `term` into an affine form over OPAQUE Int leaves (#7956
    /// index-congruence). Where `parse_affine_int_expr` returns `None` on a
    /// UF-application leaf (`(seq_offset a)`), this parser keeps the leaf
    /// opaque, keyed by `TermId`. Returns `None` only for genuinely nonlinear
    /// shapes (a product of two non-constant factors) or non-Int sorts.
    /// Purely structural; memoized cross-round in `affine_cache.opaque_parse`.
    fn parse_affine_opaque(&self, term: TermId) -> Option<Rc<OpaqueAffineExpr>> {
        if let Some(cached) = self.affine_cache.opaque_parse.borrow().get(&term).cloned() {
            return cached;
        }
        let parsed = 'parse: {
            if !matches!(self.terms.sort(term), Sort::Int) {
                break 'parse None;
            }
            match self.terms.get(term) {
                TermData::Const(Constant::Int(n)) => Some((HashMap::default(), n.clone())),
                TermData::App(Symbol::Named(name), args)
                    if matches!(name.as_str(), "+" | "-" | "*") =>
                {
                    match name.as_str() {
                        "+" => {
                            let mut expr: OpaqueAffineExpr = (HashMap::default(), BigInt::from(0));
                            let mut ok = true;
                            for &arg in args {
                                let Some(parsed_arg) = self.parse_affine_opaque(arg) else {
                                    ok = false;
                                    break;
                                };
                                Self::merge_opaque_affine(&mut expr, &parsed_arg, 1);
                            }
                            ok.then_some(expr)
                        }
                        "-" if args.len() == 1 => self.parse_affine_opaque(args[0]).map(|parsed| {
                            let mut expr: OpaqueAffineExpr = (HashMap::default(), BigInt::from(0));
                            Self::merge_opaque_affine(&mut expr, &parsed, -1);
                            expr
                        }),
                        "-" => {
                            let mut expr: OpaqueAffineExpr = (HashMap::default(), BigInt::from(0));
                            let mut ok = false;
                            if let Some(first) = self.parse_affine_opaque(args[0]) {
                                Self::merge_opaque_affine(&mut expr, &first, 1);
                                ok = true;
                                for &arg in &args[1..] {
                                    let Some(parsed_arg) = self.parse_affine_opaque(arg) else {
                                        ok = false;
                                        break;
                                    };
                                    Self::merge_opaque_affine(&mut expr, &parsed_arg, -1);
                                }
                            }
                            ok.then_some(expr)
                        }
                        // "*": only constant × affine stays linear; a product
                        // of two non-constant factors is treated as ONE opaque
                        // leaf (sound: any Int term may be a leaf).
                        _ => {
                            let mut const_factor = BigInt::from(1);
                            let mut non_constant: Option<Rc<OpaqueAffineExpr>> = None;
                            let mut linear = true;
                            for &arg in args {
                                let Some(parsed_arg) = self.parse_affine_opaque(arg) else {
                                    linear = false;
                                    break;
                                };
                                if parsed_arg.0.is_empty() {
                                    const_factor *= &parsed_arg.1;
                                } else if non_constant.is_none() {
                                    non_constant = Some(parsed_arg);
                                } else {
                                    linear = false;
                                    break;
                                }
                            }
                            if linear {
                                let mut expr: OpaqueAffineExpr = non_constant
                                    .map(|rc| rc.as_ref().clone())
                                    .unwrap_or((HashMap::default(), BigInt::from(1)));
                                expr.1 *= &const_factor;
                                for coeff in expr.0.values_mut() {
                                    *coeff *= &const_factor;
                                }
                                expr.0.retain(|_, coeff| *coeff != BigInt::from(0));
                                Some(expr)
                            } else {
                                // Opaque nonlinear leaf.
                                let mut vars = HashMap::default();
                                vars.insert(term, BigInt::from(1));
                                Some((vars, BigInt::from(0)))
                            }
                        }
                    }
                }
                // Every other Int-sorted term (Var, UF application, select,
                // ite, ...) is an opaque leaf.
                _ => {
                    let mut vars = HashMap::default();
                    vars.insert(term, BigInt::from(1));
                    Some((vars, BigInt::from(0)))
                }
            }
        }
        .map(Rc::new);
        self.affine_cache
            .opaque_parse
            .borrow_mut()
            .insert(term, parsed.clone());
        parsed
    }

    fn merge_opaque_affine(target: &mut OpaqueAffineExpr, source: &OpaqueAffineExpr, sign: i32) {
        let sign = BigInt::from(sign);
        for (&leaf, coeff) in &source.0 {
            let entry = target.0.entry(leaf).or_insert_with(|| BigInt::from(0));
            *entry += coeff * &sign;
            if *entry == BigInt::from(0) {
                target.0.remove(&leaf);
            }
        }
        target.1 += &source.1 * &sign;
    }

    /// #7956 index-congruence: explain `t1 = t2` for Int terms whose affine
    /// forms agree MODULO provably-equal opaque leaves.
    ///
    /// SOUNDNESS: with both sides parsed as `Σ c_k·leaf_k + const`, the
    /// difference `t1 − t2` is the linear combination
    /// `Σ c_j·(a_j − b_j) + (const1 − const2)` over the matched leaf pairs
    /// `(a_j, b_j)`. This routine returns `Some(reasons)` only when
    /// `const1 == const2`, every residual leaf is matched against a leaf of
    /// the SAME coefficient on the other side, and each matched pair is
    /// provably equal via the existing BASE explanation machinery
    /// (`explain_equal_if_provable_base`: direct atom / asserted-equality
    /// path / structural affine identity), whose reasons are SAT-visible
    /// asserted equality atoms. Under any assignment satisfying `reasons`,
    /// each `a_j = b_j` holds, so `t1 − t2 = 0` is a linear-arithmetic
    /// identity — `t1 = t2` is entailed. The returned reasons are exactly the
    /// union of the pair explanations, so lemma/conflict consumers stay
    /// well-founded. Base-only leaf explanations keep this non-recursive.
    ///
    /// COMPLETENESS is best-effort by design (greedy exact-coefficient
    /// matching, leaf cap): a `None` here just preserves the pre-existing
    /// behavior.
    pub(crate) fn explain_equal_by_affine_leaf_congruence(
        &self,
        t1: TermId,
        t2: TermId,
    ) -> Option<Vec<TheoryLit>> {
        const MAX_RESIDUAL_LEAVES: usize = 8;
        // Cheap gate: only arithmetic-STRUCTURED shapes can gain anything over
        // the direct checks (two opaque leaves reduce to the direct pair the
        // base machinery already tried).
        let structured = |term: TermId| {
            matches!(
                self.terms.get(term),
                TermData::App(Symbol::Named(name), _) if matches!(name.as_str(), "+" | "-" | "*")
            )
        };
        if !structured(t1) && !structured(t2) {
            return None;
        }
        let p1 = self.parse_affine_opaque(t1)?;
        let p2 = self.parse_affine_opaque(t2)?;
        if p1.1 != p2.1 {
            return None;
        }
        // Residual per-leaf coefficients of `t1 - t2`.
        let mut diff: HashMap<TermId, BigInt> = p1.0.clone();
        for (&leaf, coeff) in &p2.0 {
            let entry = diff.entry(leaf).or_insert_with(|| BigInt::from(0));
            *entry -= coeff;
            if *entry == BigInt::from(0) {
                diff.remove(&leaf);
            }
        }
        if diff.is_empty() {
            // Identical modulo hash-consing — tautological.
            return Some(Vec::new());
        }
        if diff.len() > MAX_RESIDUAL_LEAVES {
            return None;
        }
        let zero = BigInt::from(0);
        let mut pos: Vec<(TermId, BigInt)> = Vec::new();
        let mut neg: Vec<(TermId, BigInt)> = Vec::new();
        for (leaf, coeff) in diff {
            if coeff > zero {
                pos.push((leaf, coeff));
            } else {
                neg.push((leaf, -coeff));
            }
        }
        if pos.len() != neg.len() {
            return None;
        }
        // Deterministic greedy matching (sorted by coefficient then TermId).
        pos.sort_unstable_by(|a, b| a.1.cmp(&b.1).then(a.0 .0.cmp(&b.0 .0)));
        neg.sort_unstable_by(|a, b| a.1.cmp(&b.1).then(a.0 .0.cmp(&b.0 .0)));
        let mut reasons: Vec<TheoryLit> = Vec::new();
        let mut used = vec![false; neg.len()];
        for (a, coeff_a) in &pos {
            let mut matched = false;
            for (j, (b, coeff_b)) in neg.iter().enumerate() {
                if used[j] || coeff_a != coeff_b {
                    continue;
                }
                if let Some(pair_reasons) = self.explain_equal_if_provable_base(*a, *b) {
                    reasons.extend(pair_reasons);
                    used[j] = true;
                    matched = true;
                    break;
                }
            }
            if !matched {
                return None;
            }
        }
        Self::canonicalize_theory_lits(&mut reasons);
        Some(reasons)
    }

    /// Opaque-affine key for `term` with every leaf canonicalised to its
    /// equivalence-class representative. Two Int terms whose difference is a
    /// linear combination of equivalence-class-equal leaves at matching
    /// coefficients (equal constant) map to the SAME key.
    ///
    /// This is the grouping key that captures both `equal_by_affine_form`
    /// (§ soundness case 2) and `explain_equal_by_affine_leaf_congruence`
    /// (§ soundness case 3): see `index_conflict_partition`. Returns `None`
    /// for non-Int terms (where those affine paths cannot fire).
    fn opaque_affine_rep_key(&self, term: TermId) -> Option<(Vec<(u32, BigInt)>, BigInt)> {
        let parsed = self.parse_affine_opaque(term)?;
        let (leaves, constant) = parsed.as_ref();
        // Fold each opaque leaf onto its equivalence-class representative.
        // A base-equality match between two DISTINCT opaque leaves (the only
        // way leaf congruence pairs residual leaves) is provably an
        // equivalence-class equality — distinct opaque leaves are never
        // `equal_by_affine_form` under hash-consing (a variable is keyed by its
        // exact TermId; a compound affine term is never an opaque leaf) — so
        // matched leaves land on the same representative and the
        // per-representative coefficient sums of congruent terms coincide.
        let mut combined: HashMap<u32, BigInt> = HashMap::default();
        for (&leaf, coeff) in leaves {
            let rep = self.equiv_class_representative(leaf).0;
            let entry = combined.entry(rep).or_insert_with(|| BigInt::from(0));
            *entry += coeff;
        }
        let zero = BigInt::from(0);
        let mut key: Vec<(u32, BigInt)> = combined
            .into_iter()
            .filter(|(_, coeff)| *coeff != zero)
            .collect();
        key.sort_unstable_by_key(|entry| entry.0);
        Some((key, constant.clone()))
    }

    /// Partition `indices` (the distinct select-index terms) into blocks such
    /// that any two indices `explain_equal_if_provable` would prove equal share
    /// a block. Returns `index_term -> block representative` (the minimum
    /// `TermId` of the block), with an entry for every input index.
    ///
    /// SOUNDNESS — over-approximation of the index-equality relation `R` that
    /// BOTH select-conflict consumers gate on
    /// (`check_store_permutation_select_conflicts` via
    /// `explain_equal_if_provable`, `row2_extended_conflict_lemmas` via the
    /// weaker `known_equal ⊆ R`). `R(i, j) ⇒ same block`. `R` is exactly the
    /// success set of `explain_equal_if_provable`, which has three paths:
    ///   1. same equivalence class (syntactic identity / directly-asserted
    ///      equality atom / asserted-equality BFS path) — grouped by
    ///      `equiv_class_representative`;
    ///   2. `equal_by_affine_form` (equal interned varmap id AND equal
    ///      constant) — grouped by `affine_canonical`;
    ///   3. `explain_equal_by_affine_leaf_congruence` (opaque-affine forms with
    ///      equal constant whose residual leaves match pairwise via base
    ///      equality at equal coefficients) — grouped by `opaque_affine_rep_key`.
    ///
    /// Each grouping unions its members into one block; the transitive union
    /// (union-find) is only COARSER than `R`, so no `R`-edge is ever split
    /// across blocks (grouping 2 is subsumed by grouping 3 but kept as explicit
    /// insurance). Blocks may also hold indices that are NOT pairwise
    /// `R`-related (over-approximation); the consumers re-check index equality
    /// per candidate pair, so the produced conflicts are byte-identical.
    pub(crate) fn index_conflict_partition(&self, indices: &[TermId]) -> HashMap<TermId, TermId> {
        fn uf_find(parent: &mut [usize], mut x: usize) -> usize {
            while parent[x] != x {
                parent[x] = parent[parent[x]];
                x = parent[x];
            }
            x
        }
        fn uf_union(parent: &mut [usize], a: usize, b: usize) {
            let ra = uf_find(parent, a);
            let rb = uf_find(parent, b);
            if ra != rb {
                // Attach to the smaller root for deterministic forests.
                if ra < rb {
                    parent[rb] = ra;
                } else {
                    parent[ra] = rb;
                }
            }
        }

        let n = indices.len();
        let mut parent: Vec<usize> = (0..n).collect();

        // Grouping (1): equivalence-class representative.
        {
            let mut first_of: HashMap<TermId, usize> = HashMap::default();
            for (i, &t) in indices.iter().enumerate() {
                let rep = self.equiv_class_representative(t);
                match first_of.get(&rep) {
                    Some(&first) => uf_union(&mut parent, first, i),
                    None => {
                        first_of.insert(rep, i);
                    }
                }
            }
        }
        // Grouping (2): affine canonical form (varmap id, constant). This is
        // EXACTLY the pairs `equal_by_affine_form` relates.
        {
            let mut first_of: HashMap<(u32, BigInt), usize> = HashMap::default();
            for (i, &t) in indices.iter().enumerate() {
                if let Some((id, form)) = self.affine_canonical(t) {
                    let key = (id, form.1.clone());
                    match first_of.get(&key) {
                        Some(&first) => uf_union(&mut parent, first, i),
                        None => {
                            first_of.insert(key, i);
                        }
                    }
                }
            }
        }
        // Grouping (3): opaque-affine key with rep-canonicalised leaves. Covers
        // `explain_equal_by_affine_leaf_congruence` (and re-covers grouping 2).
        {
            let mut first_of: HashMap<(Vec<(u32, BigInt)>, BigInt), usize> = HashMap::default();
            for (i, &t) in indices.iter().enumerate() {
                if let Some(key) = self.opaque_affine_rep_key(t) {
                    match first_of.get(&key) {
                        Some(&first) => uf_union(&mut parent, first, i),
                        None => {
                            first_of.insert(key, i);
                        }
                    }
                }
            }
        }

        // Materialise `index -> block representative` (min TermId per block).
        let mut root_min: HashMap<usize, TermId> = HashMap::default();
        for (i, &t) in indices.iter().enumerate() {
            let r = uf_find(&mut parent, i);
            root_min
                .entry(r)
                .and_modify(|m| {
                    if t.0 < m.0 {
                        *m = t;
                    }
                })
                .or_insert(t);
        }
        let mut result: HashMap<TermId, TermId> = HashMap::default();
        for (i, &t) in indices.iter().enumerate() {
            let r = uf_find(&mut parent, i);
            result.insert(t, root_min[&r]);
        }
        result
    }

    /// Rebuild disequality set and adjacency list from current assignments.
    pub(crate) fn rebuild_assign_indices(&mut self) {
        if !self.assign_dirty {
            // M2: an out-of-order equality retraction invalidated the shadow
            // union-find while `eq_adj` stayed incrementally maintained.
            // Re-sync eagerly at this check-cycle entry point so the union-find
            // read paths come back online (cost: one O(#equality atoms) pass,
            // the same as today's `assign_dirty` rebuild; the retraction path
            // is cold — see blueprint §2a).
            if self.shadow_uf_stale {
                self.rebuild_shadow_uf();
            }
            return;
        }

        #[cfg(test)]
        {
            self.assign_index_rebuilds += 1;
        }

        // ROW2 dirty-entry scan: the equality graph is rebuilt wholesale
        // (post-pop or bulk retraction) — every entry's views/probes may have
        // changed, so the incremental watch state is meaningless.
        self.row2_mark_all_dirty();

        self.diseq_set.clear();
        self.eq_adj.clear();
        // M1 shadow union-find: rebuilt in lockstep from the same sorted
        // entries, so the shadow stays deterministic wherever eq_adj is.
        self.shadow_uf.clear();

        // Sort by eq_term for deterministic adjacency/disequality construction (#3060)
        let mut eq_entries: Vec<_> = self.equality_cache.iter().collect();
        eq_entries.sort_by_key(|(&term, _)| term.0);
        for (&eq_term, &(lhs, rhs)) in eq_entries {
            match self.assigns.get(&eq_term) {
                Some(&true) => {
                    self.eq_adj.entry(lhs).or_default().push((rhs, eq_term));
                    self.eq_adj.entry(rhs).or_default().push((lhs, eq_term));
                    self.shadow_uf.union(
                        lhs,
                        rhs,
                        union_find::EqJustification::Asserted { eq_term },
                    );
                }
                Some(&false) => {
                    let key = Self::ordered_pair(lhs, rhs);
                    self.diseq_set.insert(key);
                }
                None => {}
            }
        }

        // Merge external disequalities from combined solver (#4665)
        for &key in &self.external_diseqs {
            self.diseq_set.insert(key);
        }

        // Merge external equalities from combined solver (#4665)
        let sentinel = TermId::SENTINEL;
        for &(t1, t2) in &self.external_eqs {
            self.eq_adj.entry(t1).or_default().push((t2, sentinel));
            self.eq_adj.entry(t2).or_default().push((t1, sentinel));
            let key = Self::ordered_pair(t1, t2);
            self.shadow_uf.union(
                t1,
                t2,
                union_find::EqJustification::External {
                    key,
                    has_reasons: self.external_eq_reasons.contains_key(&key),
                },
            );
        }

        self.pending_registered_equalities.clear();
        self.assign_dirty = false;
        self.shadow_uf_stale = false;
    }

    /// Rebuild the M1 shadow union-find from the current assignment, exactly
    /// as `rebuild_assign_indices` would. Used when an out-of-order equality
    /// retraction (edge removal/replacement) invalidated the shadow while
    /// `eq_adj` was updated incrementally.
    pub(crate) fn rebuild_shadow_uf(&mut self) {
        self.shadow_uf.clear();
        let mut eq_entries: Vec<_> = self.equality_cache.iter().collect();
        eq_entries.sort_by_key(|(&term, _)| term.0);
        for (&eq_term, &(lhs, rhs)) in eq_entries {
            if self.assigns.get(&eq_term) == Some(&true) {
                self.shadow_uf
                    .union(lhs, rhs, union_find::EqJustification::Asserted { eq_term });
            }
        }
        for &(t1, t2) in &self.external_eqs {
            let key = Self::ordered_pair(t1, t2);
            self.shadow_uf.union(
                t1,
                t2,
                union_find::EqJustification::External {
                    key,
                    has_reasons: self.external_eq_reasons.contains_key(&key),
                },
            );
        }
        self.shadow_uf_stale = false;
    }

    /// M1 consistency invariant: the shadow union-find's non-singleton
    /// classes must be exactly the BFS-derived equivalence classes.
    /// Called after `build_equiv_class_cache` rebuilds the eager cache.
    #[cfg(debug_assertions)]
    fn debug_assert_shadow_uf_matches_equiv_classes(&mut self) {
        if self.shadow_uf_stale {
            self.rebuild_shadow_uf();
        }
        let uf_classes = self.shadow_uf.non_singleton_classes();
        let mut bfs_classes: Vec<Vec<TermId>> = self
            .equiv_classes
            .iter()
            .filter(|class| class.len() > 1)
            .map(|class| {
                let mut class = class.clone();
                class.sort_unstable_by_key(|t| t.0);
                class
            })
            .collect();
        bfs_classes.sort_unstable_by_key(|class| class[0].0);
        debug_assert_eq!(
            uf_classes, bfs_classes,
            "arrays M1: shadow union-find partitions must equal BFS equivalence classes"
        );
    }

    /// Compute equivalence classes from eq_adj using connected components.
    /// Reuses the previous cache until the equality graph connectivity changes.
    pub(crate) fn build_equiv_class_cache(&mut self) {
        debug_assert!(
            !self.assign_dirty,
            "arrays: build_equiv_class_cache called before rebuild_assign_indices"
        );
        if self.equiv_class_cache_version == Some(self.eq_adj_version) {
            return;
        }

        self.equiv_class_map.clear();
        self.equiv_classes.clear();

        for &start in self.eq_adj.keys() {
            if self.equiv_class_map.contains_key(&start) {
                continue;
            }
            let class_idx = self.equiv_classes.len();
            let mut class = Vec::new();
            let mut queue = vec![start];

            while let Some(t) = queue.pop() {
                if self.equiv_class_map.contains_key(&t) {
                    continue;
                }
                self.equiv_class_map.insert(t, class_idx);
                class.push(t);
                if let Some(neighbors) = self.eq_adj.get(&t) {
                    for &(other, _) in neighbors {
                        if !self.equiv_class_map.contains_key(&other) {
                            queue.push(other);
                        }
                    }
                }
            }

            self.equiv_classes.push(class);
        }

        self.equiv_class_cache_version = Some(self.eq_adj_version);
        #[cfg(test)]
        {
            self.equiv_class_cache_builds += 1;
        }
        // M1: the shadow union-find must induce exactly these partitions.
        #[cfg(debug_assertions)]
        self.debug_assert_shadow_uf_matches_equiv_classes();
    }

    /// Record an assignment with trail support
    pub(crate) fn record_assignment(&mut self, term: TermId, value: bool) {
        match self.assigns.get(&term).copied() {
            Some(prev) if prev == value => {}
            prev => {
                self.trail.push((term, prev));
                self.assigns.insert(term, value);
                self.bump_propagate_state_version();
                // ROW2 dirty-entry scan: wake entries whose evaluation read
                // this atom's assignment (entry skip condition or probes)
                // and whose wake mask covers this transition.
                self.row2_wake_assign(term, value);
                if self.is_equality_term(term) {
                    if self.warm_assignment_indices_ready(term) {
                        self.update_assignment_indices_incrementally(term, prev, Some(value));
                    } else if !self.dirty
                        && !self.assign_dirty
                        && term.index() >= self.populated_terms
                    {
                        self.queue_pending_registered_equality(term);
                    } else {
                        self.assign_dirty = true;
                        if Self::equality_assignment_affects_eq_graph(prev, Some(value)) {
                            self.note_eq_graph_changed();
                        }
                    }
                    // Event-driven self-store (#6820): when an equality involving
                    // a store term is assigned true, queue for check_self_store.
                    if value {
                        if let Some(&(lhs, rhs)) = self.equality_cache.get(&term) {
                            if self.store_cache.contains_key(&lhs) {
                                self.pending_self_store.push((term, lhs));
                            }
                            if self.store_cache.contains_key(&rhs) {
                                self.pending_self_store.push((term, rhs));
                            }
                            // Event-driven array equality (#6820 Step 4): when an
                            // array equality is assigned true, queue for check_array_equality.
                            if matches!(self.terms.sort(lhs), Sort::Array(_)) {
                                self.pending_array_eqs.push((term, lhs, rhs));
                            }
                        }
                    }
                }
            }
        }
    }
}
