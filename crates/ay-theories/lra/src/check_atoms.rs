// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Atom processing helpers for `LraSolver::check()`.
//!
//! Extracted from the check() method to reduce theory_solver.rs size.
//! Contains: incremental atom trail processing, disequality collection,
//! to_int axiom injection, and post-simplex propagation orchestration.

use super::*;

/// Result of processing newly-asserted atoms in check().
pub(crate) struct CheckAtomStats {
    /// Disequality atoms collected for post-simplex checking.
    pub disequalities: Vec<(TermId, LinearExpr, bool)>,
    /// Number of atoms successfully parsed and asserted.
    pub parsed_count: usize,
    /// Number of atoms skipped (unparseable or Boolean combinations).
    pub skipped_count: usize,
}

impl LraSolver {
    /// Process newly-asserted atoms from the trail, assert bounds into the
    /// simplex tableau, and collect disequality atoms.
    ///
    /// First pass: iterate new atoms (since last check), parse them, assert
    /// bounds, and collect disequalities.
    /// Second pass: collect prior disequalities from the incremental trail.
    ///
    /// Returns `Err(conflict)` if an immediate conflict is detected (e.g.,
    /// asserting `true` as `false`). Otherwise returns statistics and
    /// collected disequalities for post-simplex checking.
    pub(crate) fn process_check_atoms(
        &mut self,
        debug: bool,
    ) -> Result<CheckAtomStats, Box<TheoryResult>> {
        self.process_check_atoms_inner(debug, false)
    }

    /// BCP-time variant: skip re-collecting previously asserted disequalities.
    /// The final full check handles disequality/model-only work.
    ///
    /// #8255: Fast-path when no new atoms have been asserted since the last
    /// check. The asserted_trail hasn't grown, so the for-loop in
    /// process_check_atoms_inner iterates 0 times. Skip the function call
    /// entirely to avoid Vec allocations and the disequality-trail skip logic.
    pub(crate) fn process_check_atoms_bcp(
        &mut self,
        debug: bool,
    ) -> Result<CheckAtomStats, Box<TheoryResult>> {
        if self.last_check_trail_pos >= self.asserted_trail.len() {
            return Ok(CheckAtomStats {
                disequalities: Vec::new(),
                parsed_count: 0,
                skipped_count: 0,
            });
        }
        self.process_check_atoms_inner(debug, true)
    }

    fn process_check_atoms_inner(
        &mut self,
        debug: bool,
        bcp_mode: bool,
    ) -> Result<CheckAtomStats, Box<TheoryResult>> {
        let new_start = self.last_check_trail_pos;
        let trail_len = self.asserted_trail.len();

        let mut parsed_count = 0;
        let mut skipped_count = 0;
        let mut _cache_hits = 0;
        // #8255: Per-check cascade budget. Instead of allowing cascade_rounds
        // per atom (O(atoms * cascade_rounds * rows * width)), cap the total
        // compute_implied_bounds calls across ALL atoms in a single check.
        // The post-simplex fixpoint loop in run_post_simplex_propagation()
        // catches any cascades missed by the per-atom budget.
        //
        // Budget: 32 for small problems (< 200 rows), 16 for medium (200-499),
        // 0 for large (500+, already skipped). This replaces the per-atom cap
        // while preserving the same maximum cascade depth for single-atom checks.
        let cascade_budget_max: u32 = if bcp_mode {
            if self.max_row_width > 50 || self.rows.len() >= 500 {
                0
            } else if self.rows.len() < 200 {
                32
            } else {
                16
            }
        } else if self.rows.len() < 200 {
            // Full-check mode: generous budget since it runs once per split-loop.
            64
        } else {
            32
        };
        let mut cascade_budget_remaining: u32 = cascade_budget_max;
        // #9217: Track the earliest trail position of an atom skipped due to
        // has_unsupported=true. These atoms must be re-processed on the next
        // check() call because ITE conditions that were unknown at parse time
        // may become available later when the SAT solver assigns them.
        // Without this, last_check_trail_pos advances past unsupported atoms,
        // preventing re-parsing and leaving the theory permanently in Unknown.
        let mut earliest_unsupported_skip: Option<usize> = None;
        // Track disequalities for post-simplex checking.
        // Stores (term, expr, asserted_value) where asserted_value is the value the term was asserted with.
        // Disequalities must be re-collected from ALL asserted atoms (not just new ones)
        // because they are model-dependent and not cached in bound_atoms.
        let mut disequalities: Vec<(TermId, LinearExpr, bool)> = Vec::new();

        // First pass: process NEW atoms for bound assertions + disequality collection
        for i in new_start..trail_len {
            let term = self.asserted_trail[i];
            let Some(&value) = self.asserted.get(&term) else {
                continue;
            };

            // Skip atoms whose bounds have already been asserted into the tableau
            // (can happen if the same atom is re-asserted within the same scope).
            if self.bound_atoms.contains(&(term, value)) {
                continue;
            }

            // Handle constant Bool atoms (e.g., term layer folds `X = X` to `true`).
            // Asserting `true` as false (or `false` as true) is an immediate contradiction.
            // Uses const_bool_cache from register_atom (#6590 Packet 1); falls back
            // to self.terms on cache miss for atoms registered before caching was added.
            let is_const_bool = self
                .const_bool_cache
                .get(&term)
                .copied()
                .unwrap_or_else(|| {
                    if let TermData::Const(Constant::Bool(b)) = self.terms().get(term) {
                        Some(*b)
                    } else {
                        None
                    }
                });
            if let Some(b) = is_const_bool {
                if value != b {
                    self.stats.conflict_count += 1;
                    return Err(Box::new(TheoryResult::Unsat(vec![TheoryLit {
                        term,
                        value,
                    }])));
                }
                continue;
            }

            // Use cached parse result if available
            let cached = self.atom_cache.get(&term).cloned();
            let parsed_info = match cached {
                Some(info) => {
                    // #8373: Re-parse atoms whose cached result has unsupported
                    // sub-expressions (typically ITE conditions that were unknown
                    // at registration time). Now that ITE conditions have been
                    // forwarded to self.asserted via the DPLL extension layer,
                    // re-parsing may resolve the ITEs to their correct branches
                    // instead of over-approximating as fresh variables.
                    //
                    // The atom_cache stores the parse result from register_atom(),
                    // which runs before any trail processing. At that point,
                    // self.asserted is empty, so parse_linear_expr creates fresh
                    // variables for ITE sub-expressions. This cache is never
                    // invalidated when ITE conditions become available later.
                    //
                    // We re-parse only when has_unsupported is true (cheap guard).
                    // If re-parsing succeeds without unsupported sub-expressions,
                    // we use the new result and update the cache. If it still has
                    // unsupported parts, we keep the original cached result.
                    if info.as_ref().is_some_and(|pi| pi.has_unsupported) {
                        tracing::warn!(
                            ?term,
                            asserted_len = self.asserted.len(),
                            "#8373: cached atom has_unsupported=true, attempting re-parse"
                        );
                        // #9217: Clear unsupported marker BEFORE re-parsing so
                        // that parse_linear_expr's mark_current_atom_unsupported()
                        // call (via insert()) can actually re-add it if the atom
                        // is still unsupported. Without this, insert() is a no-op
                        // because the atom is already in the set, and the post-parse
                        // contains() check always returns true -- making re-parse
                        // appear to fail even when ITE conditions are now resolved.
                        self.persistent_unsupported_atoms.remove(&term);
                        self.persistent_unsupported_trail.retain(|&a| a != term);
                        // Try re-parsing with current assertion context
                        self.current_parsing_atom = Some(term);
                        let reparsed = self.parse_atom(term).map(|(expr, is_le, strict)| {
                            let is_eq = matches!(self.terms().get(term), TermData::App(Symbol::Named(name), _) if name == "=");
                            let is_distinct = matches!(self.terms().get(term), TermData::App(Symbol::Named(name), _) if name == "distinct");
                            let has_unsupported = self.persistent_unsupported_atoms.contains(&term);
                            ParsedAtomInfo { expr, is_le, strict, is_eq, is_distinct, has_unsupported, compound_slack: None }
                        });
                        self.current_parsing_atom = None;
                        if reparsed.as_ref().is_some_and(|i| !i.has_unsupported) {
                            // ITE conditions are now resolved. Update cache and
                            // perform deferred atom_index registration (#8373).
                            // At registration time, this atom was skipped in
                            // atom_index because the expression contained fresh
                            // variables over-approximating unresolved ITEs. Now
                            // that the expression is correct, register it for
                            // sound bound propagation.
                            self.atom_cache.insert(term, reparsed.clone());
                            if let Some(ref resolved_info) = reparsed {
                                self.register_atom_index_for_resolved_atom(term, resolved_info);
                            }
                            reparsed
                        } else {
                            // Still unsupported after re-parse.
                            tracing::warn!(
                                ?term,
                                persistent_unsupported = self.persistent_unsupported_atoms.len(),
                                "#8373: re-parse FAILED, still unsupported"
                            );
                            info
                        }
                    } else {
                        _cache_hits += 1;
                        info
                    }
                }
                None => {
                    // Parse and cache. Set current_parsing_atom so that
                    // parse_linear_expr can track which atom triggered
                    // unsupported sub-expressions (#6167).
                    self.current_parsing_atom = Some(term);
                    if self.debug_intern {
                        safe_eprintln!("[PARSE] atom {:?}", term);
                    }
                    let parsed = self.parse_atom(term).map(|(expr, is_le, strict)| {
                        let is_eq = matches!(self.terms().get(term), TermData::App(Symbol::Named(name), _) if name == "=");
                        let is_distinct = matches!(self.terms().get(term), TermData::App(Symbol::Named(name), _) if name == "distinct");
                        let has_unsupported = self.persistent_unsupported_atoms.contains(&term);
                        ParsedAtomInfo { expr, is_le, strict, is_eq, is_distinct, has_unsupported, compound_slack: None }
                    });
                    self.current_parsing_atom = None;
                    self.atom_cache.insert(term, parsed.clone());
                    parsed
                }
            };

            let Some(info) = parsed_info else {
                skipped_count += 1;
                // Check if the skipped atom is a Boolean combination (or, and, xor, ite).
                //
                // #8452: Pure Boolean connectives (or, and, xor, =>, not) between
                // Bool-sorted arguments are handled entirely by the Tseitin/DPLL
                // layer and create NO arithmetic constraints. The LRA solver should
                // skip them without marking them as unsupported. Previously, marking
                // these as unsupported caused check() to downgrade Sat->Unknown on
                // benchmarks like sc-6.induction3 which have many xor atoms (42 xor
                // atoms -> Unknown).
                //
                // Only mark as unsupported when arguments include non-Bool sorts that
                // might create arithmetic constraints the LRA solver is missing.
                match self.terms().get(term) {
                    TermData::App(Symbol::Named(name), args)
                        if name == "or"
                            || name == "and"
                            || name == "xor"
                            || name == "=>"
                            || name == "not" =>
                    {
                        // #8003: Boolean combinations (or, and, xor, =>) are
                        // propositional connectives handled entirely by the
                        // Tseitin/DPLL layer. They appear in the theory trail
                        // because the DPLL layer passes ALL atoms — including
                        // intermediate CNF expressions — to the theory solver.
                        //
                        // Previously, these were marked as unsupported, which
                        // caused the theory to return Unknown for satisfiable
                        // QF_LRA benchmarks with xor conditions in ITE terms
                        // (e.g., sc-6). The xor atoms have no arithmetic content
                        // and are NOT constraints that the theory needs to handle.
                        // Marking them unsupported is incorrect — it's the same
                        // category as Bool-sort equality/distinct (line 259).
                        if debug {
                            safe_eprintln!(
                                "[LRA] Skipping Boolean combination {:?} - handled by DPLL layer",
                                term
                            );
                        }
                    }
                    // Bool-sort equality/distinct (e.g., (= x_48 (not x_40))) are
                    // Boolean connectives (iff/xor) handled by the Tseitin layer,
                    // not arithmetic predicates. parse_atom returns None for these
                    // (#4919). Skip without marking unsupported.
                    TermData::App(Symbol::Named(name), args)
                        if (name == "=" || name == "distinct")
                            && args
                                .first()
                                .is_some_and(|&a| self.terms().sort(a) == &Sort::Bool) =>
                    {
                        if debug {
                            safe_eprintln!(
                                "[LRA] Skipping Bool-sort {} {:?} - handled by Tseitin layer",
                                name,
                                term
                            );
                        }
                    }
                    TermData::Ite(_, _, _) => {
                        // Bool-sort ITE atoms (e.g., `(ite cond p q)` where p,q
                        // are Bool) are Boolean circuits handled entirely by the
                        // Tseitin/DPLL layer. The LRA solver need not track them,
                        // and marking them unsupported incorrectly converts SAT
                        // results to Unknown (#4919).
                        //
                        // Non-Bool ITE atoms (Real/Int-valued) should have been
                        // eliminated by lift_arithmetic_ite_all; mark unsupported
                        // to preserve soundness if lifting missed them.
                        let is_bool_ite = self.terms().sort(term) == &Sort::Bool;
                        if !is_bool_ite {
                            if debug {
                                safe_eprintln!(
                                    "[LRA] Skipping non-Bool ITE atom {:?} - marking incomplete",
                                    term
                                );
                            }
                            self.mark_atom_unsupported(term);
                        } else if debug {
                            safe_eprintln!(
                                "[LRA] Skipping Bool ITE atom {:?} - handled by Tseitin layer",
                                term
                            );
                        }
                    }
                    // #8373: Pure Boolean variables (TermData::Var) asserted via
                    // the ITE condition forwarding path are NOT arithmetic atoms.
                    // They exist in self.asserted solely so that parse_linear_expr
                    // can resolve ITE conditions. Skip without marking unsupported.
                    TermData::Var(_, _) => {
                        if debug {
                            safe_eprintln!(
                                "[LRA] Skipping Bool Var atom {:?} - ITE condition indicator",
                                term
                            );
                        }
                    }
                    _ => {
                        // Unrecognized atom (e.g., BV comparisons like bvsle).
                        // In standalone mode (not combined_theory_mode), no other
                        // theory handles these, so we must flag as unsupported to
                        // prevent false SAT results from ignored constraints (#5523).
                        if !self.combined_theory_mode {
                            self.mark_atom_unsupported(term);
                        }
                        if debug {
                            safe_eprintln!(
                                "[LRA] Skipping unparseable atom {:?} (term: {:?}), combined_theory_mode={}",
                                term,
                                self.terms().get(term),
                                self.combined_theory_mode,
                            );
                        }
                    }
                }
                continue;
            };
            parsed_count += 1;

            let ParsedAtomInfo {
                expr,
                is_le,
                strict,
                is_eq,
                is_distinct,
                has_unsupported,
                compound_slack: _,
            } = info;

            // #8373: Skip bound assertion for atoms with unsupported sub-expressions
            // (e.g., ITE conditions that are still unknown). The fresh variable
            // over-approximation creates wrong bounds that can't be easily undone.
            // By skipping, we ensure the atom will be re-processed on a later
            // check() call (it won't be in bound_atoms), potentially with the
            // ITE conditions resolved. The `has_asserted_unsupported` flag in
            // check_impl() ensures the theory returns Unknown rather than SAT
            // when unsupported atoms are still present.
            if has_unsupported {
                skipped_count += 1;
                // #9217: Record the trail position of this unsupported atom
                // so last_check_trail_pos doesn't advance past it. On the
                // next check() call, the atom will be re-processed with
                // potentially-resolved ITE conditions.
                if earliest_unsupported_skip.is_none() {
                    earliest_unsupported_skip = Some(i);
                }
                if debug {
                    safe_eprintln!(
                        "[LRA] #8373: Skipping bound assertion for unsupported atom {:?}",
                        term
                    );
                }
                continue;
            }

            // For all arithmetic atoms, expr is normalized so that the atom is:
            // expr <= 0 (for is_le=true) or expr >= 0 (for is_le=false)
            // The bound is always 0.
            // #8406: Rational::zero() avoids BigRational heap allocation.
            let zero = Rational::zero();

            if is_eq || is_distinct {
                // For equality (=):
                //   value=true  → assert equality (a = b)
                //   value=false → add disequality (a != b)
                // For distinct:
                //   value=true  → add disequality (a != b) - INVERTED
                //   value=false → assert equality (a = b) - INVERTED
                let is_equality = (is_eq && value) || (is_distinct && !value);

                if is_equality {
                    // A5 core: BCP-time checks defer equality rows; the full
                    // check materializes violated ones on demand.
                    if self.a5_core && bcp_mode && !expr.is_constant() {
                        self.deferred_eq_atoms.push((term, expr.clone(), value));
                        self.bound_atoms.insert((term, value));
                        continue;
                    }
                    // Equality: expr = 0 means expr <= 0 AND expr >= 0
                    // Use the actual assertion value for reason_value (important for `distinct` negations)
                    if !expr.is_constant() {
                        self.assert_bound_for_atom(
                            expr.clone(),
                            zero.clone(),
                            BoundType::Upper,
                            false,
                            term,
                            value,
                            (term, value),
                        );
                        self.assert_bound_for_atom(
                            expr,
                            zero,
                            BoundType::Lower,
                            false,
                            term,
                            value,
                            (term, value),
                        );
                    }
                    self.bound_atoms.insert((term, value));
                } else {
                    // Disequality: x != c can't be directly encoded in simplex.
                    // We'll check these after simplex to see if any are violated by the model.
                    // Store (term, expr, asserted_value) for post-simplex checking: if expr evaluates to 0
                    // in the model, the disequality is violated.
                    // NOTE: Disequalities are NOT cached in bound_atoms because they must be
                    // re-checked against the current model on every check() call.
                    if debug {
                        safe_eprintln!("[LRA] Disequality atom {:?}: will check model later", term);
                    }
                    self.disequality_trail.push((term, expr.clone(), value));
                    disequalities.push((term, expr, value));
                }
            } else if value {
                // Positive assertion: expr <= 0 or expr < 0
                if is_le {
                    self.assert_bound_for_atom(
                        expr,
                        zero,
                        BoundType::Upper,
                        strict,
                        term,
                        true,
                        (term, true),
                    );
                } else {
                    // expr >= 0 or expr > 0
                    self.assert_bound_for_atom(
                        expr,
                        zero,
                        BoundType::Lower,
                        strict,
                        term,
                        true,
                        (term, true),
                    );
                }
                self.bound_atoms.insert((term, value));
            } else {
                // Negated assertion: !(expr <= 0) means expr > 0
                if is_le {
                    // !(expr <= 0) => expr > 0
                    self.assert_bound_for_atom(
                        expr,
                        zero,
                        BoundType::Lower,
                        !strict,
                        term,
                        false,
                        (term, false),
                    );
                } else {
                    // !(expr >= 0) => expr < 0
                    self.assert_bound_for_atom(
                        expr,
                        zero,
                        BoundType::Upper,
                        !strict,
                        term,
                        false,
                        (term, false),
                    );
                }
                self.bound_atoms.insert((term, value));
            }

            // #7719 / #6617 D3: interleave implied-bound derivation with atom
            // processing so later atoms in the same batched check can benefit
            // from bounds unlocked by earlier ones. Without this, BCP-time
            // batched checks strand cross-row cascades until a later round.
            //
            // #8003: Dense LP / large tableau optimization. Skip per-atom
            // cascade for dense rows (>50 coefficients) and large tableaux
            // (500+ rows) in BCP mode. The post-simplex propagation path
            // in run_post_simplex_propagation() handles cascading.
            //
            // #8255: Per-check cascade budget replaces the per-atom cap.
            // Previously, each atom got cascade_rounds iterations of
            // compute_implied_bounds (up to 16 for small problems). With
            // N atoms per check, this was O(N * 16) calls — on sc-8
            // (10K+ checks, ~200 rows), this produced 20K+ cascade rounds.
            //
            // The shared budget caps the TOTAL cascade calls across all
            // atoms in a single process_check_atoms invocation. Per-atom
            // cap is min(budget_remaining, 8) so deep cascades are still
            // possible for the first few atoms, but late atoms in large
            // batches defer their cascades to the post-simplex fixpoint.
            //
            // Soundness: the post-simplex fixpoint loop and the full
            // check_impl() path catch any cascades missed here.
            let per_atom_cap: u32 = if bcp_mode {
                // In BCP mode, limit per-atom cascade depth. The post-simplex
                // fixpoint handles deeper cascades.
                if self.rows.len() < 200 {
                    8
                } else {
                    4
                }
            } else {
                // Full-check mode: generous per-atom cap.
                if self.rows.len() < 200 {
                    16
                } else {
                    10
                }
            };
            let cascade_rounds = cascade_budget_remaining.min(per_atom_cap);
            if cascade_rounds > 0 && !self.touched_rows.is_empty() {
                for _ in 0..cascade_rounds {
                    cascade_budget_remaining = cascade_budget_remaining.saturating_sub(1);
                    let result = self.compute_implied_bounds();
                    let is_empty = result.newly_bounded.is_empty();
                    if !is_empty {
                        // #8452 TL62: Per-atom immediate bound propagation.
                        // After computing implied bounds from the cascade, immediately
                        // scan newly-bounded variables for atoms that can be propagated.
                        // This matches Z3's propagate_basic_bounds() which runs per-
                        // assertion, not per-batch.
                        //
                        // Reference: Z3 arith_solver.cpp:121-128 propagate_basic_bounds()
                        if bcp_mode && !self.atom_index.is_empty() {
                            let mut sorted_vars: Vec<u32> =
                                result.newly_bounded.iter().copied().collect();
                            sorted_vars.sort_unstable();
                            self.compute_bound_propagations_for_vars(&sorted_vars);
                        }
                        self.propagation_dirty_vars.extend(&result.newly_bounded);
                    }
                    // #8256: Stop early when the inner cascade converged (natural
                    // fixpoint). Further calls would re-derive the same bounds.
                    if is_empty || result.converged {
                        break;
                    }
                }
            }
        }
        // Update incremental position: all atoms up to trail_len are now processed.
        // #9217: If any atom was skipped because has_unsupported=true, set the
        // trail cursor back to that position so the atom is re-processed on the
        // next check() call. This ensures ITE conditions that become available
        // later (when the SAT solver assigns them) trigger re-parsing of the
        // unsupported atom, resolving the ITE to its correct branch.
        // Without this fix, last_check_trail_pos advances past the unsupported
        // atom and it is never re-processed, leaving the theory permanently
        // returning Unknown on satisfiable QF_LRA benchmarks with ITE expressions.
        self.last_check_trail_pos = earliest_unsupported_skip.unwrap_or(trail_len);

        // Second pass: collect disequalities from previously-processed atoms.
        // Use the incremental disequality_trail instead of scanning all atoms O(trail).
        // The trail already contains (term, expr, value) triples from prior check() calls;
        // we only need to verify they are still asserted (not popped).
        if !bcp_mode {
            let mut _dropped_not_asserted = 0usize;
            for (term, expr, value) in &self.disequality_trail {
                // Verify this disequality is still in the current assertion set
                // (it may have been logically overridden, though pop handles most cases).
                if self.asserted.get(term) == Some(value) {
                    disequalities.push((*term, expr.clone(), *value));
                } else {
                    _dropped_not_asserted += 1;
                }
            }
            if debug {
                safe_eprintln!(
                    "[LRA] diseq second pass: trail={} kept={} dropped_not_asserted={}",
                    self.disequality_trail.len(),
                    disequalities.len(),
                    _dropped_not_asserted
                );
            }
        }

        Ok(CheckAtomStats {
            disequalities,
            parsed_count,
            skipped_count,
        })
    }

    /// Inject floor axioms for to_int terms (#5944):
    ///   to_int(x) <= x < to_int(x) + 1
    /// Expressed as bounds on (x - to_int(x)): 0 <= diff < 1.
    pub(crate) fn inject_to_int_axioms(&mut self) {
        if self.to_int_terms.is_empty() {
            return;
        }
        for i in 0..self.to_int_terms.len() {
            let (to_int_var, inner_arg) = self.to_int_terms[i];
            if !self.injected_to_int_axioms.insert(to_int_var) {
                continue; // Already injected in this scope
            }
            // Parse inner argument to get its linear expression
            let arg_expr = self.parse_linear_expr(inner_arg);
            // diff = x - to_int(x)
            let mut diff = arg_expr;
            diff.add_term_rat(to_int_var, -Rational::one());
            // #6679: Sentinel provenance — unconditional theory axioms must not
            // degrade to Unknown when the simplex later builds a conflict touching
            // these bounds. The contradictory-bounds precheck treats sentinel-only
            // bounds as partial conflicts. This fix was originally landed in
            // theory_impl.rs by commit 0c89b93f4 but was lost when check_atoms.rs
            // was extracted in commit 2ed40fe68 (#8747).
            let axiom_reason = [(TermId::SENTINEL, true)];
            // Assert diff >= 0 (to_int(x) <= x)
            self.assert_bound_with_reasons(
                diff.clone(),
                Rational::zero(),
                BoundType::Lower,
                false,
                &axiom_reason,
                None,
            );
            // Assert diff < 1 (x < to_int(x) + 1)
            self.assert_bound_with_reasons(
                diff,
                Rational::one(),
                BoundType::Upper,
                true, // strict: diff < 1
                &axiom_reason,
                None,
            );
            self.dirty = true;
        }
    }

    /// Post-simplex propagation: compute implied bounds, wake compound atoms,
    /// discover offset equalities, and queue bound refinements.
    ///
    /// This MUST run after simplex returns Sat and before disequality checking
    /// so that propagate() has finite bounds for compound atoms.
    ///
    /// When `bcp_mode` is true (called from `check_during_propagate`), skip
    /// expensive model-completion work (offset equality discovery, bound
    /// refinement requests) that is only needed at final-check time. This
    /// reduces per-BCP-callback overhead on QF_LRA benchmarks where the theory
    /// callback fires hundreds of times per solve.
    ///
    /// #8187: The `skip_implied_bounds` parameter was removed. Research
    /// confirmed that Z3 ALWAYS runs simplex during BCP (never throttles),
    /// so the tableau is always feasible when this function runs. The Phase 3
    /// BCP budget system that necessitated skip_implied_bounds was replaced
    /// with dual_simplex_propagate() using proportional budget max(200, 5*num_vars).
    pub(crate) fn run_post_simplex_propagation(
        &mut self,
        need_simplex: bool,
        debug: bool,
        bcp_mode: bool,
    ) {
        self.stats.simplex_sat_count += 1;
        let pre_prop_count = self.pending_propagations.len();
        let has_cascade_rows = !self.touched_rows.is_empty();
        // Skip compute_implied_bounds in BCP mode when nothing changed
        // (no direct bounds changed + no cascade rows + implied bounds
        // already populated).
        //
        // #8319: AY_NO_IMPLIED_BOUNDS disables compute_implied_bounds entirely.
        //
        // #8452: When need_simplex is true, do NOT skip implied bounds in
        // BCP mode. Simplex pivots change the tableau, creating new row-based
        // bound derivation opportunities. Z3's unit_propagate() always runs
        // propagate_bounds_for_touched_rows() after simplex.
        //
        // The skip only applies when nothing changed at all (no simplex, no
        // cascade rows, no direct bound changes).
        // Compute-and-discard fix (sat-side-model-search diagnosis): when
        // theory propagation is disabled (per-instance
        // `set_no_theory_propagation` or AY_NO_THEORY_PROPAGATION),
        // `propagate_impl()` discards every pending propagation at drain
        // time, so the propagation results of BCP-time implied-bounds
        // computation are wasted work (profiled as the #1 hot leaf even with
        // the flag on). However, the computed bounds have one other surviving
        // consumer during BCP: `queue_post_simplex_refinements` (BP_REFINE
        // dynamic atom creation). Measured on DRAGON_3 depth-1: skipping the
        // BCP computation while refinement is still enabled flips the
        // eager-arm verdict from sat (1.4s) to unknown — the refinement
        // atoms are load-bearing for completeness. So the skip only applies
        // when bound refinement is ALSO disabled, i.e. when the computed
        // bounds are provably discarded. Final-check cascades are always
        // kept (they additionally feed compound wakeups and offset-equality
        // discovery).
        let skip_implied = self.no_implied_bounds
            || (bcp_mode && self.no_theory_propagation && self.no_bound_refinement)
            || (bcp_mode
                && !need_simplex
                && !self.direct_bounds_changed_since_implied
                && !has_cascade_rows
                && !self.implied_bounds.is_empty());
        // #8452: After backtrack/pop, implied_bounds is cleared but touched_rows
        // may be empty (no bounds changed during unwind, or all changed vars'
        // rows already processed). The old gate `need_simplex || has_cascade_rows`
        // would skip compute_implied_bounds entirely, leaving the cache empty
        // until the next callback that tightens a bound. This delays cross-variable
        // propagation by one or more BCP rounds, causing unnecessary decisions on
        // benchmarks where the first post-backtrack callback processes
        // non-arithmetic atoms.
        //
        // More generally, when direct_bounds_changed_since_implied is true, the
        // implied bounds overlay is stale and compute_implied_bounds must run to
        // incorporate the new direct bounds. This covers two cases:
        //   1. Post-backtrack rebuild: implied_bounds is empty, needs full scan.
        //   2. Stale overlay: new direct bounds asserted after the last
        //      compute_implied_bounds call, need overlay + row analysis.
        //
        // Z3's propagate_bounds_for_touched_rows() always runs after simplex and
        // after any bound change, so bounds are never stale. Matching that.
        let need_implied_refresh = self.direct_bounds_changed_since_implied;
        // #8255: Stale-cascade fast skip. In BCP mode, when the only reason to
        // enter compute_implied_bounds is seeded touched_rows from the previous
        // cascade (has_cascade_rows) but no new direct bounds have changed and
        // no simplex ran, those seeded rows will be generation-skipped inside
        // compute_implied_bounds (their row_computed_gen == var_bound_gen for all
        // variables since no new bounds were applied). Skip the entire call to
        // avoid O(touched_rows) iteration and generation-check overhead.
        //
        // This converts the "enter compute_implied_bounds, iterate rows, skip
        // all via generation check, exit" overhead to a simple boolean check.
        // On windowreal (718 rows), this eliminates ~1500 calls where the cascade
        // seeds rows but no new information is available to process.
        // #8422: Don't skip stale cascade rows when propagate_direct_touched_rows_pending
        // is true. This flag indicates the previous fixpoint didn't converge and the
        // touched_rows contain real cascade information (not stale generation-matched rows).
        // The rows were seeded by the last compute_implied_bounds iteration which found
        // new bounds but couldn't continue due to the fixpoint cap.
        let stale_cascade_skip = bcp_mode
            && has_cascade_rows
            && !need_simplex
            && !need_implied_refresh
            && !self.propagate_direct_touched_rows_pending;
        if stale_cascade_skip {
            self.touched_rows.clear();
        }
        if (need_simplex || (has_cascade_rows && !stale_cascade_skip) || need_implied_refresh)
            && !skip_implied
        {
            if debug {
                // Approach G (#4919): show touched_rows AFTER simplex (includes
                // pivot-modified rows from Approach D).
                safe_eprintln!(
                    "[LRA] PRE compute_implied_bounds: touched_rows={} (includes pivot rows)",
                    self.touched_rows.len(),
                );
            }
            // Snapshot touched rows before compute_implied_bounds clears them.
            // Only needed for offset equality discovery (final-check only).
            // #8256: Attempted BCP-time offset equality discovery but reverted.
            // Z3's cheap_eq_on_nbase propagates equalities directly through the
            // E-graph (unit propagation). AY's architecture requires model equality
            // splits, which are expensive during BCP. The row-scan overhead of
            // discover_offset_equalities on every BCP callback outweighs the
            // deferred benefit when equalities are only consumed at full check.
            // #8422: Confirmed BCP-time offset equality causes 12.8x regression
            // on simple_startup_7nodes (764ms -> 9791ms) due to propagation
            // feedback loop -- more equalities trigger more propagation rounds.
            let touched_snapshot = if bcp_mode {
                None
            } else {
                Some(self.touched_rows.clone())
            };
            // #7982: Iterative fixpoint for implied bounds. Z3's propagation
            // loop re-enters bound_analyzer_on_row whenever newly-derived bounds
            // enable further derivations. AY previously ran a single pass and
            // relied on the DPLL loop to re-enter, leaving transitive cascades
            // stranded until the next check() call.
            //
            // #8422: Differentiated fixpoint caps for BCP vs full-check mode.
            //
            // BCP mode (check_during_propagate): cap at 4. Higher caps (8, 16)
            // generate conflict storms — the extra implied bounds create more
            // theory conflicts per BCP call, destabilizing the SAT search on
            // synched.base and sc-8. BCP is called frequently; the DPLL loop
            // re-enters for further cascading, so 4 iterations suffice.
            //
            // Full-check mode (check after Sat): cap at 8. Full check runs
            // once per split-loop iteration (not per BCP call), so extra
            // iterations are affordable and catch deeper transitive cascades
            // that BCP's limited budget misses.
            //
            // Dense BCP exception: cap at 1 for rows wider than 50 coefficients.
            // Each iteration is O(rows * width), prohibitively expensive for
            // iterative fixpoint.
            //
            // #8319: AY_MAX_FIXPOINT_ROUNDS env var overrides the default cap.
            let mut all_newly_bounded = DenseU32Set::default();
            let mut fixpoint_iters = 0u32;
            let default_max = if bcp_mode && self.max_row_width > 50 {
                // #8422: Dense BCP cap at 2 (increased from 1). Single-pass
                // missed one-hop transitive cascades even on dense benchmarks.
                2
            } else if bcp_mode {
                // #8452: Adaptive fixpoint cap based on tableau size.
                // Z3's propagation loop has no explicit cap; it re-enters
                // bound_analyzer_on_row until no new bounds are derived.
                // Each iteration only processes touched rows (not all rows),
                // so the cost scales with cascade depth * width.
                //
                // On small/medium problems (< 200 rows), deeper cascades
                // significantly reduce decisions (sc-6: 5445 -> 4169 at cap 24).
                // On larger problems (>= 200 rows), deep cascades at cap 24
                // cause over-propagation leading to conflict storms.
                //
                // #8256: Two-tier BCP caps. Cap 24 on large problems caused
                // conflict storms (simple_startup: 7K -> 15K decisions).
                // Keep conservative cap for BCP (runs per callback).
                //
                // #8255: Dry-streak adaptive throttling. When 4+ consecutive
                // BCP checks find zero implied bounds, the bound lattice has
                // saturated — further fixpoint iterations waste O(cap*rows)
                // work. Throttle cap to 1 (single pass). Streak resets on
                // bound tightening, pop/soft_reset, or finding new bounds.
                // On sc-6 (5006 checks), eliminates ~2500*31 wasted fixpoint
                // iterations.
                // #clocksynchro: Four-tier BCP fixpoint cap based on tableau size.
                //
                // Small (<200 rows): deep cascades reduce decisions significantly.
                // Medium-small (200-349 rows): moderate cap avoids conflict storms
                //   while still catching multi-hop transitive chains.
                // Medium-large (350-499 rows): conservative cap. Per-iteration
                //   cost is O(touched_rows * width) and with 380+ rows
                //   (simple_startup), 8 iterations * 5 cascade depth * 8 CDCL
                //   fixpoint = 320 compute_implied_bounds calls per decision,
                //   each doing expensive bignum arithmetic. Cap at 3 reduces to
                //   120 calls. The DPLL loop re-enters for further cascading.
                // Large (500+ rows): cap at 2 (same as dense-width path). Each
                //   compute_implied_bounds iteration is O(touched_rows * width),
                //   and with 700+ rows (clocksynchro), 8 iterations per BCP
                //   callback at ~0.1s each = ~0.8s per callback. With 36+
                //   equality cycles at level 0, that's ~30s of overhead. Capping
                //   at 2 cuts this to ~7s. The DPLL loop re-enters for further
                //   cascading, so shallow BCP cascades are sufficient.
                let base_cap = if self.rows.len() < 200 {
                    32
                } else if self.rows.len() < 350 {
                    8
                } else if self.rows.len() < 500 {
                    3
                } else {
                    2
                };
                if self.bcp_implied_dry_streak >= 4 {
                    1
                } else {
                    base_cap
                }
            } else {
                // Full-check mode: runs once per split-loop iteration (not
                // per BCP callback), so deeper cascades are affordable.
                // #8256: Increased large-problem cap from 8 to 20. The
                // simple_startup benchmarks have 380+ rows with transitive
                // bound chains (x_3 <= x_4 <= ... <= x_N) that require
                // deeper fixpoint iterations to fully propagate. Full-check
                // is the last chance before a split-loop round-trip, so
                // thorough cascade discovery reduces unnecessary iterations.
                if self.rows.len() < 200 {
                    32
                } else {
                    20
                }
            };
            // Fix #2 (sat-side-model-search diagnosis): restrain BCP-time
            // implied-bounds on the propagation-disabled cex lane. With
            // `no_theory_propagation` set, every implied bound derived during
            // BCP is discarded by `propagate_impl()` (BP_REFINE is also a
            // no-op), so the transitive cascade is pure per-check overhead and
            // was profiled as the dominant leaf on deep-cex DRAGON instances.
            // Restrain to a single derivation pass (outer fixpoint cap 0 → one
            // `compute_implied_bounds` call; inner cascade capped to 1 via
            // `bcp_implied_single_pass`). Sound: fewer implied bounds is a
            // weaker (sound) propagation; the full cascade still runs at final
            // check (bcp_mode=false), so eager-arm completeness — which needs
            // the cascade to feed LIA integer reasoning at final check — is
            // preserved. Other lanes keep propagation on and are untouched.
            let restrain_bcp_implied = bcp_mode
                && self.no_theory_propagation
                && !lra_debug_flags().no_bcp_implied_restraint;
            self.bcp_implied_single_pass = restrain_bcp_implied;
            let max_fixpoint_iters: u32 = if restrain_bcp_implied {
                0
            } else {
                self.max_fixpoint_rounds.unwrap_or(default_max)
            };
            let mut any_deep_cascade_productive = false;
            let fixpoint_continuation_needed = loop {
                let result = self.compute_implied_bounds();
                let is_empty = result.newly_bounded.is_empty();
                if result.deep_cascade_productive {
                    any_deep_cascade_productive = true;
                }
                if !is_empty {
                    // #8422: Interleave bound propagation with the fixpoint loop.
                    // After each compute_implied_bounds() iteration discovers newly
                    // bounded variables, immediately scan those variables' atoms to
                    // queue propagations. This allows propagations from early fixpoint
                    // rounds to be returned to the SAT solver sooner, rather than
                    // waiting until the entire fixpoint loop exits. Z3 achieves its
                    // 228K propagation volume by naturally interleaving LP-derived
                    // bounds with atom scanning in every propagate_core() call.
                    //
                    // Only run for newly bounded variables (not the full dirty set)
                    // to keep cost proportional to new information.
                    let mut newly_bounded_sorted: Vec<u32> =
                        result.newly_bounded.iter().copied().collect();
                    newly_bounded_sorted.sort_unstable();
                    if !self.atom_index.is_empty() && !newly_bounded_sorted.is_empty() {
                        self.compute_bound_propagations_for_vars(&newly_bounded_sorted);
                    }
                    all_newly_bounded.extend(&result.newly_bounded);
                }
                // #8256: Stop the outer fixpoint when the inner cascade converged
                // naturally (didn't hit MAX_CASCADE_DEPTH).
                let reached_cap =
                    !is_empty && !result.converged && fixpoint_iters >= max_fixpoint_iters;
                if is_empty || result.converged || reached_cap {
                    // #8008: Track outer fixpoint iteration stats.
                    if fixpoint_iters > self.stats.max_outer_fixpoint_iters {
                        self.stats.max_outer_fixpoint_iters = fixpoint_iters;
                    }
                    self.stats.total_outer_fixpoint_iters += u64::from(fixpoint_iters);
                    break reached_cap && !self.touched_rows.is_empty();
                }
                fixpoint_iters += 1;
                // touched_rows was already seeded by compute_implied_bounds for
                // rows containing newly_bounded variables. The next iteration
                // will analyze only those rows, deriving further transitive bounds.
            };
            // Fix #2: clear the transient single-pass restraint so later
            // final-check cascades (bcp_mode=false) compute the full fixpoint.
            self.bcp_implied_single_pass = false;
            // #8422: Keep propagate_direct_touched_rows_pending set only when the
            // fixpoint hit the iteration cap with new bounds still being found and
            // compute_implied_bounds left touched_rows queued. When the fixpoint
            // converges, those reseeded rows are cache state rather than actionable
            // continuation work, so the extension can skip them cheaply.
            //
            // Previously, unconditionally clearing this flag combined with
            // implied_bounds_fresh=true caused propagate_impl() to skip the
            // remaining cascade, and the next BCP callback's stale_cascade_skip
            // cleared the rows. This lost up to 32 rounds of transitive bound
            // derivation on benchmarks with long bound chains (simple_startup).
            self.propagate_direct_touched_rows_pending = fixpoint_continuation_needed;
            // #8200: Update BCP dry streak counter.
            if bcp_mode {
                if all_newly_bounded.is_empty() {
                    self.bcp_implied_dry_streak = self.bcp_implied_dry_streak.saturating_add(1);
                } else {
                    self.bcp_implied_dry_streak = 0;
                }
                // #8255: Update BCP cascade dry streak counter.
                // Track whether cascading beyond depth 1 produced any additional
                // bounds in this fixpoint invocation. When deep cascading is
                // consistently unproductive (streak >= 3), compute_implied_bounds
                // throttles cascade depth to 1, saving O(depth * rows_per_round)
                // per check on large problems where the bound lattice saturates
                // after the first cascade pass.
                if any_deep_cascade_productive {
                    self.bcp_cascade_dry_streak = 0;
                } else {
                    self.bcp_cascade_dry_streak = self.bcp_cascade_dry_streak.saturating_add(1);
                }
            }
            if debug {
                safe_eprintln!(
                    "[LRA] compute_implied_bounds fixpoint: {} newly bounded vars, {} iterations",
                    all_newly_bounded.len(),
                    fixpoint_iters,
                );
            }
            // Mark variables with new implied bounds as dirty for propagation.
            // This enables multi-variable interval propagation in propagate() to
            // fire on atoms referencing these variables (#4919 RC2).
            self.propagation_dirty_vars.extend(&all_newly_bounded);

            // Offset equality discovery is model-completion work.
            // During BCP propagation, skip it -- it'll run at final check.
            // #8256: Attempted BCP-time offset equality discovery but reverted.
            // AY's model-equality split architecture makes BCP-time equality
            // discovery counterproductive: the row-scan overhead of
            // discover_offset_equalities on every BCP callback is wasted when
            // equalities are only consumed as splits at full check. Z3 handles
            // this differently by propagating equalities as unit clauses through
            // the E-graph, which AY's split-based architecture cannot match.
            // #8422: Confirmed regression -- BCP-time offset equalities cause
            // propagation feedback loops (12.8x slowdown on simple_startup).
            if !bcp_mode {
                if let Some(ref snapshot) = touched_snapshot {
                    self.discover_offset_equalities(snapshot);
                }
            }

            // BP_REFINE (#4919 Phase 6): After simplex finds feasible and
            // compute_implied_bounds() derives fresh bounds, scan atoms for
            // variables that gained a tighter implied bound with no matching
            // existing atom. Queue BoundRefinementRequests for the DPLL
            // executor to create new atoms.
            //
            // Runs in BOTH full-check and BCP modes. Z3's refine_bound()
            // fires during every propagate_core() call (theory_lra.cpp:2498),
            // not just at final check. Enabling it during BCP gives the SAT
            // solver finer-grained theory information earlier, reducing
            // unnecessary decisions on under-constrained variables.
            //
            // Budget: queue_post_simplex_refinements caps at
            // MAX_REFINEMENTS_PER_CHECK (8) to prevent atom explosion during
            // BCP where the callback fires hundreds of times per solve.
            //
            // Reference: Z3 propagate_lp_solver_bound() / refine_bound()
            // at theory_lra.cpp:2463-2504.
            // #8319: AY_NO_BOUND_REFINEMENT disables BP_REFINE dynamic atom creation.
            if !self.no_bound_refinement {
                self.queue_post_simplex_refinements(&all_newly_bounded, debug);
            }
        } else if skip_implied {
            // #7973: Skipped compute_implied_bounds. Reset the direct-touched flag.
            self.propagate_direct_touched_rows_pending = false;
        }
        // #7719 D3: Reuse persistent scratch buffer instead of allocating a
        // fresh Vec<u32> per call. On 1000 check() calls with ~5 dirty vars each,
        // this eliminates 1000 small-Vec allocations. Take the buffer out of self
        // to avoid borrow conflicts with &mut self methods, then put it back.
        let mut dirty_vars = std::mem::take(&mut self.dirty_vars_scratch);
        dirty_vars.clear();
        dirty_vars.extend(self.propagation_dirty_vars.iter().copied());
        // #7654: Sort dirty vars for deterministic propagation order.
        // propagation_dirty_vars is a HashSet with RandomState — iteration
        // order varies per process, causing non-deterministic propagation
        // subsets when MAX_IMPLIED_PROPAGATIONS caps the total.
        dirty_vars.sort_unstable();
        // #8452: Run compound wake and bound propagation during BCP for ALL
        // problems, including large LRA. Z3's new solver (sat/smt mode) uses
        // UINT_MAX as propagation threshold — it NEVER skips bound propagation.
        // The previous large_lra skip (rows > 200 || max_row_width > 50) was
        // disabling the entire propagation pipeline during BCP, preventing the
        // SAT solver from receiving theory guidance on non-trivial benchmarks.
        //
        // Performance is maintained by the dirty-var filter: only variables
        // with changed bounds are scanned, limiting work to O(dirty * atoms_per_var).
        let compound_queued = self.queue_compound_propagations_for_dirty_vars(&dirty_vars);
        // Same-variable chain bound propagation (Z3 Component 3).
        // Run even when simplex was skipped: after backtracking, propagated_atoms
        // is cleared, so previously propagated atoms need re-propagation with
        // the existing bounds. Restricting the scan to dirty variables keeps
        // this incremental on large QF_LRA instances (#6582 Packet 4).
        if !self.atom_index.is_empty() && !dirty_vars.is_empty() {
            self.compute_bound_propagations_for_vars(&dirty_vars);
        }
        self.dirty_vars_scratch = dirty_vars;
        if debug {
            let new_props = self.pending_propagations.len() - pre_prop_count;
            safe_eprintln!(
                "[LRA] Post-simplex propagation: atom_index_size={}, compound_use_vars={}, new_propagations={}, compound_queued={}, dirty_vars={}, wake_dirty_hits={}, wake_candidates={}",
                self.atom_index.len(),
                self.compound_use_index.len(),
                new_props,
                compound_queued,
                self.propagation_dirty_vars.len(),
                self.last_compound_wake_dirty_hits,
                self.last_compound_wake_candidates,
            );
        }
    }
}
