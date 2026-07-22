// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counting and error-implied invariant discovery.

use super::*;

impl PdrSolver {
    /// Discover counting invariants for chained predicate structures.
    ///
    /// For benchmarks like gj2007 where predicates form a chain (inv -> inv2 -> ... -> invN),
    /// discovers invariants of the form `B = k * C` where k increases with each predicate.
    ///
    /// The approach:
    /// 1. Find predicates that have a var=var equality (e.g., B = C) in init
    /// 2. For each such predicate and each predicate in the problem, try B = k*C for k = 1..10
    /// 3. Verify using SMT that B = k*C is implied by all ways to reach that predicate
    pub(in crate::pdr::solver) fn discover_counting_invariants(&mut self) {
        // #7457: Internal time cap. Each verify_multiplicative_invariant call uses
        // 100ms SMT timeout, and with O(n^2 * k) candidates (e.g., 4 vars × 3 × 10
        // = 120 checks), this can consume 4+ seconds on problems where counting
        // invariants don't help. Cap to 500ms to avoid starving the overall solve.
        let counting_deadline =
            ay_core::time::Instant::now() + std::time::Duration::from_millis(500);

        // First, find predicates with var=var equalities in init (the "base" predicates)
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // For each predicate, try to find multiplicative invariants B = k*C
        for pred in &predicates {
            // Skip predicates with unrestricted incoming inter-predicate transitions.
            // Guarded entry transitions are handled by `add_discovered_invariant`, which enforces
            // entry-inductiveness before accepting the candidate.
            if self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                continue;
            }
            let has_incoming = self.has_any_incoming_inter_predicate_transitions(pred.id);

            // Skip predicates in cyclic SCCs. Counting invariants verified within-predicate
            // may not hold for transitions INTO the predicate from other SCC members.
            if let Some(&scc_idx) = self.scc_info.predicate_to_scc.get(&pred.id) {
                if self.scc_info.sccs[scc_idx].is_cyclic
                    && self.scc_info.sccs[scc_idx].predicates.len() > 1
                {
                    continue;
                }
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Need at least 2 integer variables
            let int_vars: Vec<_> = canonical_vars
                .iter()
                .filter(|v| matches!(v.sort, ChcSort::Int))
                .collect();
            if int_vars.len() < 2 {
                continue;
            }
            // Skip high-arity predicates (#6047): counting discovery is O(n^2 * k)
            // in the number of integer variables. With 50+ vars (common in model-checker-consumer
            // harnesses after array scalarization), this generates 25k+ SMT checks
            // per predicate and dominates the solve time. Limit to predicates
            // with <= 20 integer variables (20*20*10 = 4000 candidates, manageable).
            if int_vars.len() > 20 {
                continue;
            }

            // For each pair of integer variables, try B = k*C for small k
            for vi in &int_vars {
                if self.is_cancelled() {
                    return;
                }
                for vj in &int_vars {
                    if vi.name == vj.name {
                        continue;
                    }
                    if self.is_cancelled() || ay_core::time::Instant::now() >= counting_deadline {
                        return;
                    }

                    // Try k = 1 to 10
                    for k in 1i128..=10 {
                        let mult_invariant = ChcExpr::eq(
                            ChcExpr::var((*vi).clone()),
                            ChcExpr::mul(ChcExpr::Int(k), ChcExpr::var((*vj).clone())),
                        );

                        // Check if this invariant is already known
                        let already_known = self.frames.len() > 1
                            && self.frames[1]
                                .lemmas
                                .iter()
                                .any(|l| l.predicate == pred.id && l.formula == mult_invariant);
                        if already_known {
                            continue;
                        }

                        // Verify the invariant holds for this predicate
                        // by checking: for all ways to reach pred, the invariant holds
                        if self.verify_multiplicative_invariant(pred.id, &vi.name, &vj.name, k) {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered counting invariant for pred {}: {} = {} * {}",
                                    pred.id.index(),
                                    vi.name,
                                    k,
                                    vj.name
                                );
                            }

                            // IMPORTANT: only stop after successful insertion.
                            // For derived predicates, preservation can hold for many k over
                            // self-loops, but entry-inductiveness usually accepts only the
                            // phase-specific coefficient.
                            let accepted =
                                self.add_discovered_invariant(pred.id, mult_invariant.clone(), 1);
                            if accepted {
                                // For incoming-edge predicates, equality candidates can be
                                // "accepted" via weakening (e.g., to >= / <=) when entry
                                // checks fail. Keep searching until the exact multiplicative
                                // equality is actually present.
                                let exact_installed = self.frames.len() > 1
                                    && self.frames[1].contains_lemma(pred.id, &mult_invariant);
                                if has_incoming && !exact_installed {
                                    continue;
                                }
                                // Found and accepted an invariant for this pair, stop trying
                                // larger k.
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    /// Discover invariants implied by error conditions.
    ///
    /// For error clauses of the form: pred(vars) ∧ guard ∧ ¬conclusion → false
    /// This derives the invariant: guard ⇒ conclusion for the predicate.
    ///
    /// Example (gj2007): inv5(A,B,C) ∧ (A >= 5*C) ∧ (B ≠ 5*C) → false
    /// Derives: (A >= 5*C) ⇒ (B = 5*C) for inv5
    pub(in crate::pdr::solver) fn discover_error_implied_invariants(&mut self) {
        // First collect candidates to avoid borrow conflicts
        let mut candidates: Vec<(PredicateId, ChcExpr, String, String, i128)> = Vec::new();
        let mut direct_candidates: Vec<(PredicateId, ChcExpr)> = Vec::new();

        for (clause_idx, clause) in self.problem.clauses().iter().enumerate() {
            if !matches!(clause.head, crate::ClauseHead::False) {
                continue;
            }

            // Must have exactly one body predicate
            if clause.body.predicates.len() != 1 {
                continue;
            }

            let (pred_id, body_args) = &clause.body.predicates[0];
            let constraint = match &clause.body.constraint {
                Some(c) => c,
                None => continue,
            };

            let canonical_vars = match self.canonical_vars(*pred_id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            if body_args.len() != canonical_vars.len() {
                continue;
            }

            // Build variable map from body args to canonical names
            // #2492: Also extract constituent vars from expression body args
            let mut var_map: FxHashMap<String, (usize, String)> = FxHashMap::default();
            for (idx, (arg, canon)) in body_args.iter().zip(canonical_vars.iter()).enumerate() {
                match arg {
                    ChcExpr::Var(v) => {
                        var_map.insert(v.name.clone(), (idx, canon.name.clone()));
                    }
                    expr => {
                        for v in expr.vars() {
                            var_map
                                .entry(v.name.clone())
                                .or_insert_with(|| (idx, v.name.clone()));
                        }
                    }
                }
            }

            // Try to extract pattern: (A >= k*C) ∧ (B ≠ k*C)
            if let Some((guard, k, conclusion_var, mult_var)) =
                Self::extract_counting_error_pattern(constraint, &var_map)
            {
                // Transform guard to use canonical variable names
                let canonical_guard = Self::transform_to_canonical_vars(&guard, &var_map);
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Found counting error pattern for pred {}: guard={} (canonical={}), k={}, concl_var={}, mult_var={}",
                        pred_id.index(), guard, canonical_guard, k, conclusion_var, mult_var
                    );
                }
                candidates.push((*pred_id, canonical_guard, conclusion_var, mult_var, k));
            }
            // Also try simpler pattern: (guard) ∧ (X ≠ Y) for simple var-var equality
            // This handles gj2007_m_3's error: inv5(B,C,A,D) ∧ (B >= 5*D) ∧ (C != D) → false
            // which yields invariant (B >= 5*D) => (C = D)
            // (#1398: Extended error-implied extraction)
            else if let Some((guard, var1, var2)) =
                Self::extract_simple_negated_equality(constraint, &var_map)
            {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Found simple negated equality pattern for pred {}: guard={}, {} != {}",
                        pred_id.index(), guard, var1, var2
                    );
                }
                // Store with k=1 (no scaling), var1 as conclusion, var2 as "mult" (really just equality partner)
                candidates.push((*pred_id, guard, var1, var2, 1));
            }
            // Pattern: (<= x p) ∧ (>= y p) in an error clause implies x > p ∨ y < p.
            // This captures the remaining dillig21_m error guard shape directly.
            else if let Some(disjunction) =
                Self::extract_interval_conflict_disjunction(constraint, &var_map)
            {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Found interval-conflict error pattern for pred {}: {}",
                        pred_id.index(),
                        disjunction
                    );
                }
                direct_candidates.push((*pred_id, disjunction));
            // Pattern: negated modular equality → (not (= (mod Var K) R)) → false
            // implies invariant (= (mod Var K) R). Captures s_multipl_17: the error
            // clause LOOPX(A) ∧ (not (= (mod A 6) 0)) → false yields (= (mod A 6) 0).
            // (#1362)
            } else if let Some(mod_inv) = Self::extract_negated_mod_equality(constraint, &var_map) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Found negated mod equality for pred {}: {}",
                        pred_id.index(),
                        mod_inv
                    );
                }
                direct_candidates.push((*pred_id, mod_inv));
            } else {
                // #1362 phases_m: Decompose pre-elimination conjunction for mod equalities.
                let mut found_conjunct = false;
                if let Some(pre_elim) = self.original_error_constraints.get(&clause_idx) {
                    let conjuncts = pre_elim.conjuncts();

                    // #1362 s_multipl_17: After multi-def inlining, mod arguments may
                    // reference free variables (e.g., `A`) that are equal to expressions
                    // over var_map variables (e.g., `A = A__inline_7 + B__inline_8`)
                    // via equality conjuncts. Build a substitution from equalities so
                    // `(mod A 6)` becomes `(mod (+ A__inline_7 B__inline_8) 6)`.
                    let subst = Self::build_equality_subst(&conjuncts, &var_map);

                    for conjunct in &conjuncts {
                        // Try direct match first
                        if let Some(mod_inv) =
                            Self::extract_negated_mod_equality(conjunct, &var_map)
                        {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Found negated mod equality in conjunct for pred {}: {} (from pre-elimination constraint)",
                                    pred_id.index(), mod_inv
                                );
                            }
                            direct_candidates.push((*pred_id, mod_inv));
                            found_conjunct = true;
                        }
                        // Try after substitution if direct match fails
                        else if !subst.is_empty() {
                            let substituted = Self::apply_subst(conjunct, &subst);
                            if let Some(mod_inv) =
                                Self::extract_negated_mod_equality(&substituted, &var_map)
                            {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Found negated mod equality after substitution for pred {}: {} (from pre-elimination constraint)",
                                        pred_id.index(), mod_inv
                                    );
                                }
                                direct_candidates.push((*pred_id, mod_inv));
                                found_conjunct = true;
                            }
                        }
                    }
                }
                if !found_conjunct && self.config.verbose {
                    safe_eprintln!(
                        "PDR: Error clause for pred {} has constraint {}, var_map={:?} - pattern not matched",
                        pred_id.index(), constraint, var_map.keys().collect::<Vec<_>>()
                    );
                }
            }
        }

        // Process candidates with mutable access
        if self.config.verbose && !candidates.is_empty() {
            safe_eprintln!(
                "PDR: Processing {} error-implied candidates",
                candidates.len()
            );
        }
        if self.config.verbose && !direct_candidates.is_empty() {
            safe_eprintln!(
                "PDR: Processing {} direct error-implied candidates",
                direct_candidates.len()
            );
        }

        let target_level = 1;
        for (pred_id, invariant) in direct_candidates {
            if self.frames[target_level].contains_lemma(pred_id, &invariant) {
                continue;
            }
            // Check if this is a mod equality invariant (= (mod var k) r) that can be
            // verified algebraically via parity preservation. If the mod is preserved
            // by all transitions, mark the lemma as algebraically_verified so that
            // check_invariants_prove_safety can use the algebraic-only fast path. (#5653)
            let algebraically_verified = Self::extract_mod_equality_components(&invariant)
                .is_some_and(|(var, k, r)| {
                    self.is_parity_preserved_by_transitions(pred_id, &var, k, r)
                });

            if algebraically_verified {
                self.add_discovered_invariant_algebraic(pred_id, invariant.clone(), target_level);
            } else {
                // Error clause pred(vars) ∧ guard(vars) -> false implies pred(vars) -> ¬guard(vars).
                self.add_lemma_to_frame(
                    Lemma::new(pred_id, invariant.clone(), target_level),
                    target_level,
                );
            }
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Discovered direct error-implied invariant for pred {}: {} (algebraic: {})",
                    pred_id.index(),
                    invariant,
                    algebraically_verified
                );
            }
        }

        for (pred_id, guard, conclusion_var, mult_var, k) in candidates {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Trying error-implied invariant for pred {}: {} => {} = {} * {}",
                    pred_id.index(),
                    guard,
                    conclusion_var,
                    k,
                    mult_var
                );
            }
            // Derive invariant: guard ⇒ (conclusion_var = k * mult_var)
            let rhs = if k == 1 {
                ChcExpr::var(ChcVar::new(&mult_var, ChcSort::Int))
            } else {
                ChcExpr::mul(
                    ChcExpr::Int(k),
                    ChcExpr::var(ChcVar::new(&mult_var, ChcSort::Int)),
                )
            };
            let conclusion = ChcExpr::eq(
                ChcExpr::var(ChcVar::new(&conclusion_var, ChcSort::Int)),
                rhs,
            );

            // Build implication: guard ⇒ conclusion = ¬guard ∨ conclusion
            let conditional_invariant =
                ChcExpr::or(ChcExpr::not(guard.clone()), conclusion.clone());

            // Error clauses syntactically imply these invariants:
            //   pred(vars) ∧ guard(vars) ∧ ¬conclusion(vars) → false
            // is equivalent to:
            //   pred(vars) → (guard(vars) → conclusion(vars))
            //
            // So we can add them directly without inductiveness checks.
            if self.frames[target_level].contains_lemma(pred_id, &conditional_invariant) {
                continue;
            }
            // #2459: Route through add_lemma_to_frame for cross-predicate propagation.
            self.add_lemma_to_frame(
                Lemma::new(pred_id, conditional_invariant, target_level),
                target_level,
            );
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Discovered error-implied invariant for pred {}: {} => {} = {} * {}",
                    pred_id.index(),
                    guard,
                    conclusion_var,
                    k,
                    mult_var
                );
            }
        }
    }
}
