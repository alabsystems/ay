// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Generate all currently-known bound axiom term pairs for testing and API wrappers.
    pub fn generate_bound_axiom_terms_inner(&self) -> Vec<(TermId, bool, TermId, bool)> {
        let mut axioms = Vec::new();
        // #8529: Use deterministic HashSet (module-level import) to ensure
        // axiom dedup is consistent across process runs.
        let mut seen = HashSet::default();
        let mut total_indexed = 0usize;
        let mut vars_with_bounds = 0usize;
        let mut max_bounds = 0usize;
        let compound_wakeup_vars = self
            .compound_use_index
            .values()
            .filter(|atoms| !atoms.is_empty())
            .count();
        let compound_wakeup_edges = self
            .compound_use_index
            .values()
            .map(Vec::len)
            .sum::<usize>();
        for atoms in self.atom_index.values() {
            total_indexed += atoms.len();
            if atoms.len() >= 2 {
                vars_with_bounds += 1;
                max_bounds = max_bounds.max(atoms.len());
            }
        }
        // Count single-atom vars (no axiom pairing possible).
        let single_atom_vars = self
            .atom_index
            .values()
            .filter(|atoms| atoms.len() == 1)
            .count();
        if total_indexed > 0 || compound_wakeup_edges > 0 {
            tracing::info!(
                atom_index_vars = self.atom_index.len(),
                vars_with_bounds,
                single_atom_vars,
                total_indexed,
                max_bounds,
                compound_wakeup_vars,
                compound_wakeup_edges,
                compound_queued = self.last_compound_propagations_queued,
                "Bound axiom generation stats (#4919)"
            );
        }
        let same_var_start = axioms.len();
        for atoms in self.atom_index.values() {
            if atoms.len() < 2 {
                continue;
            }
            // #8256: All-pairs bound axiom generation for variables with
            // moderate numbers of bounds. Z3 generates axioms between ALL
            // bounds on the same theory variable (mk_bound_axioms in
            // arith_axioms.cpp). The nearest-neighbor strategy relies on
            // BCP transitivity chains (x>=3 -> x>=2 -> x>=1), but each
            // chain step triggers a theory callback with O(vars*atoms) cost.
            // All-pairs generates direct implications (x>=3 -> x>=1),
            // allowing BCP to propagate without theory callbacks.
            //
            // For variables with <= ALL_PAIRS_THRESHOLD bounds, generate
            // O(n^2) axioms. This covers 99%+ of variables in practice
            // (max_bounds is typically 4-14). Above the threshold, fall
            // back to nearest-neighbor to avoid quadratic clause blowup.
            //
            // Empirically on simple_startup_10nodes: nearest-neighbor
            // generates ~1366 axioms. All-pairs (threshold=20) generates
            // ~10x more, matching Z3's 15408 binary clauses.
            const ALL_PAIRS_THRESHOLD: usize = 30;

            if atoms.len() <= ALL_PAIRS_THRESHOLD {
                // All-pairs: generate axioms between every pair of atoms.
                for (i, a1) in atoms.iter().enumerate() {
                    for a2 in atoms.iter().skip(i + 1) {
                        if a1.term == a2.term {
                            continue;
                        }
                        self.mk_bound_axiom_terms(a1, a2, &mut axioms, &mut seen);
                        self.mk_bound_axiom_terms(a2, a1, &mut axioms, &mut seen);
                    }
                }
            } else {
                // Fall back to nearest-neighbor for variables with many bounds.
                for (i, a1) in atoms.iter().enumerate() {
                    let mut lo_inf: Option<&AtomRef> = None;
                    let mut hi_inf: Option<&AtomRef> = None;
                    let mut lo_sup: Option<&AtomRef> = None;
                    let mut hi_sup: Option<&AtomRef> = None;

                    // Scan backwards for nearest neighbors with bound_value <= a1
                    for j in (0..i).rev() {
                        let a2 = &atoms[j];
                        if a2.term == a1.term {
                            continue;
                        }
                        if !a2.is_upper {
                            if lo_inf.is_none() {
                                lo_inf = Some(a2);
                            }
                        } else if hi_inf.is_none() {
                            hi_inf = Some(a2);
                        }
                        if lo_inf.is_some() && hi_inf.is_some() {
                            break;
                        }
                    }

                    // Scan forwards for nearest neighbors with bound_value >= a1
                    for a2 in atoms.iter().skip(i + 1) {
                        if a2.term == a1.term {
                            continue;
                        }
                        if !a2.is_upper {
                            if lo_sup.is_none() {
                                lo_sup = Some(a2);
                            }
                        } else if hi_sup.is_none() {
                            hi_sup = Some(a2);
                        }
                        if lo_sup.is_some() && hi_sup.is_some() {
                            break;
                        }
                    }

                    for neighbor in [lo_inf, lo_sup, hi_inf, hi_sup].into_iter().flatten() {
                        self.mk_bound_axiom_terms(a1, neighbor, &mut axioms, &mut seen);
                    }
                }
            }
        }
        let same_var_count = axioms.len() - same_var_start;
        let cross_neg_start = axioms.len();
        // #8422: Cross-proportional axiom generation for compound atoms.
        //
        // Generalization of the #8452 cross-negation approach. Two slack
        // variables s1 and s2 are "proportional" when their coefficient
        // vectors differ only by a scalar multiple k:
        //   key2[i] = k * key1[i]  for all i
        //
        // When k = -1 this is the negation case: s1 + s2 = oc1 + oc2.
        // In general: s2 = k * s1 + (oc2 - k * oc1).
        //
        // For positive k (same direction):
        //   s1 <= b  =>  s2 <= k*b + offset  (upper on s1 maps to upper on s2)
        //   s1 >= b  =>  s2 >= k*b + offset  (lower on s1 maps to lower on s2)
        //
        // For negative k (opposite direction):
        //   s1 <= b  =>  s2 >= k*b + offset  (upper on s1 maps to lower on s2)
        //   s1 >= b  =>  s2 <= k*b + offset  (lower on s1 maps to upper on s2)
        //
        // k = -1 is the classic negation partner case. Projection onto s1's
        // bound space uses bound_value' = (b - offset) / k, with direction
        // flipped when k < 0.
        //
        // Z3 handles this implicitly: it uses one theory variable for each
        // normalized expression (sign-canonicalized), so all atoms naturally
        // land on the same variable. AY creates separate slacks, requiring
        // explicit cross-slack axiom generation.
        //
        // Reference: Z3 arith_axioms.cpp mk_bound_axioms — all bounds on the
        // same theory variable.
        {
            // Normalize each expression key to a canonical direction for
            // proportionality detection. The canonical form has the first
            // coefficient positive. Two keys are proportional iff their
            // canonical forms (after dividing by the first coefficient) match.
            //
            // canonical_key(key) = (vars, normalized_coeffs) where
            //   normalized_coeffs[i] = key[i].coeff / key[0].coeff
            // Two keys are proportional when their canonical forms match.
            // The proportionality constant k = key2[0].coeff / key1[0].coeff.
            //
            // Group all slacks by canonical key, then generate cross-axioms
            // between all pairs in each group.
            let mut canonical_groups: HashMap<
                Vec<(u32, Rational)>,
                Vec<(u32, Rational, Rational)>,
            > = HashMap::default();
            // canonical_groups maps canonical_key -> vec of (slack, proportionality_factor_k, orig_constant)
            // where s_i = k_i * canonical_expr + oc_i

            for (key, &(slack, ref oc)) in &self.expr_to_slack {
                if key.is_empty() {
                    continue;
                }
                let first_coeff = &key[0].1;
                if first_coeff.is_zero() {
                    continue;
                }
                // Normalize: divide all coefficients by the first coefficient.
                let canonical: Vec<(u32, Rational)> =
                    key.iter().map(|(v, c)| (*v, c / first_coeff)).collect();
                // The proportionality factor k: s = k * canonical_expr + oc
                // where canonical_expr has first coefficient = 1.
                // k = first_coeff (since canonical = key / first_coeff, so key = first_coeff * canonical)
                canonical_groups.entry(canonical).or_default().push((
                    slack,
                    first_coeff.clone(),
                    oc.clone(),
                ));
            }

            // #8529: Use deterministic HashSet for pair dedup.
            let mut processed_pairs: HashSet<(u32, u32)> = HashSet::default();

            for group in canonical_groups.values() {
                if group.len() < 2 {
                    continue;
                }
                // Generate cross-axioms for all pairs in this proportionality group.
                for i in 0..group.len() {
                    let (s1, ref k1, ref oc1) = group[i];
                    let Some(atoms1) = self.atom_index.get(&s1) else {
                        continue;
                    };
                    if atoms1.is_empty() {
                        continue;
                    }
                    for (s2, k2, oc2) in group.iter().skip(i + 1) {
                        let s2 = *s2;
                        if s1 == s2 {
                            continue;
                        }
                        let pair = if s1 < s2 { (s1, s2) } else { (s2, s1) };
                        if !processed_pairs.insert(pair) {
                            continue;
                        }
                        let Some(atoms2) = self.atom_index.get(&s2) else {
                            continue;
                        };
                        if atoms2.is_empty() {
                            continue;
                        }

                        // Relationship: s1 = k1 * C + oc1, s2 = k2 * C + oc2
                        // where C is the canonical expression.
                        // => C = (s1 - oc1) / k1 = (s2 - oc2) / k2
                        // => s2 = (k2/k1) * s1 + (oc2 - k2/k1 * oc1)
                        //       = ratio * s1 + offset
                        let ratio = k2 / k1;
                        let ratio_times_oc1 = &ratio * oc1;
                        let offset = oc2 - &ratio_times_oc1;
                        let ratio_positive = ratio.is_positive();

                        // Project atoms from s2 onto s1's bound space:
                        // s2 OP b  <=>  ratio * s1 + offset OP b
                        //           <=>  s1 OP' (b - offset) / ratio
                        // Direction flips when ratio is negative.
                        let projected_from_2: Vec<AtomRef> = atoms2
                            .iter()
                            .map(|a| {
                                let projected_bv = &(&a.bound_value - &offset) / &ratio;
                                AtomRef {
                                    term: a.term,
                                    bound_value: projected_bv,
                                    is_upper: if ratio_positive {
                                        a.is_upper
                                    } else {
                                        !a.is_upper
                                    },
                                    strict: a.strict,
                                }
                            })
                            .collect();

                        // Generate axioms: atoms1 vs projected atoms2.
                        for a1 in atoms1 {
                            for a2 in &projected_from_2 {
                                if a1.term == a2.term {
                                    continue;
                                }
                                self.mk_bound_axiom_terms(a1, a2, &mut axioms, &mut seen);
                            }
                        }

                        // Project atoms from s1 onto s2's bound space:
                        // s1 OP b  <=>  (s2 - offset) / ratio OP b
                        //           <=>  s2 OP' ratio * b + offset
                        // Direction flips when ratio is negative.
                        let projected_from_1: Vec<AtomRef> = atoms1
                            .iter()
                            .map(|a| {
                                let projected_bv = &(&ratio * &a.bound_value) + &offset;
                                AtomRef {
                                    term: a.term,
                                    bound_value: projected_bv,
                                    is_upper: if ratio_positive {
                                        a.is_upper
                                    } else {
                                        !a.is_upper
                                    },
                                    strict: a.strict,
                                }
                            })
                            .collect();

                        // Generate axioms: atoms2 vs projected atoms1.
                        for a2 in atoms2 {
                            for a1 in &projected_from_1 {
                                if a2.term == a1.term {
                                    continue;
                                }
                                self.mk_bound_axiom_terms(a2, a1, &mut axioms, &mut seen);
                            }
                        }
                    }
                }
            }
        }
        let cross_neg_count = axioms.len() - cross_neg_start;
        let eq_start = axioms.len();

        // Generate axioms connecting equality atoms to bound atoms (#4919).
        // For each single-variable equality (= x k), generate:
        //   ~eq ∨ bound   when eq implies bound  (x=k → x>=k' when k'<=k)
        //   ~eq ∨ ~bound  when eq contradicts bound (x=k → ¬(x>=k') when k'>k)
        // This connects equality atoms to the bound ordering system without
        // decomposing the equality, preserving the original equality semantics
        // for the theory solver while enabling BCP propagation.
        for (&eq_term, cached) in &self.atom_cache {
            let Some(info) = cached else { continue };
            if !info.is_eq || info.expr.coeffs.len() != 1 {
                continue;
            }
            let (var, ref coeff) = info.expr.coeffs[0];
            if coeff.is_zero() {
                continue;
            }
            let k = (-info.expr.constant.clone() / coeff.clone()).to_big();
            let Some(bounds) = self.atom_index.get(&var) else {
                continue;
            };
            for bound in bounds {
                if bound.term == eq_term {
                    continue;
                }
                if !bound.is_upper {
                    let implies = if bound.strict {
                        bound.bound_value < k
                    } else {
                        bound.bound_value <= k
                    };
                    if implies {
                        let key = if eq_term <= bound.term {
                            (eq_term, bound.term)
                        } else {
                            (bound.term, eq_term)
                        };
                        if seen.insert(key) {
                            axioms.push((eq_term, false, bound.term, true));
                        }
                    }
                    let contradicts = if bound.strict {
                        bound.bound_value >= k
                    } else {
                        bound.bound_value > k
                    };
                    if contradicts {
                        axioms.push((eq_term, false, bound.term, false));
                    }
                } else {
                    let implies = if bound.strict {
                        bound.bound_value > k
                    } else {
                        bound.bound_value >= k
                    };
                    if implies {
                        let key = if eq_term <= bound.term {
                            (eq_term, bound.term)
                        } else {
                            (bound.term, eq_term)
                        };
                        if seen.insert(key) {
                            axioms.push((eq_term, false, bound.term, true));
                        }
                    }
                    let contradicts = if bound.strict {
                        bound.bound_value <= k
                    } else {
                        bound.bound_value < k
                    };
                    if contradicts {
                        axioms.push((eq_term, false, bound.term, false));
                    }
                }
            }
        }
        let eq_count = axioms.len() - eq_start;

        // #8596: Generate equality-to-equality exclusion axioms.
        // When two equality atoms (= x k1) and (= x k2) exist on the same
        // LRA variable with k1 != k2, they are mutually exclusive:
        //   NOT(x=k1) OR NOT(x=k2)
        //
        // Without this, the SAT solver can set both x=0 and x=1 to true
        // simultaneously (via default phase), causing the theory solver to
        // see contradictory values for x and produce a false UNSAT. This is
        // critical for AUFLIA where select(a,y) is an uninterpreted term
        // mapped to a single LRA variable, and ITE expansion creates
        // competing equality atoms like (= select(a,y) 0) and (= select(a,y) 1).
        //
        // Z3 handles this in mk_bound_axioms (arith_axioms.cpp) since
        // equalities are decomposed into upper+lower bounds that land in the
        // same atom_index. AY keeps equalities out of atom_index, so we need
        // explicit exclusion axioms.
        let eq_excl_start = axioms.len();
        {
            // Collect single-variable equalities grouped by their variable.
            let mut eq_by_var: HashMap<u32, Vec<(TermId, Rational)>> = HashMap::default();
            for (&eq_term, cached) in &self.atom_cache {
                let Some(info) = cached else { continue };
                if !info.is_eq || info.expr.coeffs.len() != 1 {
                    continue;
                }
                let (var, ref coeff) = info.expr.coeffs[0];
                if coeff.is_zero() {
                    continue;
                }
                let k = -info.expr.constant.clone() / coeff.clone();
                eq_by_var.entry(var).or_default().push((eq_term, k));
            }
            // For each pair of equalities on the same variable with different
            // values, emit NOT(eq1) OR NOT(eq2).
            for eqs in eq_by_var.values() {
                if eqs.len() < 2 {
                    continue;
                }
                for i in 0..eqs.len() {
                    for j in (i + 1)..eqs.len() {
                        let (t1, ref k1) = eqs[i];
                        let (t2, ref k2) = eqs[j];
                        if k1 == k2 {
                            continue; // Same value — not exclusive
                        }
                        let key = if t1 <= t2 { (t1, t2) } else { (t2, t1) };
                        if seen.insert(key) {
                            // ~eq1 ∨ ~eq2
                            axioms.push((t1, false, t2, false));
                        }
                    }
                }
            }
        }
        let eq_excl_count = axioms.len() - eq_excl_start;

        if !axioms.is_empty() {
            tracing::info!(
                total = axioms.len(),
                same_var = same_var_count,
                cross_proportional = cross_neg_count,
                equality = eq_count,
                equality_exclusion = eq_excl_count,
                "Bound axiom breakdown (#8422)"
            );
        }
        axioms
    }

    /// Build the negation_partners map from expr_to_slack (#8008).
    ///
    /// For each slack variable S1 with expression key K, check if the negated
    /// key (-K) also has a slack variable S2. If so, S1 + S2 = oc1 + oc2 = K_constant.
    /// Store the partnership so that implied bounds can propagate between negation pairs
    /// during `compute_implied_bounds()`.
    ///
    /// This mirrors the cross-negation axiom detection in `generate_bound_axiom_terms_inner()`
    /// but builds a runtime lookup table instead of SAT clauses.
    pub(crate) fn build_negation_partners(&mut self) {
        // Determine max slack var id for sizing the vector.
        let max_slack = self.slack_var_set.iter().copied().max().unwrap_or(0) as usize;
        self.negation_partners.clear();
        self.negation_partners.resize(max_slack + 1, None);

        let keys: Vec<Vec<(u32, Rational)>> = self.expr_to_slack.keys().cloned().collect();
        let mut processed_pairs: HashSet<(u32, u32)> = HashSet::default();

        for key in &keys {
            let neg_key: Vec<(u32, Rational)> = key.iter().map(|(v, c)| (*v, -c.clone())).collect();

            let Some(&(s1, ref oc1)) = self.expr_to_slack.get(key) else {
                continue;
            };
            let Some(&(s2, ref oc2)) = self.expr_to_slack.get(&neg_key) else {
                continue;
            };
            if s1 == s2 {
                continue;
            }
            let pair = if s1 < s2 { (s1, s2) } else { (s2, s1) };
            if !processed_pairs.insert(pair) {
                continue;
            }

            let k_sum = oc1 + oc2; // K = oc1 + oc2, the constant sum s1 + s2

            // Ensure both indices fit.
            let max_id = std::cmp::max(s1, s2) as usize;
            if max_id >= self.negation_partners.len() {
                self.negation_partners.resize(max_id + 1, None);
            }

            self.negation_partners[s1 as usize] = Some((s2, k_sum.clone()));
            self.negation_partners[s2 as usize] = Some((s1, k_sum));
        }

        if self.debug_lra && !processed_pairs.is_empty() {
            safe_eprintln!(
                "[LRA] Built {} cross-negation partner pairs for bound propagation (#8008)",
                processed_pairs.len(),
            );
        }
    }

    /// Generate bound axiom term pairs newly exposed by one registered atom.
    pub fn generate_incremental_bound_axioms_inner(
        &self,
        atom: TermId,
    ) -> Vec<(TermId, bool, TermId, bool)> {
        let Some(Some(info)) = self.atom_cache.get(&atom) else {
            return Vec::new();
        };
        if info.is_distinct {
            return Vec::new();
        }
        // #8596: For equality atoms, generate exclusion axioms against other
        // equalities on the same variable, plus eq-to-bound axioms.
        if info.is_eq {
            return self.generate_incremental_eq_exclusion_axioms(atom, info);
        }

        // Determine the variable (or slack) and bound parameters for this atom.
        // Single-variable atoms: var is the coefficient variable, bound_value = -constant/coeff.
        // Compound atoms (#8008): var is the slack variable, bound_value = orig_constant - constant.
        let (var, bound_value, is_upper) = if info.expr.coeffs.len() == 1 {
            let (v, coeff) = &info.expr.coeffs[0];
            if coeff.is_zero() {
                return Vec::new();
            }
            let bv = -info.expr.constant.clone() / coeff.clone();
            let coeff_positive = coeff.is_positive();
            let iu = matches!((info.is_le, coeff_positive), (true, true) | (false, false));
            (*v, bv, iu)
        } else if info.expr.coeffs.len() > 1 {
            // Compound atom: look up the slack variable.
            // First try the precomputed compound_slack field.
            let slack = if let Some(s) = info.compound_slack {
                s
            } else {
                // Fallback: look up in atom_slack.
                // atom_slack is keyed by (term, is_le) for the positive polarity.
                if let Some(&(s, _)) = self.atom_slack.get(&(atom, true)) {
                    s
                } else if let Some(&(s, _)) = self.atom_slack.get(&(atom, false)) {
                    s
                } else {
                    return Vec::new();
                }
            };
            // Get the original constant for this slack to compute bound_value.
            // The bound_value for a compound atom on slack S is: orig_constant - expr.constant
            // where orig_constant is the constant stored in expr_to_slack for S.
            let mut key: Vec<(u32, Rational)> = info
                .expr
                .coeffs
                .iter()
                .map(|(v, c)| (*v, c.clone()))
                .collect();
            key.sort_by_key(|(v, _)| *v);
            let orig_constant = if let Some((_, oc)) = self.expr_to_slack.get(&key) {
                oc.clone()
            } else {
                return Vec::new();
            };
            let bv = &orig_constant - &info.expr.constant;
            let iu = info.is_le;
            (slack, bv, iu)
        } else {
            return Vec::new();
        };

        let Some(existing) = self.atom_index.get(&var) else {
            return Vec::new();
        };
        if existing.is_empty() {
            return Vec::new();
        }

        let new_ref = AtomRef {
            term: atom,
            bound_value,
            is_upper,
            strict: info.strict,
        };

        let mut lo_inf: Option<&AtomRef> = None;
        let mut lo_sup: Option<&AtomRef> = None;
        let mut hi_inf: Option<&AtomRef> = None;
        let mut hi_sup: Option<&AtomRef> = None;

        for existing_atom in existing {
            if existing_atom.term == atom {
                continue;
            }
            if existing_atom.bound_value == new_ref.bound_value
                && existing_atom.is_upper == new_ref.is_upper
                && existing_atom.strict == new_ref.strict
            {
                continue;
            }
            let k2 = &existing_atom.bound_value;
            if !existing_atom.is_upper {
                if *k2 < new_ref.bound_value {
                    if lo_inf.is_none_or(|b| *k2 > b.bound_value) {
                        lo_inf = Some(existing_atom);
                    }
                } else if lo_sup.is_none_or(|b| *k2 < b.bound_value) {
                    lo_sup = Some(existing_atom);
                }
            } else if *k2 < new_ref.bound_value {
                if hi_inf.is_none_or(|b| *k2 > b.bound_value) {
                    hi_inf = Some(existing_atom);
                }
            } else if hi_sup.is_none_or(|b| *k2 < b.bound_value) {
                hi_sup = Some(existing_atom);
            }
        }

        let mut axioms = Vec::new();
        // #8529: Use deterministic HashSet for axiom dedup.
        let mut seen = HashSet::default();
        for neighbor in [lo_inf, lo_sup, hi_inf, hi_sup].into_iter().flatten() {
            self.mk_bound_axiom_terms(&new_ref, neighbor, &mut axioms, &mut seen);
        }

        // #8008: For compound atoms, also generate cross-negation axioms.
        // If this atom is on slack S1, and there exists a negation partner S2
        // such that S1 + S2 = K, generate axioms between the new atom and
        // atoms on S2 (projected onto S1's bound space).
        if info.expr.coeffs.len() > 1 {
            if let Some(Some((partner_slack, ref k_sum))) = self.negation_partners.get(var as usize)
            {
                let partner_slack = *partner_slack;
                let k_sum = k_sum.clone();
                if let Some(partner_atoms) = self.atom_index.get(&partner_slack) {
                    for pa in partner_atoms {
                        if pa.term == atom {
                            continue;
                        }
                        // Project partner atom onto our slack's bound space:
                        // S1 + S2 = K, so S2 = K - S1.
                        // An atom `S2 OP b` becomes `S1 OP_flip K - b`.
                        let projected = AtomRef {
                            term: pa.term,
                            bound_value: &k_sum - &pa.bound_value,
                            is_upper: !pa.is_upper,
                            strict: pa.strict,
                        };
                        self.mk_bound_axiom_terms(&new_ref, &projected, &mut axioms, &mut seen);
                    }
                }
            }
        }

        axioms
    }

    /// #8596: Generate incremental equality exclusion axioms for a new
    /// equality atom. For each other equality (= x k') on the same
    /// LRA variable with k' != k, emit NOT(x=k) OR NOT(x=k').
    /// Also generates eq-to-bound axioms (same logic as bulk generation).
    fn generate_incremental_eq_exclusion_axioms(
        &self,
        atom: TermId,
        info: &ParsedAtomInfo,
    ) -> Vec<(TermId, bool, TermId, bool)> {
        let mut axioms = Vec::new();
        if info.expr.coeffs.len() != 1 {
            return axioms;
        }
        let (var, ref coeff) = info.expr.coeffs[0];
        if coeff.is_zero() {
            return axioms;
        }
        let k = -info.expr.constant.clone() / coeff.clone();

        // Scan all cached atoms for other equalities on the same variable.
        for (&other_term, cached) in &self.atom_cache {
            if other_term == atom {
                continue;
            }
            let Some(other_info) = cached else { continue };
            if !other_info.is_eq || other_info.expr.coeffs.len() != 1 {
                continue;
            }
            let (other_var, ref other_coeff) = other_info.expr.coeffs[0];
            if other_var != var || other_coeff.is_zero() {
                continue;
            }
            let other_k = -other_info.expr.constant.clone() / other_coeff.clone();
            if k != other_k {
                // Different values on same variable: mutually exclusive.
                axioms.push((atom, false, other_term, false)); // ~eq1 ∨ ~eq2
            }
        }

        // Also generate eq-to-bound axioms for this new equality.
        if let Some(bounds) = self.atom_index.get(&var) {
            let k_big = k.to_big();
            for bound in bounds {
                if bound.term == atom {
                    continue;
                }
                if !bound.is_upper {
                    let implies = if bound.strict {
                        bound.bound_value < k_big
                    } else {
                        bound.bound_value <= k_big
                    };
                    if implies {
                        axioms.push((atom, false, bound.term, true)); // ~eq ∨ bound
                    }
                    let contradicts = if bound.strict {
                        bound.bound_value >= k_big
                    } else {
                        bound.bound_value > k_big
                    };
                    if contradicts {
                        axioms.push((atom, false, bound.term, false)); // ~eq ∨ ~bound
                    }
                } else {
                    let implies = if bound.strict {
                        bound.bound_value > k_big
                    } else {
                        bound.bound_value >= k_big
                    };
                    if implies {
                        axioms.push((atom, false, bound.term, true)); // ~eq ∨ bound
                    }
                    let contradicts = if bound.strict {
                        bound.bound_value <= k_big
                    } else {
                        bound.bound_value < k_big
                    };
                    if contradicts {
                        axioms.push((atom, false, bound.term, false)); // ~eq ∨ ~bound
                    }
                }
            }
        }

        axioms
    }
}
