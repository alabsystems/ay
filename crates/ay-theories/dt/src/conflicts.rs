// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conflict detection for the DT theory solver.
//!
//! Implements constructor clash, injectivity, tester, disequality, and acyclicity checks.
//!
//! ## Allocation strategy (#8599)
//!
//! All temporary data structures (class groupings, DFS state, BFS state) are stored
//! as persistent buffers on `DtSolver` and cleared/reused on each `check()` call.
//! This avoids per-call heap allocations in the DPLL(T) hot loop.

use super::*;

impl DtSolver<'_> {
    /// Build a conflict clause from all asserted equality literals.
    fn eq_lits_as_conflict(&self) -> Vec<TheoryLit> {
        self.asserted_eq_lits
            .iter()
            .copied()
            .map(|t| TheoryLit::new(t, true))
            .collect()
    }

    /// Check for constructor clash in an equivalence class.
    ///
    /// Returns Some(conflict) if two different constructors are in the same class.
    ///
    /// Uses `buf_sorted_ctor_keys`, `buf_class_groups`, `buf_sorted_reps` as
    /// persistent buffers to avoid per-call allocation (#8599).
    pub(super) fn check_clash(&mut self) -> Option<Vec<TheoryLit>> {
        // Clear and reuse persistent buffers.
        self.buf_sorted_ctor_keys.clear();
        self.buf_sorted_ctor_keys
            .extend(self.term_constructors.keys().copied());
        self.buf_sorted_ctor_keys.sort_unstable_by_key(|t| t.0);

        self.buf_class_groups.clear();
        for &term_id in &self.buf_sorted_ctor_keys {
            let rep = self.find(term_id);
            // Store (term_id, index_into_sorted_ctor_keys) — we use term_id directly
            // and look up ConstructorInfo from term_constructors when needed.
            self.buf_class_groups
                .entry(rep)
                .or_default()
                .push((term_id, 0));
        }

        // Sorted class representatives for deterministic iteration.
        self.buf_sorted_reps.clear();
        self.buf_sorted_reps
            .extend(self.buf_class_groups.keys().copied());
        self.buf_sorted_reps.sort_unstable_by_key(|t| t.0);

        for &rep in &self.buf_sorted_reps {
            let ctors = &self.buf_class_groups[&rep];
            if ctors.len() < 2 {
                continue;
            }

            // Check if all constructors have the same name (same datatype).
            let first_info = &self.term_constructors[&ctors[0].0];
            let first_ctor = &first_info.ctor_name;
            let first_dt = &first_info.dt_name;

            for &(term_id, _) in &ctors[1..] {
                let info = &self.term_constructors[&term_id];
                if &info.dt_name == first_dt && &info.ctor_name != first_ctor {
                    // Constructor clash! Different constructors in same class.
                    let first_term = ctors[0].0;
                    if self.asserted_eq_lits.is_empty() {
                        return Some(vec![
                            TheoryLit::new(first_term, true),
                            TheoryLit::new(term_id, true),
                        ]);
                    }

                    let reasons = self.explain_equality(first_term, term_id);
                    let mut c: Vec<TheoryLit> = if reasons.is_empty() {
                        self.eq_lits_as_conflict()
                    } else {
                        reasons
                            .into_iter()
                            .map(|t| TheoryLit::new(t, true))
                            .collect()
                    };
                    c.sort_by_key(|l| (l.term.0, l.value));
                    c.dedup_by_key(|l| (l.term.0, l.value));
                    return Some(c);
                }
            }
        }

        None
    }

    /// Check for injectivity conflicts and generate propagations.
    ///
    /// When C(a1, ..., an) = C(b1, ..., bn), we have a1 = b1, ..., an = bn by injectivity.
    /// If any of these equalities conflicts with an asserted disequality, return a conflict.
    /// Otherwise, queue them for Nelson-Oppen propagation.
    ///
    /// Uses `buf_sorted_ctor_keys`, `buf_class_groups`, `buf_sorted_reps` as
    /// persistent buffers (#8599).
    pub(super) fn check_injectivity_conflicts(&mut self) -> Option<Vec<TheoryLit>> {
        // Clear and reuse persistent buffers.
        self.buf_sorted_ctor_keys.clear();
        self.buf_sorted_ctor_keys
            .extend(self.term_constructors.keys().copied());
        self.buf_sorted_ctor_keys.sort_unstable_by_key(|t| t.0);

        self.buf_class_groups.clear();
        for &term_id in &self.buf_sorted_ctor_keys {
            let rep = self.find(term_id);
            self.buf_class_groups
                .entry(rep)
                .or_default()
                .push((term_id, 0));
        }

        self.buf_sorted_reps.clear();
        self.buf_sorted_reps
            .extend(self.buf_class_groups.keys().copied());
        self.buf_sorted_reps.sort_unstable_by_key(|t| t.0);

        // Iterate over classes. We need to read from buf_class_groups while also
        // mutating self (for union, pending_injectivity_eqs, etc.), so we clone
        // the sorted_reps and iterate over that.
        let sorted_reps: Vec<TermId> = self.buf_sorted_reps.clone();

        for rep in sorted_reps {
            let ctors: Vec<(TermId, usize)> = self.buf_class_groups[&rep].clone();
            if ctors.len() < 2 {
                continue;
            }

            // Extract (term_id, ctor_name, args) into owned data so we can
            // release the borrow on self.term_constructors before mutation (#8599).
            // This inner collection is proportional to the class size (typically small).
            let ctor_data: Vec<(TermId, String, Vec<TermId>)> = ctors
                .iter()
                .filter_map(|&(term_id, _)| {
                    self.term_constructors
                        .get(&term_id)
                        .map(|info| (term_id, info.ctor_name.clone(), info.args.clone()))
                })
                .collect();

            // Group by constructor name.
            let mut by_ctor: HashMap<&str, Vec<usize>> = HashMap::default();
            for (i, (_, ctor_name, _)) in ctor_data.iter().enumerate() {
                by_ctor.entry(ctor_name.as_str()).or_default().push(i);
            }

            let mut sorted_ctor_names: Vec<&str> = by_ctor.keys().copied().collect();
            sorted_ctor_names.sort_unstable();

            for ctor_name in sorted_ctor_names {
                let indices = &by_ctor[ctor_name];
                if indices.len() < 2 {
                    continue;
                }

                let arity = ctor_data[indices[0]].2.len();
                if indices.iter().any(|&i| ctor_data[i].2.len() != arity) {
                    continue;
                }

                for field_idx in 0..arity {
                    let mut args: Vec<TermId> = Vec::with_capacity(indices.len());
                    let mut arg_set: HashSet<TermId> = Default::default();

                    for &i in indices {
                        let arg = ctor_data[i].2[field_idx];
                        if arg_set.insert(arg) {
                            args.push(arg);
                        }
                    }

                    if args.len() <= 1 {
                        continue;
                    }

                    // Disequality between required-equal args -> conflict.
                    for diseq_idx in 0..self.asserted_diseqs.len() {
                        let (diseq_lhs, diseq_rhs, diseq_lit) = self.asserted_diseqs[diseq_idx];
                        if arg_set.contains(&diseq_lhs) && arg_set.contains(&diseq_rhs) {
                            let parent_a = ctor_data[indices[0]].0;
                            let parent_b = indices
                                .iter()
                                .find(|&&i| {
                                    ctor_data[i].2.get(field_idx) == Some(&diseq_rhs)
                                        || ctor_data[i].2.get(field_idx) == Some(&diseq_lhs)
                                })
                                .map(|&i| ctor_data[i].0)
                                .unwrap_or(ctor_data[indices[1]].0);
                            let reasons = self.explain_equality(parent_a, parent_b);
                            let mut c: Vec<TheoryLit> = if reasons.is_empty() {
                                self.eq_lits_as_conflict()
                            } else {
                                reasons
                                    .into_iter()
                                    .map(|t| TheoryLit::new(t, true))
                                    .collect()
                            };
                            c.push(TheoryLit::new(diseq_lit, false));
                            c.sort_by_key(|l| (l.term.0, l.value));
                            c.dedup_by_key(|l| (l.term.0, l.value));
                            return Some(c);
                        }
                    }

                    // Merge in union-find (#5082) and queue for N-O propagation.
                    let arg_rep = args[0];
                    for &other in &args[1..] {
                        self.union(arg_rep, other);
                        let pair = if arg_rep.0 < other.0 {
                            (arg_rep, other)
                        } else {
                            (other, arg_rep)
                        };
                        if !self.propagated_eq_pairs.contains(&pair) {
                            self.propagated_eq_pairs.insert(pair);
                            let parent_a = ctor_data[indices[0]].0;
                            let parent_b = ctor_data[indices[1]].0;
                            let reasons = self.explain_equality(parent_a, parent_b);
                            let reason: Vec<TheoryLit> = if reasons.is_empty() {
                                self.eq_lits_as_conflict()
                            } else {
                                reasons
                                    .into_iter()
                                    .map(|t| TheoryLit::new(t, true))
                                    .collect()
                            };
                            self.pending_injectivity_eqs
                                .push(DiscoveredEquality::new(pair.0, pair.1, reason));
                        }
                    }
                }
            }
        }

        None
    }

    /// Upward constructor congruence (#dt-congruence).
    ///
    /// If two applications of the **same** constructor `C(a1,...,an)` and
    /// `C(b1,...,bn)` have every argument pair already merged in the union-find
    /// (`find(a_i) == find(b_i)` for all `i`), then by congruence the two
    /// constructor terms denote the same value and must be merged:
    /// `C(a1,...,an) = C(b1,...,bn)`.
    ///
    /// Example (reproducer 3): `a = zero` ⇒ `succ(a) = succ(zero)`, which
    /// contradicts an asserted `succ(a) != succ(zero)`.
    ///
    /// The merge is justified by the union of the argument-equality reasons, so
    /// the reason-graph edge carries the full reason set for explanation. This
    /// runs to a fixpoint within a single `check()` (merging two constructor
    /// terms can equalize further argument pairs, enabling more congruence).
    ///
    /// Returns `true` if any new merge was performed.
    pub(super) fn apply_constructor_congruence(&mut self) -> bool {
        let mut changed_any = false;
        loop {
            // Snapshot constructor terms with their (ctor_name, args), sorted by
            // term id for determinism.
            self.buf_sorted_ctor_keys.clear();
            self.buf_sorted_ctor_keys
                .extend(self.term_constructors.keys().copied());
            self.buf_sorted_ctor_keys.sort_unstable_by_key(|t| t.0);

            let ctor_data: Vec<(TermId, String, Vec<TermId>)> = self
                .buf_sorted_ctor_keys
                .iter()
                .filter_map(|&t| {
                    self.term_constructors
                        .get(&t)
                        .map(|info| (t, info.ctor_name.clone(), info.args.clone()))
                })
                .collect();

            let mut changed = false;
            'pairs: for i in 0..ctor_data.len() {
                for j in (i + 1)..ctor_data.len() {
                    let (ti, ci, ai) = (&ctor_data[i].0, &ctor_data[i].1, &ctor_data[i].2);
                    let (tj, cj, aj) = (&ctor_data[j].0, &ctor_data[j].1, &ctor_data[j].2);
                    if ci != cj || ai.len() != aj.len() {
                        continue;
                    }
                    // Already equal: nothing to do.
                    if self.find(*ti) == self.find(*tj) {
                        continue;
                    }
                    // Require every argument pair to be in the same class.
                    if !ai
                        .iter()
                        .zip(aj.iter())
                        .all(|(&x, &y)| self.find(x) == self.find(y))
                    {
                        continue;
                    }
                    // Collect the argument-equality reasons.
                    let (ti, tj) = (*ti, *tj);
                    let arg_pairs: Vec<(TermId, TermId)> =
                        ai.iter().copied().zip(aj.iter().copied()).collect();
                    let mut reasons: Vec<TermId> = Vec::new();
                    for (x, y) in arg_pairs {
                        if x != y {
                            reasons.extend(self.explain_equality(x, y));
                        }
                    }
                    reasons.sort_by_key(|t| t.0);
                    reasons.dedup();
                    self.union_with_reasons(ti, tj, reasons);
                    changed = true;
                    changed_any = true;
                    // Restart the scan: the union may enable further congruence.
                    break 'pairs;
                }
            }
            if !changed {
                break;
            }
        }
        changed_any
    }

    /// Downward selector-projection congruence (#dt-sel-projection).
    ///
    /// From a constructor equality `t = C(a_0, ..., a_{n-1})` (i.e. some member
    /// `t` of the class containing the constructor term `C(...)`), the datatype
    /// axiom `is-C(t) ⟹ sel_i(t) = a_i` lets us project: for every *existing*
    /// selector application `(sel_i t')` whose argument `t'` is in the same class
    /// as the constructor term, we may conclude `sel_i(t') = a_i`.
    ///
    /// We only union with selector applications that ALREADY exist in the term
    /// store (looked up via `find_app_named`, which never creates a term), exactly
    /// like the tester-edge handling in `occurs_check`. A selector application that
    /// does not appear in the formula cannot participate in any equality and so
    /// cannot affect (in)satisfiability — skipping it is complete.
    ///
    /// This is what lets `occurs_check` see cycles routed through nested
    /// constructors via their projections. Example (the motivating bug):
    /// `x = cons(cons(tl x))`. The class of `x` contains the constructor term
    /// `cons(cons(tl x))`; projecting selector `tl` onto the existing term
    /// `(tl x)` yields `tl(x) = cons(tl x)`, which closes the cycle
    /// `x ⊳ cons(...) ⊳ tl(x) = cons(tl x) ⊳ ...` and the occurs-check rejects it.
    ///
    /// Soundness: every union performed here is a logical consequence of an
    /// already-present constructor equality (`t = C(args)` is recorded in
    /// `term_constructors` and the union-find), so it can only constrain the
    /// model — it can never manufacture a spurious cycle.
    ///
    /// Returns `true` if any new merge was performed.
    pub(super) fn apply_selector_projection(&mut self) -> bool {
        if self.ctor_selectors.is_empty() {
            return false;
        }

        // Snapshot constructor terms (term_id, ctor_name, args), sorted for
        // determinism (#3060).
        self.buf_sorted_ctor_keys.clear();
        self.buf_sorted_ctor_keys
            .extend(self.term_constructors.keys().copied());
        self.buf_sorted_ctor_keys.sort_unstable_by_key(|t| t.0);

        let ctor_data: Vec<(TermId, String, Vec<TermId>)> = self
            .buf_sorted_ctor_keys
            .iter()
            .filter_map(|&t| {
                self.term_constructors
                    .get(&t)
                    .map(|info| (t, info.ctor_name.clone(), info.args.clone()))
            })
            .collect();

        // Build a deterministic class-rep -> members map over all known terms in
        // the union-find. Members are needed to find every `t'` in the
        // constructor term's class that might carry a selector application.
        let mut all_terms: Vec<TermId> = self.parent.keys().copied().collect();
        all_terms.sort_unstable_by_key(|t| t.0);
        let mut rep_to_members: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for t in all_terms {
            let rep = self.find(t);
            rep_to_members.entry(rep).or_default().push(t);
        }

        let mut changed_any = false;
        for (ctor_term, ctor_name, args) in ctor_data {
            let Some(sel_names) = self.ctor_selectors.get(&ctor_name).cloned() else {
                continue;
            };
            // Selector names are parallel to constructor fields/args.
            if sel_names.len() != args.len() {
                continue;
            }
            let rep = self.find(ctor_term);
            // Class members of the constructor term (include the rep itself).
            let mut members: Vec<TermId> = rep_to_members.get(&rep).cloned().unwrap_or_default();
            if !members.contains(&rep) {
                members.push(rep);
            }
            members.sort_unstable_by_key(|t| t.0);
            members.dedup();

            for (i, sel_name) in sel_names.iter().enumerate() {
                let arg_i = args[i];
                for &member in &members {
                    // Look up `(sel_name member)` WITHOUT creating it.
                    let Some(sel_app) = self.terms.find_app_named(sel_name, &[member]) else {
                        continue;
                    };
                    if self.find(sel_app) == self.find(arg_i) {
                        continue;
                    }
                    // Reason: the constructor equality `member = C(args)` (i.e.
                    // member = ctor_term). Every projected equality is implied by it.
                    let mut reasons = self.explain_equality(member, ctor_term);
                    reasons.sort_by_key(|t| t.0);
                    reasons.dedup();
                    self.union_with_reasons(sel_app, arg_i, reasons);
                    changed_any = true;
                }
            }
        }
        changed_any
    }

    /// Detect a clash between two distinct constant values in the same class
    /// (#dt-congruence).
    ///
    /// Injectivity (`C(a) = C(b) ⇒ a = b`) can force two argument terms to be
    /// merged. When those arguments are concrete, distinct constants — e.g.
    /// `x = c(0)` and `x = c(1)` force `0 = 1` — the equivalence class becomes
    /// inconsistent. The standalone QF_DT solver has no arithmetic partner to
    /// reject `0 = 1`, so the datatype theory must reject it directly: a class
    /// containing two syntactically distinct `Const` terms is unsatisfiable.
    ///
    /// Constants are hash-consed, so distinct constant values have distinct
    /// `TermId`s; any two such terms in one class are necessarily unequal.
    pub(super) fn check_constant_clash(&mut self) -> Option<Vec<TheoryLit>> {
        // Group all constant terms known to the union-find by class rep.
        self.buf_sorted_ctor_keys.clear();
        self.buf_sorted_ctor_keys
            .extend(self.parent.keys().copied());
        self.buf_sorted_ctor_keys.sort_unstable_by_key(|t| t.0);

        let num_terms = self.terms.len();
        let const_terms: Vec<TermId> = self
            .buf_sorted_ctor_keys
            .iter()
            .copied()
            // Guard against out-of-range ids (unit tests use synthetic TermIds
            // that are not interned in the store).
            .filter(|&t| t.index() < num_terms && matches!(self.terms.get(t), TermData::Const(_)))
            .collect();

        // Map class rep -> first constant term seen.
        let mut rep_to_const: HashMap<TermId, TermId> = HashMap::default();
        for t in const_terms {
            let rep = self.find(t);
            if let Some(&prev) = rep_to_const.get(&rep) {
                if prev != t {
                    // Two distinct constants in the same class: clash.
                    let reasons = self.explain_equality(prev, t);
                    let mut c: Vec<TheoryLit> = if reasons.is_empty() {
                        self.eq_lits_as_conflict()
                    } else {
                        reasons
                            .into_iter()
                            .map(|t| TheoryLit::new(t, true))
                            .collect()
                    };
                    c.sort_by_key(|l| (l.term.0, l.value));
                    c.dedup_by_key(|l| (l.term.0, l.value));
                    return Some(c);
                }
            } else {
                rep_to_const.insert(rep, t);
            }
        }

        None
    }

    /// Check for conflicts between tester results and constructors (#5082).
    ///
    /// Two cases:
    /// 1. `is-C(t) = false` but a term `C(...)` is in the same equivalence class as `t`.
    /// 2. `is-C(t) = true` but a term `C'(...)` (different constructor) is in t's class.
    pub(super) fn check_tester_conflicts(&mut self) -> Option<Vec<TheoryLit>> {
        // Collect tester entries to iterate over (avoids borrow conflict with &mut self).
        // This is proportional to tester_results.len(), not term_constructors.len().
        let tester_entries: Vec<(TermId, String, bool, TermId)> = self
            .tester_results
            .iter()
            .map(|(&arg, (ctor, val, lit))| (arg, ctor.clone(), *val, *lit))
            .collect();

        for (tester_arg, tester_ctor, tester_val, tester_lit) in &tester_entries {
            let tester_rep = self.find(*tester_arg);

            for (ctor_term, ctor_info) in &self.term_constructors {
                let ctor_rep = self.find(*ctor_term);
                if ctor_rep != tester_rep {
                    continue;
                }

                let same_ctor = &ctor_info.ctor_name == tester_ctor;
                if (*tester_val && !same_ctor) || (!*tester_val && same_ctor) {
                    let reasons = self.explain_equality(*tester_arg, *ctor_term);
                    let mut c: Vec<TheoryLit> = if reasons.is_empty() {
                        self.eq_lits_as_conflict()
                    } else {
                        reasons
                            .into_iter()
                            .map(|t| TheoryLit::new(t, true))
                            .collect()
                    };
                    c.push(TheoryLit::new(*tester_lit, *tester_val));
                    c.sort_by_key(|l| (l.term.0, l.value));
                    c.dedup_by_key(|l| (l.term.0, l.value));
                    return Some(c);
                }
            }
        }

        None
    }

    /// Check for conflicts between implied equalities and asserted disequalities.
    ///
    /// If `a` and `b` are in the same union-find class (via asserted equalities),
    /// then an asserted disequality `(not (= a b))` is inconsistent.
    pub(super) fn check_disequality_conflicts(&mut self) -> Option<Vec<TheoryLit>> {
        for idx in 0..self.asserted_diseqs.len() {
            let (lhs, rhs, diseq_lit) = self.asserted_diseqs[idx];
            if self.find(lhs) == self.find(rhs) {
                let reasons = self.explain_equality(lhs, rhs);
                let mut c: Vec<TheoryLit> = if reasons.is_empty() {
                    self.eq_lits_as_conflict()
                } else {
                    reasons
                        .into_iter()
                        .map(|t| TheoryLit::new(t, true))
                        .collect()
                };
                c.push(TheoryLit::new(diseq_lit, false));
                c.sort_by_key(|l| (l.term.0, l.value));
                c.dedup_by_key(|l| (l.term.0, l.value));
                return Some(c);
            }
        }

        None
    }

    fn occurs_check_conflict(&mut self, cycle_edges: &[(TermId, TermId)]) -> Vec<TheoryLit> {
        let mut reasons: Vec<TermId> = Vec::new();
        // Tester literals justifying any tester-induced edge traversed by the cycle.
        // These are asserted *true*, so they enter the conflict with polarity true.
        let mut tester_reasons: Vec<TermId> = Vec::new();
        for &(parent_rep, child_rep) in cycle_edges {
            // A tester-induced edge (`is-C(v) ⟹ v ⊳ sel_i(v)`) is justified by the
            // tester literal, plus whatever equalities relate the two endpoints.
            if let Some(&tester_lit) = self.buf_oc_tester_edges.get(&(parent_rep, child_rep)) {
                tester_reasons.push(tester_lit);
            }
            let edge_reasons = self.explain_equality(parent_rep, child_rep);
            reasons.extend(edge_reasons);
        }

        let mut conflict: Vec<TheoryLit> = if reasons.is_empty() && tester_reasons.is_empty() {
            self.eq_lits_as_conflict()
        } else {
            reasons
                .into_iter()
                .map(|t| TheoryLit::new(t, true))
                .collect()
        };
        // Tester literals are asserted true; include them with their true polarity.
        for lit in tester_reasons {
            conflict.push(TheoryLit::new(lit, true));
        }
        conflict.sort_by_key(|l| (l.term.0, l.value));
        conflict.dedup_by_key(|l| (l.term.0, l.value));
        conflict
    }

    /// Acyclicity check using persistent DFS buffers (#8599).
    ///
    /// Uses `buf_oc_color`, `buf_oc_parent_edge`, `buf_oc_rep_to_args`, `buf_oc_stack`
    /// to avoid per-call allocation of DFS state.
    pub(super) fn occurs_check(&mut self) -> Option<Vec<TheoryLit>> {
        // Build representative-to-args adjacency using persistent buffer.
        self.buf_oc_rep_to_args.clear();
        // Collect and sort constructor term keys for determinism (#3060).
        self.buf_sorted_ctor_keys.clear();
        self.buf_sorted_ctor_keys
            .extend(self.term_constructors.keys().copied());
        self.buf_sorted_ctor_keys.sort_unstable_by_key(|t| t.0);

        for &term_id in &self.buf_sorted_ctor_keys {
            let rep = self.find(term_id);
            if let Some(info) = self.term_constructors.get(&term_id) {
                self.buf_oc_rep_to_args
                    .entry(rep)
                    .or_default()
                    .extend(info.args.iter().copied());
            }
        }

        // Tester-induced edges (#dt-acyclic-tester).
        //
        // A true tester `is-C(v)` is semantically equivalent to
        // `v = C(sel_1(v), ..., sel_n(v))` for datatypes (SMT-LIB), even when no
        // explicit `C(...)` constructor term appears in the formula. For the
        // acyclicity check, that means rep(v) reaches each *existing* selector
        // application `(sel_i v)`. We add those edges here, using ONLY selector
        // terms already interned in the store (looked up via `find_app_named`,
        // which never creates a term). This lets occurs-check catch cycles like
        // `is-succ(v) ∧ (pred v) = v` (⇒ `v = succ(v)`, UNSAT) that are otherwise
        // invisible because there is no `succ(..)` constructor term.
        //
        // Soundness: every edge added here is implied by an asserted true tester,
        // so any cycle found is a genuine cycle in the asserted facts — the check
        // still only ever reports UNSAT for a real well-foundedness violation.
        self.buf_oc_tester_edges.clear();
        if !self.ctor_selectors.is_empty() {
            // Collect (arg, ctor_name, tester_lit) for asserted-true testers first to
            // release the borrow on self.tester_results before mutating buffers.
            let mut true_testers: Vec<(TermId, String, TermId)> = self
                .tester_results
                .iter()
                .filter(|(_, (_, val, _))| *val)
                .map(|(&arg, (ctor, _, lit))| (arg, ctor.clone(), *lit))
                .collect();
            // Deterministic order (#3060).
            true_testers.sort_unstable_by_key(|(arg, _, _)| arg.0);

            for (arg, ctor_name, tester_lit) in true_testers {
                let Some(sel_names) = self.ctor_selectors.get(&ctor_name).cloned() else {
                    continue;
                };
                let arg_rep = self.find(arg);
                for sel_name in &sel_names {
                    // Look up `(sel_name arg)` WITHOUT creating it. If it does not
                    // already exist, it cannot appear in any equality and therefore
                    // cannot close a cycle, so skipping it is complete.
                    let Some(sel_app) = self.terms.find_app_named(sel_name, &[arg]) else {
                        continue;
                    };
                    let sel_rep = self.find(sel_app);
                    self.buf_oc_rep_to_args
                        .entry(arg_rep)
                        .or_default()
                        .push(sel_app);
                    // Record the tester literal as the justification for this edge.
                    self.buf_oc_tester_edges
                        .entry((arg_rep, sel_rep))
                        .or_insert(tester_lit);
                }
            }
        }

        // DFS state using persistent buffers.
        // 0/unset = unvisited, 1 = on stack, 2 = fully explored (cycle-free).
        self.buf_oc_color.clear();
        self.buf_oc_parent_edge.clear();

        // Encode DFS operations: op=0 -> Enter(from), op=1 -> Exit
        // Stack entries: (op, node, from)
        self.buf_oc_stack.clear();

        self.buf_sorted_reps.clear();
        self.buf_sorted_reps
            .extend(self.buf_oc_rep_to_args.keys().copied());
        self.buf_sorted_reps.sort_unstable_by_key(|t| t.0);

        // Clone sorted_reps to avoid borrow conflict with self.
        let reps: Vec<TermId> = self.buf_sorted_reps.clone();

        for start in reps {
            let start = self.find(start);
            if matches!(self.buf_oc_color.get(&start), Some(2)) {
                continue;
            }

            self.buf_oc_stack.clear();
            // op=0 -> Enter, from=start
            self.buf_oc_stack.push((0, start, start));

            while let Some((op, node, from)) = self.buf_oc_stack.pop() {
                let node = self.find(node);
                if op == 1 {
                    // Exit
                    self.buf_oc_color.insert(node, 2);
                    continue;
                }
                // Enter
                match self.buf_oc_color.get(&node).copied() {
                    Some(2) => continue,
                    Some(1) => {
                        // Cycle detected! Reconstruct cycle edges.
                        let mut cycle_edges: Vec<(TermId, TermId)> = Vec::new();
                        cycle_edges.push((from, node));
                        let mut curr = from;
                        while curr != node {
                            if let Some(&(parent, child)) = self.buf_oc_parent_edge.get(&curr) {
                                cycle_edges.push((parent, child));
                                curr = parent;
                            } else {
                                break;
                            }
                        }
                        return Some(self.occurs_check_conflict(&cycle_edges));
                    }
                    _ => {}
                }

                self.buf_oc_color.insert(node, 1);
                // Push Exit marker
                self.buf_oc_stack.push((1, node, node));

                if let Some(args) = self.buf_oc_rep_to_args.get(&node) {
                    let args: Vec<TermId> = args.clone();
                    for arg in args {
                        let arg_rep = self.find(arg);
                        if !self.buf_oc_rep_to_args.contains_key(&arg_rep) {
                            continue;
                        }
                        match self.buf_oc_color.get(&arg_rep).copied() {
                            Some(2) => continue,
                            Some(1) => {
                                // Cycle: node -> arg_rep (which is on stack)
                                let mut cycle_edges: Vec<(TermId, TermId)> = Vec::new();
                                cycle_edges.push((node, arg_rep));
                                let mut curr = node;
                                while curr != arg_rep {
                                    if let Some(&(parent, child)) =
                                        self.buf_oc_parent_edge.get(&curr)
                                    {
                                        cycle_edges.push((parent, child));
                                        curr = parent;
                                    } else {
                                        break;
                                    }
                                }
                                return Some(self.occurs_check_conflict(&cycle_edges));
                            }
                            _ => {
                                self.buf_oc_parent_edge.insert(arg_rep, (node, arg_rep));
                                self.buf_oc_stack.push((0, arg_rep, node));
                            }
                        }
                    }
                }
            }
        }

        None
    }

    /// Check DT invariants (debug builds only).
    ///
    /// Extracted from check() to stay within the function-size limit.
    #[cfg(debug_assertions)]
    pub(super) fn debug_check_invariants(&self) {
        // Union-find representatives are fixpoints (sampled).
        debug_assert!(
            self.parent.keys().take(64).all(|&t| {
                let r = self.find(t);
                self.find(r) == r
            }),
            "BUG: DT union-find representative is not a fixpoint"
        );
        // asserted_eq_lits hasn't shrunk below the most recent scope snapshot.
        debug_assert!(
            self.scopes
                .last()
                .is_none_or(|s| self.asserted_eq_lits.len() >= s.asserted_eq_lits_len),
            "BUG: DT asserted_eq_lits ({}) < scope snapshot ({})",
            self.asserted_eq_lits.len(),
            self.scopes.last().map_or(0, |s| s.asserted_eq_lits_len),
        );
        // asserted_diseqs hasn't shrunk below the most recent scope snapshot.
        debug_assert!(
            self.scopes
                .last()
                .is_none_or(|s| self.asserted_diseqs.len() >= s.asserted_diseqs_len),
            "BUG: DT asserted_diseqs ({}) < scope snapshot ({})",
            self.asserted_diseqs.len(),
            self.scopes.last().map_or(0, |s| s.asserted_diseqs_len),
        );
    }
}
