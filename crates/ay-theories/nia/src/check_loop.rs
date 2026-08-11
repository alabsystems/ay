// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NIA check loop: LIA check -> sign -> patch -> tangent refinement.
//!
//! Ported from NRA's check_loop.rs, adapted for integer arithmetic
//! (LIA backend instead of LRA).

use ay_core::nonlinear;
use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::{TheoryLit, TheoryResult, TheorySolver};
use ay_lra::GomoryCut;
use num_rational::BigRational;
use num_traits::{One, Zero};

use std::collections::BTreeMap;

use super::NiaSolver;

/// Deterministic ceiling on the bit-size (numerator + denominator) of any
/// model value the refinement loop may derive further cuts from
/// (#nia-gomory-cap).
///
/// On divergent instances the model-point escalation roughly squares the
/// model values each round (bit-sizes DOUBLE per iteration), so `2^256`-scale
/// application constants (~256 bits) blow past any fixed cap within a handful
/// of rounds while remaining trivially cheap below it — and pathological
/// escalations reach the cap in ~12 rounds from small seeds. 4096 bits is
/// generous headroom over real workloads (degree-8 products of 2^256-scale
/// values are ~2048 bits) and keeps every under-cap BigRational gcd in the
/// microsecond range. Capping cut generation is completeness-only: cuts are
/// redundant-by-construction lemmas, so the guard can only produce a sound
/// Unknown, never a wrong verdict.
const MAX_REFINEMENT_MODEL_BITS: u64 = 4096;

impl NiaSolver<'_> {
    /// Last-resort SAT-only lane: clausal local search over the ORIGINAL
    /// assertion formulas (`#nia-clausal-sls`, see `local_search.rs`).
    ///
    /// Runs only where every box-shaped fallback has already declined —
    /// bounded enumeration, capped window search, model repair and factor split
    /// all need a finite box, and the dominant QF_NIA loss shape (VeryMax /
    /// AProVE termination VCs) has none. Local search cannot refute, so this
    /// can only turn `unknown` into an exactly-verified `sat`; it never returns
    /// `Unsat` and never bumps `conflict_count`.
    fn try_local_search_lane(&mut self) -> Option<TheoryResult> {
        let start = ay_core::time::Instant::now();
        let result = self.try_clausal_local_search();
        self.timings.enumeration += start.elapsed();
        debug_assert!(
            !matches!(result, Some(TheoryResult::Unsat(_))),
            "clausal local search must never refute"
        );
        if let Some(TheoryResult::Sat) = result {
            if self.debug {
                safe_eprintln!("[NIA] Clausal local search decided: Sat");
            }
            return result;
        }
        None
    }

    /// True when any model value the refinement escalation would derive cuts
    /// from (monomial factor/aux vars, division-purification vars) exceeds
    /// [`MAX_REFINEMENT_MODEL_BITS`] (#nia-gomory-cap). O(#vars) bit-length
    /// reads — no BigInt arithmetic.
    fn refinement_model_exceeds_cap(&self) -> bool {
        let over = |v: &BigRational| -> bool {
            v.numer().bits() + v.denom().bits() > MAX_REFINEMENT_MODEL_BITS
        };
        for mon in self.monomials.values() {
            if self.var_value(mon.aux_var).as_ref().is_some_and(over) {
                return true;
            }
            for &v in &mon.vars {
                if self.var_value(v).as_ref().is_some_and(over) {
                    return true;
                }
            }
        }
        for purif in &self.div_purifications {
            if self.var_value(purif.div_term).as_ref().is_some_and(over)
                || self.var_value(purif.denominator).as_ref().is_some_and(over)
            {
                return true;
            }
        }
        false
    }

    /// Monomial congruence lemmas (#nia-congruence): two registered monomials
    /// whose factor multisets are pairwise equal *under the currently asserted
    /// equalities* denote the same product, so their auxiliary (product)
    /// variables must be equal.
    ///
    /// ## Why this is needed
    ///
    /// Standalone NIA over-approximates every nonlinear product `x*y` as a
    /// fresh *opaque* integer variable (the monomial's aux var; see
    /// `NiaSolver::new`). Two syntactically distinct products — e.g. `l*r`
    /// (term A) and `l_view*r_view` (term B) — therefore get two *independent*
    /// opaque variables. If the problem also asserts `l = l_view` and
    /// `r = r_view`, the products are semantically identical, but the
    /// relaxation never links the two opaque vars: it can freely pick
    /// `aux_A = 0` and `aux_B = 5`, reporting a spurious model. This is exactly
    /// the shape of the `result == l*r => result@ == l@*r@` obligation, where
    /// `result@ == l*r` is asserted but the negated goal mentions the *other*
    /// product `l@*r@`.
    ///
    /// ## What it adds
    ///
    /// This routine asserts the **valid congruence equality** `aux_A = aux_B`
    /// into the inner LIA solver as a *shared equality* (`assert_shared_equality`
    /// — the same channel Nelson-Oppen uses), justified by the exact set of
    /// asserted equality literals that make the factor multisets coincide. Those
    /// literals are the equality's `reasons`, so the resulting conflict clause is
    /// sound and scoped: it only ever fires while those equalities are asserted.
    /// The shared-equality channel (not raw simplex bounds) is required so the
    /// equality is visible to LIA's `check_affine_disequality_implication`, which
    /// is what discharges the integer_ops *disequality* goal
    /// `NOT(l@*r@ = result_view)`.
    ///
    /// ## Soundness
    ///
    /// Function congruence `(a = c) ∧ (b = d) → a*b = c*d` is a *universally
    /// valid* theorem of the theory of `*` (it holds in every model). Adding it
    /// as a constraint can therefore NEVER remove a genuine model — it only
    /// removes "models" that already violate the function semantics of `*`,
    /// which the relaxation should never have admitted. Concretely: every model
    /// `M` of the true (non-relaxed) problem `O` satisfies `aux_A = a*b`,
    /// `aux_B = c*d`, `a = c`, `b = d`, hence `aux_A = aux_B`; so this lemma is
    /// satisfied by every model of `O`. It can therefore only ever turn a
    /// *spurious* relaxation Sat into Unsat — never a genuine Sat. It cannot let
    /// any invalid (sat) goal verify: a goal whose negation is genuinely SAT has
    /// a model satisfying all factor (in)equalities, and that model already
    /// satisfies every congruence equality this routine could add, so the
    /// relaxation remains SAT.
    ///
    /// The equality is only asserted when the matched factors are connected by
    /// *asserted* equalities (or are syntactically identical), so the `reasons`
    /// always justify the lemma. Returns the number of congruence equalities
    /// added (0 when nothing is congruent — the common case, so this is cheap).
    fn add_monomial_congruence_lemmas(&mut self) -> usize {
        // Need at least two monomials for any congruence to be possible.
        if self.monomials.len() < 2 {
            return 0;
        }

        // 1. Build a union-find over the *factor terms* using asserted
        //    equalities `lhs = rhs` (both arguments interned terms). Each union
        //    records the justifying equality literal so the congruence lemma's
        //    reasons are exactly the equalities used.
        let mut uf = EqUnionFind::default();
        for &(term, value) in &self.asserted {
            if !value {
                continue;
            }
            // Only positive `(= a b)` atoms contribute equalities. NOTE: NIA
            // already unwraps `Not(..)` in `assert_literal`, so a negated
            // disequality would arrive here as `(= a b)` with value=false and
            // is correctly skipped above.
            if let TermData::App(Symbol::Named(name), args) = self.terms.get(term) {
                if name == "=" && args.len() == 2 {
                    uf.union(args[0], args[1], TheoryLit { term, value });
                }
            }
        }

        // 2. Canonicalize every monomial's factor multiset by replacing each
        //    factor with its union-find representative, then sorting. Group the
        //    monomials by this canonical key.
        //
        //    `BTreeMap` keeps iteration deterministic (TermId order).
        let mut groups: BTreeMap<Vec<TermId>, Vec<TermId>> = BTreeMap::new();
        for mon in self.monomials_sorted() {
            let mut canon: Vec<TermId> = mon.vars.iter().map(|&v| uf.find(v)).collect();
            canon.sort_unstable_by_key(|t| t.0);
            groups.entry(canon).or_default().push(mon.aux_var);
        }

        // 3. For each group with >= 2 monomials, link all aux vars to the first
        //    one with an exact equality. The reasons are the equalities used to
        //    connect the two monomials' corresponding factors.
        let mut added = 0;
        for (_canon, aux_vars) in groups {
            if aux_vars.len() < 2 {
                continue;
            }
            // Snapshot the two monomials' original factor lists keyed by aux var
            // so we can compute the precise reason set per pair. We need the
            // factor lists; recover them from `aux_to_monomial`.
            let rep_aux = aux_vars[0];
            let Some(rep_factors) = self.aux_to_monomial.get(&rep_aux).cloned() else {
                continue;
            };
            for &other_aux in &aux_vars[1..] {
                if other_aux == rep_aux {
                    continue;
                }
                let Some(other_factors) = self.aux_to_monomial.get(&other_aux).cloned() else {
                    continue;
                };
                // Idempotency: skip pairs already linked in this scope so the
                // inner LIA's `shared_equalities` does not accumulate duplicates
                // across repeated `check()` calls.
                let pair = if rep_aux.0 <= other_aux.0 {
                    (rep_aux, other_aux)
                } else {
                    (other_aux, rep_aux)
                };
                if self.congruence_linked.contains(&pair) {
                    continue;
                }
                // Compute the reason literals: a sound, minimal-enough set of
                // asserted equalities that make the two factor multisets
                // coincide. If we cannot justify the match with reasons (should
                // not happen for a genuine canonical match), skip — fail open.
                let Some(reasons) = self.congruence_reasons(&rep_factors, &other_factors, &uf)
                else {
                    continue;
                };
                self.congruence_linked.insert(pair);
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Congruence lemma: aux {:?} = aux {:?} (reasons={:?})",
                        rep_aux,
                        other_aux,
                        reasons
                    );
                }
                self.add_equality_lemma(rep_aux, other_aux, &reasons);
                added += 1;
            }
        }
        added
    }

    /// Compute the asserted-equality literals justifying that the factor
    /// multisets `a` and `b` coincide (each `a` factor matched to a `b` factor
    /// that is either identical or in the same union-find class). Returns
    /// `None` if no such matching exists (defensive — the caller already
    /// grouped by canonical key, so a match should exist).
    fn congruence_reasons(
        &self,
        a: &[TermId],
        b: &[TermId],
        uf: &EqUnionFind,
    ) -> Option<Vec<(TermId, bool)>> {
        if a.len() != b.len() {
            return None;
        }
        let mut remaining: Vec<TermId> = b.to_vec();
        let mut reasons: Vec<(TermId, bool)> = Vec::new();
        for &af in a {
            // Find a not-yet-consumed `b` factor in the same class as `af`.
            let pos = remaining
                .iter()
                .position(|&bf| uf.find(bf) == uf.find(af))?;
            let bf = remaining.swap_remove(pos);
            if af != bf {
                // Justify `af = bf` by the union-find path literals.
                uf.path_reasons(af, bf, &mut reasons);
            }
        }
        // De-duplicate reasons (a literal may justify several factor pairs).
        reasons.sort_unstable_by_key(|&(t, v)| (t.0, v));
        reasons.dedup();
        Some(reasons)
    }

    /// Assert the exact integer equality `lhs = rhs` (the two congruent product
    /// aux vars) into the inner LIA solver, justified by `reasons` (the asserted
    /// equality literals that make the congruence valid).
    ///
    /// Registered as a *shared equality* (the same channel Nelson-Oppen uses for
    /// EUF→LIA equalities) rather than as raw simplex bounds. This is essential:
    /// LIA's `check_affine_disequality_implication` consults `shared_equalities`
    /// (and asserted `=` literals) to detect when a chain of equalities
    /// contradicts an asserted *disequality* (e.g. `aux_A = aux_B`,
    /// `aux_B = result_view`, `aux_A != result_view`). The integer_ops goal is
    /// exactly such a disequality (`NOT(l@*r@ = result_view)`), so the
    /// congruence must reach that check to discharge it. A raw simplex bound is
    /// invisible to the affine equality view and would not suffice.
    fn add_equality_lemma(&mut self, lhs: TermId, rhs: TermId, reasons: &[(TermId, bool)]) {
        let reason_lits: Vec<TheoryLit> = reasons
            .iter()
            .map(|&(term, value)| TheoryLit { term, value })
            .collect();
        self.lia.assert_shared_equality(lhs, rhs, &reason_lits);
    }

    /// Undo all tentative scopes (sign-cut + patch) if any are active.
    pub(crate) fn undo_tentative_patch(&mut self) {
        while self.tentative_depth > 0 {
            self.lia.pop();
            self.tentative_depth -= 1;
        }
    }

    /// Inject model-derived sign bounds for original variables into a tentative
    /// LIA scope. Based on Z3's `nla_basics_lemmas.cpp:sign_lemma()`.
    fn inject_tentative_sign_cuts(&mut self) -> usize {
        let zero = BigRational::zero();
        let mut added = 0;

        // Collect variables that appear in monomials but have no sign constraint
        let mut vars_needing_sign = Vec::new();
        for mon in self.monomials.values() {
            for &var in &mon.vars {
                if !self.var_sign_constraints.contains_key(&var)
                    && !vars_needing_sign.contains(&var)
                {
                    // Skip aux vars (monomial outputs)
                    if self.aux_to_monomial.contains_key(&var) {
                        continue;
                    }
                    vars_needing_sign.push(var);
                }
            }
        }

        for var_id in vars_needing_sign {
            let Some(val) = self.var_value(var_id) else {
                continue;
            };
            let is_lower = if val > zero {
                true
            } else if val < zero {
                false
            } else {
                continue; // val == 0: no cut needed
            };
            let lra_var = self.lia.lra_solver_mut().ensure_var_registered(var_id);
            self.lia.lra_solver_mut().add_gomory_cut(
                &GomoryCut {
                    coeffs: vec![(lra_var, BigRational::one())],
                    bound: zero.clone(),
                    is_lower,
                    reasons: Vec::new(),
                    source_term: None,
                },
                var_id,
            );
            added += 1;
        }
        added
    }

    /// Get the value of a term: tries LRA model first, then constant extraction.
    /// Handles rational and integer constants that may not have LRA variables (#6811).
    pub(crate) fn term_value(&self, term: TermId) -> Option<BigRational> {
        if let Some(val) = self.lia.lra_solver().get_value(term) {
            return Some(val);
        }
        match self.terms.get(term) {
            TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
            TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
            _ => None,
        }
    }

    /// Check if any tracked division has an inconsistent model value.
    /// Returns true if `model(denom) * model(div_term) != model(num)`.
    pub(crate) fn has_inconsistent_divisions(&self) -> bool {
        for purif in &self.div_purifications {
            let Some(denom_val) = self.var_value(purif.denominator) else {
                continue;
            };
            let Some(div_val) = self.var_value(purif.div_term) else {
                continue;
            };
            let Some(num_val) = self.term_value(purif.numerator) else {
                continue;
            };
            if &denom_val * &div_val != num_val {
                return true;
            }
        }
        false
    }

    /// Generate tangent-plane refinement lemmas for inconsistent divisions.
    ///
    /// For `(/ num denom)` with model values `d = model(denom)`, `k = model(div_term)`,
    /// the tangent plane of `f(denom, div_term) = denom * div_term` at `(d, k)` is:
    ///   `T = k * denom + d * div_term - d*k`
    ///
    /// We add the constraint `T [cmp] num_value` as a Gomory cut, where `cmp` is
    /// `>=` if the product is below `num` and `<=` if above.
    /// Ported from NRA (#8453, #6811).
    fn generate_division_refinement(&mut self) -> usize {
        let mut added = 0;

        // Iterate by index to avoid cloning self.div_purifications (#8599).
        for i in 0..self.div_purifications.len() {
            let purif = self.div_purifications[i];
            let Some(d) = self.var_value(purif.denominator) else {
                continue;
            };
            let Some(k) = self.var_value(purif.div_term) else {
                continue;
            };
            let Some(num_val) = self.term_value(purif.numerator) else {
                continue;
            };

            let product = &d * &k;
            if product == num_val {
                continue; // consistent
            }

            // Tangent plane: k*denom + d*div_term - d*k [cmp] num_val
            // Rearranged: k*denom + d*div_term [cmp] num_val + d*k
            let denom_var = self
                .lia
                .lra_solver_mut()
                .ensure_var_registered(purif.denominator);
            let div_var = self
                .lia
                .lra_solver_mut()
                .ensure_var_registered(purif.div_term);

            let coeffs = vec![(denom_var, k.clone()), (div_var, d.clone())];
            let bound = &num_val + &product;
            let is_lower = product < num_val;

            self.lia.lra_solver_mut().add_gomory_cut(
                &GomoryCut {
                    coeffs,
                    bound,
                    is_lower,
                    reasons: Vec::new(),
                    source_term: None,
                },
                purif.div_term,
            );
            added += 1;

            if self.debug {
                safe_eprintln!(
                    "[NIA] division refinement: denom={:?}, div={:?}, d={}, k={}, num={}",
                    purif.denominator,
                    purif.div_term,
                    d,
                    k,
                    num_val
                );
            }
        }
        added
    }

    /// Normalize the LIA check result for the NIA check loop.
    ///
    /// LIA's `check()` may return `NeedModelEquality` or `NeedModelEqualities`
    /// when it discovers that two terms have the same model value (Z3's
    /// `assume_eqs`). In the standalone LIA pipeline, the DPLL(T) layer
    /// handles these by creating equality atoms in the SAT solver.
    ///
    /// Inside the NIA check loop, however, these equality requests are
    /// irrelevant: the NIA solver manages the nonlinear relationship between
    /// variables and their monomials directly. Passing NeedModelEquality
    /// through to the outer DPLL(T) loop causes an infinite refinement cycle
    /// because LIA re-discovers the same model-value equalities on every
    /// re-entry. The linear constraints are satisfied (LIA found Sat before
    /// discovering the equalities), so treating these as Sat is sound.
    /// Ported from NRA (#8453).
    /// EXCEPTION (#nia-diseq-model-eq): when the LIA model *violates an
    /// asserted disequality* (some `not (= a b)` whose two sides evaluate to
    /// the same model value), the "linear Sat" is NOT genuine — standalone
    /// LIA relies on the DPLL(T) layer to split such disequalities, and
    /// nobody inside the NIA loop does. Swallowing the request then returns
    /// a Sat whose model fails validation, degrading a decidable query (e.g.
    /// `x*x + x == x*(x+1)` under a finite bound, negated) to `unknown`. In
    /// that confirmed-violation case we forward the request so the outer
    /// DPLL(T) layer can create the equality atom; asserting it either way
    /// makes progress (a `true` decision immediately conflicts with the
    /// asserted disequality and is retracted; `false` hands LIA the explicit
    /// disequality to split). The infinite-cycle concern above does not apply
    /// because each forwarded request is anchored to a *violated* asserted
    /// disequality: once the atom exists and is decided, LIA no longer
    /// produces a model with `a == b`, so the same request cannot recur.
    /// When either side has no model value we conservatively keep the
    /// historical suppression (fail-safe: same behavior as before).
    fn normalize_lia_result(&self, result: TheoryResult) -> TheoryResult {
        match &result {
            TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_) => {
                if self.model_violates_asserted_disequality() {
                    if self.debug {
                        safe_eprintln!(
                            "[NIA] Forwarding LIA NeedModelEquality -- model violates an \
                             asserted disequality (#nia-diseq-model-eq)"
                        );
                    }
                    return result;
                }
                // LIA found Sat but also wants model equalities. Inside NIA,
                // we only care about the linear Sat -- the nonlinear part is
                // checked by the monomial consistency loop.
                if self.debug {
                    safe_eprintln!("[NIA] Suppressing LIA NeedModelEquality -- treating as Sat");
                }
                TheoryResult::Sat
            }
            _ => result,
        }
    }

    /// True when some asserted disequality `not (= a b)` (integer sides) is
    /// violated by the current LIA model — both sides have known model values
    /// and they coincide. Sides without a model value (unregistered compound
    /// terms) are skipped, keeping the check conservative (see
    /// `normalize_lia_result`).
    ///
    /// Two evaluation strategies, both fail-closed:
    /// 1. Direct LRA model values of the two sides (the historical check —
    ///    covers plain variables and LRA-registered compound terms).
    /// 2. EXACT arithmetic evaluation of each side from the leaf variables'
    ///    integral model values (#nia-diseq-eval). Industrial QF_NIA (e.g.
    ///    AProVE termination VCs) asserts disequalities over POLYNOMIAL sides
    ///    like `not (= 0 (+ a1 (* a2 a3) (- a4)))`; the sum term has no LRA
    ///    variable, so strategy 1 skips it, the NeedModelEquality suppression
    ///    then returns a "Sat" whose model violates the disequality, and the
    ///    executor's model gate degrades the answer to `unknown`. Evaluating
    ///    the sides exactly (products computed for real, not via the opaque
    ///    aux relaxation) confirms the violation so the request is forwarded
    ///    and the DPLL(T) layer can split the disequality. Any leaf without an
    ///    integral model value keeps that atom skipped (conservative, same as
    ///    before).
    fn model_violates_asserted_disequality(&self) -> bool {
        for &(t, v) in &self.asserted {
            if v {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.terms.get(t) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            // Strategy 1: direct model values (historical behavior).
            if let (Some(a), Some(b)) = (self.var_value(args[0]), self.var_value(args[1])) {
                if a == b {
                    return true;
                }
                // Both sides have direct values and they differ: the
                // disequality is genuinely satisfied; no need to re-evaluate.
                continue;
            }
            // Strategy 2: exact evaluation from leaf-variable model values.
            if let Some(var_map) = self.integer_model_point_for(&[args[0], args[1]]) {
                if let (Some(a), Some(b)) = (
                    self.eval_term(args[0], &var_map),
                    self.eval_term(args[1], &var_map),
                ) {
                    if a == b {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Fingerprint of the refinement-relevant solver state
    /// (#nia-refine-stall): model values AND bounds of every monomial factor
    /// and aux variable, plus division-purification model values. The
    /// tangent / McCormick / secant / division refinement cuts are functions
    /// of exactly this state, so an unchanged fingerprint across iterations
    /// means the refinement is re-deriving identical (idempotent) cuts and
    /// can never converge. Deterministic within a process run (hashes
    /// `TermId` indices and exact rational numerator/denominator pairs in
    /// sorted term order).
    fn refinement_state_fingerprint(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        let mut seen: Vec<TermId> = Vec::new();
        for mon in self.monomials_sorted() {
            seen.push(mon.aux_var);
            seen.extend_from_slice(&mon.vars);
        }
        for purif in &self.div_purifications {
            seen.push(purif.div_term);
            seen.push(purif.numerator);
            seen.push(purif.denominator);
        }
        seen.sort_unstable_by_key(|t| t.0);
        seen.dedup();
        for term in seen {
            term.0.hash(&mut hasher);
            match self.var_value(term) {
                Some(v) => {
                    1u8.hash(&mut hasher);
                    v.numer().hash(&mut hasher);
                    v.denom().hash(&mut hasher);
                }
                None => 0u8.hash(&mut hasher),
            }
            match self.lia.lra_solver().get_bounds(term) {
                Some((lb, ub)) => {
                    for b in [lb, ub] {
                        match b {
                            Some(bound) => {
                                let v = bound.value.to_big();
                                1u8.hash(&mut hasher);
                                v.numer().hash(&mut hasher);
                                v.denom().hash(&mut hasher);
                                bound.strict.hash(&mut hasher);
                            }
                            None => 0u8.hash(&mut hasher),
                        }
                    }
                }
                None => 2u8.hash(&mut hasher),
            }
        }
        hasher.finish()
    }

    /// Run the NIA check loop: LIA check -> sign -> patch -> tangent.
    ///
    /// Following Z3's NLA check sequence adapted for integer arithmetic.
    ///
    /// Phase timings (#8823) are populated in `self.timings`: the overall
    /// loop wall-clock is tracked in `timings.check_loop`, and each inner
    /// phase (sign check, patching, tangent lemma generation, enumeration)
    /// is individually attributed. LIA time is recorded inside the LIA
    /// solver itself and surfaced via `self.lia.timings()`.
    pub(crate) fn nia_check_loop(&mut self) -> TheoryResult {
        let loop_start = ay_core::time::Instant::now();
        let result = self.nia_check_loop_inner();
        // Post-UNSAT attach: if some other NIA path proved UNSAT (so the SOS
        // decision pre-phase never ran or declined), try to attach a replayable
        // rational Positivstellensatz certificate to the conflict. This only
        // records a proof artifact; it never changes the verdict. The search
        // runs the independent checker on its own output, so any attached
        // certificate is already verified.
        if matches!(result, TheoryResult::Unsat(_)) && self.last_unsat_certificate.is_none() {
            self.last_unsat_certificate = self.try_build_unsat_sos_certificate();
        }
        self.timings.check_loop += loop_start.elapsed();
        result
    }

    /// Inner helper for `nia_check_loop` so the wall-clock timer in the
    /// wrapper always fires, even on early returns (#8823).
    fn nia_check_loop_inner(&mut self) -> TheoryResult {
        // In debug mode, unoptimized BigRational arithmetic and
        // debug_assert checks make each LIA call much slower.
        // 15 iterations is enough to validate convergence patterns
        // without blocking the test suite.
        #[cfg(debug_assertions)]
        const MAX_ITERATIONS: usize = 15;
        // Release: 500 iterations to handle hard nonlinear problems.
        // The caller's deadline/interrupt handles timeout; this cap only
        // fires on genuinely pathological cases.
        #[cfg(not(debug_assertions))]
        const MAX_ITERATIONS: usize = 500;

        // Exact univariate-integer decider (#nia-univariate-int). Fires only
        // when there is at least one nonlinear monomial (linear problems are
        // already complete in LIA) and EVERY asserted atom is a polynomial
        // comparison over a SINGLE shared integer variable. It decides such
        // problems exactly — even UNBOUNDED ones like `x*x = 16` that the
        // tangent/McCormick refinement and the (necessarily bounded) integer
        // enumeration leave at `unknown`. It is fail-closed: a SAT verdict
        // carries an integer witness re-verified by exact substitution into
        // every atom, an UNSAT verdict comes only from a COMPLETE candidate
        // cover, and anything out of fragment / uncertain returns `None` so we
        // fall through to the existing refinement loop unchanged.
        if !self.monomials.is_empty() {
            if let Some(result) = self.try_univariate_integer() {
                if matches!(result, TheoryResult::Unsat(_)) {
                    self.conflict_count += 1;
                }
                if self.debug {
                    safe_eprintln!("[NIA] univariate-int decider: {result:?}");
                }
                return result;
            }
        }

        // Exact rational SOS / Positivstellensatz UNSAT decision pre-phase (W3,
        // #nia-sos). Discharges coupled-multivariate NIA infeasibilities —
        // cross-term / quadratic-form refutations like `(x−y)²<0`, `x²+y²<2xy`,
        // overflow/box-product bounds — that the incremental-linearization loop
        // below would otherwise leave at `Unknown`. Certificate-gated and
        // sound-for-UNSAT ONLY: it returns exactly `Unsat` (with an
        // independently re-checkable Positivstellensatz certificate, or on a
        // syntactically-false atom) or falls through. It NEVER emits `Sat` and
        // NEVER turns a satisfiable system into `Unsat` (see sos_check.rs).
        if let Some(result) = self.try_sos_positivstellensatz_unsat() {
            self.conflict_count += 1;
            if self.debug {
                safe_eprintln!("[NIA] SOS Positivstellensatz pre-phase: {result:?}");
            }
            return result;
        }

        // Track whether tangent hyperplane approximations were used.
        // Tangent planes are model-point linearizations that may exclude valid
        // solutions. When tangent planes were used and LIA becomes UNSAT,
        // the UNSAT is unreliable. McCormick envelopes, even-power
        // non-negativity, and sign cuts do NOT set this flag.
        let mut used_tangent_approximation = false;

        // Refinement livelock detection (#nia-refine-stall): the tangent /
        // McCormick / division refinement derives its cuts purely from the
        // current LIA model point and variable bounds. When that state is
        // IDENTICAL across consecutive iterations, the emitted cuts are
        // identical too (idempotent re-adds), so the loop can never make
        // further progress — on AProVE-style flag instances it re-adds the
        // same envelope for hundreds of iterations until MAX_ITERATIONS,
        // burning the whole time budget before the decision procedures
        // (bounded enumeration / factor split) below ever run. Three
        // consecutive identical fingerprints declare a stall, which routes
        // into the SAME fallback block as `added == 0` (sound: it only
        // reorders when the fallbacks run).
        let mut stall_fingerprint: Option<u64> = None;
        let mut stall_repeats: usize = 0;

        // Monomial congruence (#nia-congruence): link the opaque product vars
        // of monomials whose factor multisets are equal under the asserted
        // equalities (e.g. `l*r` and `l_view*r_view` when `l=l_view`,
        // `r=r_view`). These are exact, universally-valid congruence equalities
        // justified by the asserting equality literals — NOT tangent
        // approximations — so a subsequent LIA UNSAT they cause is genuine and
        // does NOT set `used_tangent_approximation`. Added before the loop so
        // the first `lia.check()` already sees them.
        let _congruence_added = self.add_monomial_congruence_lemmas();

        // Zero-lower-bound product sign / monotonicity lemmas
        // (#nia-zero-bound, see zero_bound_lemmas.rs): exact ordered-ring
        // theorems derived ONLY from asserted literals (`x>=0 && y>=0 ->
        // x*y>=0`; `x<=y && z>=0 -> x*z<=y*z`), asserted as reason-carrying
        // cuts. Like the congruence lemmas — and unlike tangent planes —
        // these are NOT approximations, so they do not set
        // `used_tangent_approximation`, and an UNSAT they cause is genuine
        // (the iteration-0 conflict stays sound because each cut's reasons
        // are the exact justifying literals). Added before the loop so the
        // first `lia.check()` already sees them.
        let _zero_bound_added = self.add_zero_bound_product_lemmas();

        for iteration in 0..=MAX_ITERATIONS {
            // Fail-closed memory guard (#nia-oom): each iteration asserts
            // tangent/McCormick/division-refinement lemmas into the persistent
            // LIA/LRA tableau, and that state is carried across branch-and-bound
            // splits, so a pathological nonlinear query can grow the tableau
            // without bound. QF_NIA ⊇ Hilbert's 10th, so unbounded growth here
            // is undecidable to rule out a-priori — we cannot promise the loop
            // terminates, but we MUST degrade gracefully rather than OOM the
            // machine. Poll the process memory ceiling (set from --memory or the
            // auto-detected half-RAM default in main) and return Unknown before
            // emitting the next round of lemmas, converting a 203 GB
            // machine-kill into a graceful Unknown(resource-out) at the budget.
            if ay_sys::process_memory_exceeded() {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] process memory ceiling exceeded at iteration {iteration} \
                         — returning Unknown(resource-out) instead of growing the tableau"
                    );
                }
                return TheoryResult::Unknown;
            }
            // Deadline re-poll (#nia-deadline, mirror of #lia-deadline-forward):
            // the caller's deadline is only polled BETWEEN theory checks, so
            // without this a single dense refinement escalation would overshoot
            // the wall budget without bound. Checked at every iteration
            // boundary; the embedded `lia.check()` polls the same forwarded
            // deadline at its own cascade checkpoints. Verdict-neutral:
            // no verdict has been computed for this iteration yet, and
            // Unknown is always sound.
            if self.should_timeout() {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] wall-clock deadline exceeded at iteration {iteration} \
                         — returning Unknown instead of refining further"
                    );
                }
                return TheoryResult::Unknown;
            }
            let lia_result = self.lia.check();
            let lia_result = self.normalize_lia_result(lia_result);

            if self.debug {
                safe_eprintln!(
                    "[NIA] Iteration {}: LIA check result: {:?}",
                    iteration,
                    lia_result
                );
            }

            // Escalation size cap (#nia-gomory-cap): the model-point refinement
            // below (tangent/McCormick/Gomory patch cuts) derives cut
            // coefficients and bounds from the CURRENT model values, and on
            // divergent instances (e.g. the ∀∃ guard `sk*sk >= c` family) each
            // round roughly SQUARES the model point — bit-sizes double every
            // iteration, single BigUint gcds inside BigRational normalization
            // come to dominate wall time, and the loop becomes a deterministic
            // nontermination that no iteration cap catches (each iteration's
            // cost explodes, not their count). Refuse to derive further cuts
            // from an oversized model point: return Unknown (give up on this
            // lemma family) exactly like the other bounded NIA machinery.
            //
            // COMPLETENESS-ONLY by construction: cuts are redundant-by-
            // construction lemmas, so emitting fewer of them can only turn a
            // would-be verdict into a sound Unknown, never into a wrong
            // verdict. A genuine LIA UNSAT is never masked — the guard is
            // gated on the non-UNSAT variants and an UNSAT verdict returns
            // through the match below untouched. TERMINATION: every cut is
            // derived from a model point that passed this cap, so cut
            // coefficients/bounds stay poly(cap)-bit; one further escalation
            // step past the cap trips the guard, and re-entrant checks exit
            // here after a single bounded `lia.check()`.
            if !matches!(
                &lia_result,
                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
            ) && self.refinement_model_exceeds_cap()
            {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] refinement model values exceed {MAX_REFINEMENT_MODEL_BITS} bits \
                         at iteration {iteration} — returning Unknown instead of escalating \
                         (#nia-gomory-cap)"
                    );
                }
                return TheoryResult::Unknown;
            }

            // #nia-zero-bound family 4 (box product upper cuts) reads factor
            // bounds from the LRA bound store, which is only populated once
            // `lia.check()` has processed the asserted atoms — the pre-loop
            // emission sees an empty store on a freshly (re)created solver.
            // (Re)derive after the check; when a new cut was added, re-run the
            // check so the verdict (including a NeedSplit that would otherwise
            // be forwarded up for a hopeless value-by-value branch crawl)
            // reflects it. Terminates: each (aux, bound) cut is deduped per
            // scope, so this fires at most once per monomial per bound value.
            if !matches!(
                &lia_result,
                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
            ) && self.add_box_product_upper_lemmas() > 0
            {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Iteration {iteration}: re-checking after box product cuts"
                    );
                }
                continue;
            }

            match &lia_result {
                TheoryResult::Sat | TheoryResult::Unknown => {
                    // Propagate monomial signs before checking consistency.
                    // This derives product signs from factor signs (e.g., if x > 0
                    // and y > 0, then x*y > 0). Ported from NRA (#8453).
                    nonlinear::propagate_monomial_signs(
                        &self.monomials,
                        &mut self.var_sign_constraints,
                    );

                    // Check sign consistency first (definitive conflicts)
                    let sign_start = ay_core::time::Instant::now();
                    let sign_conflict = self.check_sign_consistency();
                    self.timings.sign_check += sign_start.elapsed();
                    if let Some(conflict) = sign_conflict {
                        if self.debug {
                            safe_eprintln!("[NIA] Sign inconsistency detected");
                        }
                        self.conflict_count += 1;
                        return TheoryResult::Unsat(conflict);
                    }

                    // Check monomial value consistency and division consistency
                    let sign_start = ay_core::time::Instant::now();
                    let monomial_ok = !self.has_inconsistent_monomials();
                    let division_ok = !self.has_inconsistent_divisions();
                    self.timings.sign_check += sign_start.elapsed();
                    if self.debug {
                        safe_eprintln!(
                            "[NIA] consistency: monomial_ok={monomial_ok} division_ok={division_ok} has_scaled={}",
                            self.has_scaled_product_vars()
                        );
                    }
                    if monomial_ok && division_ok {
                        // #nia-const-factor: SCALED products `(* c x y)` are not
                        // registered as monomials (the monomial invariant requires
                        // `aux == product(vars)`), so neither the linearization nor
                        // `has_inconsistent_monomials` constrains the opaque `*`
                        // term to its true value. A bare LIA Sat would therefore be
                        // a SPURIOUS model (the opaque term can take any value). Run
                        // exact bounded enumeration whenever monomials OR scaled
                        // products are present; only fall back to LIA's verdict when
                        // there is genuinely nothing nonlinear left unaccounted for.
                        let has_scaled = self.has_scaled_product_vars();
                        if matches!(lia_result, TheoryResult::Unknown) {
                            if !self.monomials.is_empty() || has_scaled {
                                // Exact single-point verification first
                                // (#nia-model-point): the current model point is
                                // often already a genuine witness, and checking
                                // it is one exact formula evaluation — far
                                // cheaper than enumerating a box.
                                if let Some(result) = self.try_model_point_sat() {
                                    return result;
                                }
                                let enum_start = ay_core::time::Instant::now();
                                let enum_result = self.try_bounded_enumeration();
                                self.timings.enumeration += enum_start.elapsed();
                                if let Some(result) = enum_result {
                                    if self.debug {
                                        safe_eprintln!(
                                            "[NIA] Bounded enumeration after LIA Unknown: {:?}",
                                            result
                                        );
                                    }
                                    if matches!(result, TheoryResult::Unsat(_)) {
                                        self.conflict_count += 1;
                                    }
                                    return result;
                                }
                                // SAT-only capped fallback (#nia-capped-search):
                                // upgrades unknown -> checked sat where the
                                // exhaustive box is incomplete; never emits unsat.
                                let enum_start = ay_core::time::Instant::now();
                                let capped = self.try_capped_model_search();
                                self.timings.enumeration += enum_start.elapsed();
                                if let Some(result) = capped {
                                    if self.debug {
                                        safe_eprintln!(
                                            "[NIA] Capped model search after LIA Unknown: {:?}",
                                            result
                                        );
                                    }
                                    return result;
                                }
                                // SAT-only model-anchored repair (#nia-repair-search).
                                let enum_start = ay_core::time::Instant::now();
                                let repaired = self.try_model_repair_search();
                                self.timings.enumeration += enum_start.elapsed();
                                if let Some(result) = repaired {
                                    return result;
                                }
                                // Bounded factor case-split (#nia-factor-split):
                                // exact SAT/UNSAT via per-value linearization of
                                // small asserted-box factors.
                                let enum_start = ay_core::time::Instant::now();
                                let split = self.try_bounded_factor_split();
                                self.timings.enumeration += enum_start.elapsed();
                                if let Some(result) = split {
                                    if matches!(result, TheoryResult::Unsat(_)) {
                                        self.conflict_count += 1;
                                    }
                                    return result;
                                }
                                if let Some(result) = self.try_local_search_lane() {
                                    return result;
                                }
                            }
                            return TheoryResult::Unknown;
                        }
                        // LIA Sat. If a scaled product is present, LIA's model does
                        // not pin the opaque `*` term, so do NOT trust the bare Sat:
                        // verify the model point exactly (#nia-model-point), then
                        // try exact enumeration (its var set includes the scaled
                        // factors); if neither can decide, fall back to the
                        // SAT-only searches, else degrade to Unknown (sound —
                        // never reports an unvalidated Sat that the model checker
                        // would reject).
                        if has_scaled {
                            if let Some(result) = self.try_model_point_sat() {
                                return result;
                            }
                            let enum_start = ay_core::time::Instant::now();
                            let enum_result = self.try_bounded_enumeration();
                            self.timings.enumeration += enum_start.elapsed();
                            if let Some(result) = enum_result {
                                if matches!(result, TheoryResult::Unsat(_)) {
                                    self.conflict_count += 1;
                                }
                                return result;
                            }
                            // SAT-only fallbacks (never Unsat; see above).
                            let enum_start = ay_core::time::Instant::now();
                            let fallback = self
                                .try_capped_model_search()
                                .or_else(|| self.try_model_repair_search());
                            self.timings.enumeration += enum_start.elapsed();
                            if let Some(result) = fallback {
                                return result;
                            }
                            if let Some(result) = self.try_local_search_lane() {
                                return result;
                            }
                            return TheoryResult::Unknown;
                        }
                        return TheoryResult::Sat;
                    }

                    // Livelock check (#nia-refine-stall): fingerprint the
                    // refinement-relevant state (monomial factor/aux model
                    // values and bounds, division-purification values) BEFORE
                    // patching mutates the model. Identical state on three
                    // consecutive iterations means the model-point-derived
                    // refinement below is re-deriving the same cuts forever.
                    let fp = self.refinement_state_fingerprint();
                    if stall_fingerprint == Some(fp) {
                        stall_repeats += 1;
                    } else {
                        stall_fingerprint = Some(fp);
                        stall_repeats = 0;
                    }
                    let refinement_stalled = stall_repeats >= 2;
                    if refinement_stalled && self.debug {
                        safe_eprintln!(
                            "[NIA] Iteration {iteration}: refinement state unchanged for \
                             {stall_repeats} iterations — treating as stalled (#nia-refine-stall)"
                        );
                    }

                    // Try bounded enumeration early: if all monomial variables
                    // have finite integer bounds (directly from LRA or inferred
                    // from monomial constraints), we can decide satisfiability
                    // by exhaustive search without waiting for tangent planes
                    // to stall (#7978). This is especially important for problems
                    // where LIA returns NeedSplit before tangent planes iterate
                    // enough to trigger the stall-point enumeration.
                    if iteration == 0 {
                        let enum_start = ay_core::time::Instant::now();
                        let enum_result = self.try_bounded_enumeration();
                        self.timings.enumeration += enum_start.elapsed();
                        if let Some(result) = enum_result {
                            if self.debug {
                                safe_eprintln!(
                                    "[NIA] Early bounded enumeration decided: {:?}",
                                    result
                                );
                            }
                            if matches!(result, TheoryResult::Unsat(_)) {
                                self.conflict_count += 1;
                            }
                            return result;
                        }
                    }

                    // Tentative sign cuts for variables with unknown sign
                    if self.tentative_depth == 0 {
                        self.lia.push();
                        self.tentative_depth += 1;
                    }
                    let sign_cuts = self.inject_tentative_sign_cuts();
                    self.sign_cut_count += sign_cuts as u64;

                    // Integer rounding: try to round fractional model values
                    // to nearby integers before full patching. This is cheaper
                    // than a full tentative patch and handles the common case
                    // where simplex finds a rational relaxation that is close
                    // to an integer solution. (#8453)
                    let patch_start = ay_core::time::Instant::now();
                    let rounded = self.try_integer_rounding();
                    self.timings.patching += patch_start.elapsed();
                    if rounded {
                        self.patch_count += 1;
                        if !self.has_inconsistent_monomials() && !self.has_inconsistent_divisions()
                        {
                            // #nia-scaled-patch-verify: SCALED products
                            // `(* c x y)` are invisible to monomial
                            // consistency (not registered as monomials), so a
                            // patched model can still assign the opaque `*`
                            // term an arbitrary value. When the exact
                            // evaluator PROVES the current point violates an
                            // asserted atom, suppress the (certainly
                            // spurious) Sat and keep refining — previously
                            // this returned a Sat that the model gate would
                            // demote to unknown, forfeiting the decision
                            // procedures below. Inconclusive verification
                            // (opaque atom) keeps today's behavior.
                            if !self.has_scaled_product_vars()
                                || self.current_model_point_status() != Some(false)
                            {
                                return TheoryResult::Sat;
                            }
                        }
                    }

                    // Model patching (Z3 nla_core.cpp:patch_monomials)
                    let patch_start = ay_core::time::Instant::now();
                    let patched = self.try_tentative_patch();
                    self.timings.patching += patch_start.elapsed();
                    if patched {
                        self.patch_count += 1;
                        if !self.has_inconsistent_monomials() && !self.has_inconsistent_divisions()
                        {
                            // #nia-scaled-patch-verify: see the `rounded`
                            // branch above — suppress only PROVABLY spurious
                            // Sat verdicts when scaled products are present.
                            if !self.has_scaled_product_vars()
                                || self.current_model_point_status() != Some(false)
                            {
                                return TheoryResult::Sat;
                            }
                        }
                    }

                    // Tangent plane refinement (includes McCormick pairwise
                    // and secant cuts for higher-degree monomials #8453)
                    let tangent_start = ay_core::time::Instant::now();
                    let (mut added, used_tangent) =
                        self.add_tangent_constraints_for_incorrect_monomials();
                    self.tangent_lemma_count += added as u64;
                    if used_tangent {
                        used_tangent_approximation = true;
                    }
                    // Division refinement: tangent planes for denom * div = num (#6811, #8453).
                    // These are model-point approximations (same class as tangent planes).
                    let div_added = self.generate_division_refinement();
                    self.timings.tangent += tangent_start.elapsed();
                    if div_added > 0 {
                        added += div_added;
                        used_tangent_approximation = true;
                    }

                    if self.debug {
                        safe_eprintln!(
                            "[NIA] Added {} tangent plane constraints ({} division), re-checking",
                            added,
                            div_added
                        );
                    }

                    // Enhanced refinement: pairwise McCormick and secant cuts
                    // provide additional constraints beyond basic tangent planes,
                    // especially useful for higher-degree monomials. (#8453)
                    let tangent_start = ay_core::time::Instant::now();
                    let enhanced = self.apply_enhanced_refinement();
                    self.timings.tangent += tangent_start.elapsed();
                    added += enhanced;

                    if added == 0 || refinement_stalled || iteration == MAX_ITERATIONS {
                        // Tangent planes stalled -- try bounded enumeration
                        // before giving up. If all monomial variables have finite
                        // integer bounds and the domain is small, we can decide
                        // satisfiability by exhaustive search.
                        let enum_start = ay_core::time::Instant::now();
                        let enum_result = self.try_bounded_enumeration();
                        self.timings.enumeration += enum_start.elapsed();
                        if let Some(result) = enum_result {
                            if self.debug {
                                safe_eprintln!("[NIA] Bounded enumeration decided: {:?}", result);
                            }
                            if matches!(result, TheoryResult::Unsat(_)) {
                                self.conflict_count += 1;
                            }
                            return result;
                        }
                        // Exhaustive enumeration could not build a complete sound
                        // box (e.g. a variable is unbounded in one direction).
                        // Fall back to the SAT-only searches: the capped window
                        // search (#nia-capped-search), then the model-anchored
                        // repair search (#nia-repair-search) which pins the
                        // consistent variables at their model values and fixes up
                        // only the suspects. Both can only ever upgrade this
                        // `unknown` to a checked `sat` (validated witness) and
                        // never emit `unsat`, so they are a pure completeness
                        // gain with no soundness risk.
                        let enum_start = ay_core::time::Instant::now();
                        let capped = self
                            .try_capped_model_search()
                            .or_else(|| self.try_model_repair_search());
                        self.timings.enumeration += enum_start.elapsed();
                        if let Some(result) = capped {
                            if self.debug {
                                safe_eprintln!(
                                    "[NIA] SAT-only fallback search decided: {:?}",
                                    result
                                );
                            }
                            return result;
                        }
                        // Bounded factor case-split (#nia-factor-split): exact
                        // SAT/UNSAT via per-value linearization of small
                        // asserted-box factors.
                        let enum_start = ay_core::time::Instant::now();
                        let split = self.try_bounded_factor_split();
                        self.timings.enumeration += enum_start.elapsed();
                        if let Some(result) = split {
                            if matches!(result, TheoryResult::Unsat(_)) {
                                self.conflict_count += 1;
                            }
                            if self.debug {
                                safe_eprintln!("[NIA] Factor split decided: {:?}", result);
                            }
                            return result;
                        }
                        if let Some(result) = self.try_local_search_lane() {
                            return result;
                        }
                        return TheoryResult::Unknown;
                    }

                    continue;
                }
                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                    self.conflict_count += 1;
                    if iteration == 0 {
                        // First iteration: no tangent planes, LIA conflict is genuine.
                        // Move instead of clone since we're returning (#8599).
                        return lia_result;
                    }
                    if used_tangent_approximation {
                        // Tangent planes may have over-constrained. Recheck with
                        // only exact lemmas (McCormick, even-power, sign cuts,
                        // and division refinement at fresh model point).
                        self.undo_tentative_patch();
                        self.lia.push();
                        self.tentative_depth += 1;
                        self.inject_tentative_sign_cuts();
                        // Use mem::take to avoid cloning all Monomial values (#8599).
                        // Temporarily steal the map; restored after the recheck loop.
                        let mons = std::mem::take(&mut self.monomials);
                        for mon in mons.values() {
                            self.add_even_power_nonneg(mon);
                            self.add_mccormick_constraints(mon);
                        }
                        // Re-add division refinement at fresh model point (#6811, #8453)
                        self.generate_division_refinement();
                        let mut recheck_proved = false;
                        // Multi-pass: McCormick on nested monomials may need
                        // LIA to propagate inner bounds before outer McCormick
                        // becomes effective (e.g., a*(b*c) needs bounds on b*c).
                        for _ in 0..3 {
                            let recheck = self.lia.check();
                            let recheck = self.normalize_lia_result(recheck);
                            match &recheck {
                                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                                    recheck_proved = true;
                                    break;
                                }
                                _ => {
                                    // Re-add McCormick and division refinement
                                    // with potentially updated bounds/model
                                    let mut added_any = false;
                                    for mon in mons.values() {
                                        if self.add_mccormick_constraints(mon) > 0 {
                                            added_any = true;
                                        }
                                    }
                                    if self.generate_division_refinement() > 0 {
                                        added_any = true;
                                    }
                                    if !added_any {
                                        break;
                                    }
                                }
                            }
                        }
                        self.monomials = mons;
                        self.undo_tentative_patch();
                        if recheck_proved {
                            let conflict: Vec<TheoryLit> = self
                                .asserted
                                .iter()
                                .map(|&(t, v)| TheoryLit { term: t, value: v })
                                .collect();
                            return TheoryResult::Unsat(conflict);
                        }
                        // Try bounded enumeration before giving up -- it can decide
                        // the original nonlinear problem independently of tangent planes.
                        let enum_start = ay_core::time::Instant::now();
                        let enum_result = self.try_bounded_enumeration();
                        self.timings.enumeration += enum_start.elapsed();
                        if let Some(result) = enum_result {
                            if self.debug {
                                safe_eprintln!(
                                    "[NIA] Bounded enumeration after tangent-UNSAT: {:?}",
                                    result
                                );
                            }
                            if matches!(result, TheoryResult::Unsat(_)) {
                                self.conflict_count += 1;
                            }
                            return result;
                        }
                        // SAT-only fallbacks (#nia-capped-search,
                        // #nia-repair-search): never emit unsat, only upgrade
                        // unknown -> checked sat.
                        let enum_start = ay_core::time::Instant::now();
                        let capped = self
                            .try_capped_model_search()
                            .or_else(|| self.try_model_repair_search());
                        self.timings.enumeration += enum_start.elapsed();
                        if let Some(result) = capped {
                            if self.debug {
                                safe_eprintln!(
                                    "[NIA] SAT-only fallback search after tangent-UNSAT: {:?}",
                                    result
                                );
                            }
                            return result;
                        }
                        // Bounded factor case-split (#nia-factor-split). Runs
                        // on the ORIGINAL constraints in fresh scopes (its
                        // cover comes from asserted atoms and its branches
                        // start from `lia.push()`), so it is independent of
                        // the tangent approximations that made the UNSAT above
                        // unreliable.
                        let enum_start = ay_core::time::Instant::now();
                        let split = self.try_bounded_factor_split();
                        self.timings.enumeration += enum_start.elapsed();
                        if let Some(result) = split {
                            if matches!(result, TheoryResult::Unsat(_)) {
                                self.conflict_count += 1;
                            }
                            if self.debug {
                                safe_eprintln!(
                                    "[NIA] Factor split after tangent-UNSAT: {:?}",
                                    result
                                );
                            }
                            return result;
                        }
                        if let Some(result) = self.try_local_search_lane() {
                            return result;
                        }
                        return TheoryResult::Unknown;
                    }
                    // Only exact lemmas were used. UNSAT is genuine.
                    let conflict: Vec<TheoryLit> = self
                        .asserted
                        .iter()
                        .map(|&(t, v)| TheoryLit { term: t, value: v })
                        .collect();
                    return TheoryResult::Unsat(conflict);
                }
                other => {
                    // Cover-closed fast path (#nia-factor-split-fastpath):
                    // disequality-class requests (disequality / expression
                    // splits, model-equality forwarding) are handled by the
                    // OUTER DPLL(T) loop one branch at a time — on flag-boxed
                    // industrial instances (AProVE / T2 termination VCs) that
                    // round-trip repeats for thousands of iterations without
                    // converging, while the bounded factor split can decide
                    // the query outright from its complete asserted-box cover
                    // (branch disequalities are handled in-branch by the
                    // integer entailment probes, #nia-factor-split-diseq).
                    // Try the exact split BEFORE forwarding; fall through to
                    // the unchanged forwarding when it cannot decide.
                    // `NeedSplit` (branch-and-bound integer splits — genuine
                    // progress) and lemma requests are NOT intercepted.
                    if matches!(
                        other,
                        TheoryResult::NeedDisequalitySplit(_)
                            | TheoryResult::NeedExpressionSplit(_)
                            | TheoryResult::NeedExpressionSplits(_)
                            | TheoryResult::NeedModelEquality(_)
                            | TheoryResult::NeedModelEqualities(_)
                    ) && !self.monomials.is_empty()
                    {
                        let enum_start = ay_core::time::Instant::now();
                        let split = self.try_bounded_factor_split();
                        self.timings.enumeration += enum_start.elapsed();
                        if let Some(result) = split {
                            if matches!(result, TheoryResult::Unsat(_)) {
                                self.conflict_count += 1;
                            }
                            if self.debug {
                                safe_eprintln!(
                                    "[NIA] Factor split decided before forwarding \
                                     {other:?}-class request: {result:?}"
                                );
                            }
                            return result;
                        }
                    }

                    // SAT-only capped model search before forwarding a genuine
                    // `NeedSplit` (#nia-capped-search-needsplit). On unbounded
                    // satisfiable queries (e.g. `x*x = k*y ∧ x > c`) the LIA
                    // relaxation returns `NeedSplit` for a fractional variable
                    // and the executor's branch-and-bound eventually exhausts
                    // its split budget at a sound `unknown` — the stall-path
                    // capped search inside this loop is never reached. Attempt
                    // it here: it enumerates a bounded window and returns `Sat`
                    // ONLY for a point that `check_assignment` verifies against
                    // every asserted atom by exact integer arithmetic. It can
                    // NEVER emit `Unsat` (the window is artificial), so this is
                    // a pure completeness upgrade of `unknown -> checked sat`
                    // with zero soundness risk; the executor's independent
                    // model gate re-validates the witness on top. Bounded to a
                    // 10k-point domain, so cheap even if repeated per split.
                    if matches!(other, TheoryResult::NeedSplit(_))
                        && (!self.monomials.is_empty() || self.has_scaled_product_vars())
                    {
                        let enum_start = ay_core::time::Instant::now();
                        let capped = self.try_capped_model_search();
                        self.timings.enumeration += enum_start.elapsed();
                        if let Some(result) = capped {
                            if self.debug {
                                safe_eprintln!(
                                    "[NIA] Capped model search decided before forwarding \
                                     NeedSplit: {result:?}"
                                );
                            }
                            return result;
                        }
                    }
                    return lia_result.clone();
                }
            }
        }

        TheoryResult::Unknown
    }
}

/// Union-find over factor terms keyed by asserted equalities, used by
/// [`NiaSolver::add_monomial_congruence_lemmas`]. `parent` tracks class
/// membership for `find`; `edges` records, for every union, the ORIGINAL pair
/// of arguments and the equality literal connecting them, so the *exact* chain
/// of justifying literals between any two equal terms can be recovered.
///
/// ## Why the edge graph (and not just parent edges)
///
/// A prior version stored a single `(parent_root, lit)` edge per non-root and
/// collected those literals up to the class root. That is UNSOUND for reason
/// tracking: `union(a, b, lit)` attaches `find(a)` under `find(b)` labeled with
/// `lit`, but `lit` only justifies `a = b` — NOT `find(a) = find(b)` when `a`
/// or `b` is not already a root. The intermediate literals connecting `a` to
/// `find(a)` (or `b` to `find(b)`) are then dropped, yielding an INCOMPLETE
/// reason set. Example (the #nia-congruence-reasons wrong-UNSAT): asserting
/// `z = x*z` (lit A) then `m = x*z` (lit B) makes `z` a root and records
/// `m -> z` labeled B only; `path_reasons(z, m)` returns `[B]`, losing A, even
/// though `z = m` genuinely needs BOTH `z = x*z` and `m = x*z`. A congruence
/// lemma (or model-equality request) built on that under-justified reason set
/// is then propagated by DPLL(T) under assignments where it is not entailed —
/// a spurious conflict / wrong UNSAT.
///
/// Recording every original argument edge and walking the real path fixes this:
/// the edges form a spanning forest (an edge is added only when the endpoints
/// were in different classes), so `path_reasons` finds the unique path and
/// collects the complete, sound justification. The trees are tiny (factors in a
/// single VC), so the cost is negligible.
#[derive(Default)]
struct EqUnionFind {
    /// `parent[x]` = (parent term, connecting literal). Used ONLY for `find`
    /// (class membership); the stored literal is NOT used for reasons — see the
    /// struct docs on why root-path literals are unsound as an explanation.
    parent: BTreeMap<TermId, (TermId, TheoryLit)>,
    /// Undirected adjacency over the ORIGINAL union arguments: `edges[a]`
    /// contains `(b, lit)` for every `union(a, b, lit)` (and vice-versa).
    /// `path_reasons` walks this forest to recover the exact literal chain.
    edges: BTreeMap<TermId, Vec<(TermId, TheoryLit)>>,
}

impl EqUnionFind {
    /// Representative (root) of `x`'s class. No path compression.
    fn find(&self, mut x: TermId) -> TermId {
        while let Some(&(p, _)) = self.parent.get(&x) {
            x = p;
        }
        x
    }

    /// Append to `out` the equality literals justifying `a = b` (assumes
    /// `find(a) == find(b)`). Walks the unique path from `a` to `b` in the
    /// original-argument edge forest via BFS; every edge literal on that path
    /// is a literal asserted true, and the chain `a = ... = b` entails `a = b`.
    /// The reason set is exact (every literal actually used) and sound.
    fn path_reasons(&self, a: TermId, b: TermId, out: &mut Vec<(TermId, bool)>) {
        if a == b {
            return;
        }
        // BFS from `a`, recording the predecessor edge for each visited node so
        // the path back to `a` can be reconstructed.
        let mut prev: BTreeMap<TermId, (TermId, TheoryLit)> = BTreeMap::new();
        let mut visited: std::collections::BTreeSet<TermId> = std::collections::BTreeSet::new();
        let mut queue: std::collections::VecDeque<TermId> = std::collections::VecDeque::new();
        visited.insert(a);
        queue.push_back(a);
        while let Some(cur) = queue.pop_front() {
            if cur == b {
                break;
            }
            let Some(neighbors) = self.edges.get(&cur) else {
                continue;
            };
            for &(next, lit) in neighbors {
                if visited.insert(next) {
                    prev.insert(next, (cur, lit));
                    queue.push_back(next);
                }
            }
        }
        // Reconstruct `b -> ... -> a`, collecting each edge's literal. If `b`
        // was unreachable (should not happen when find(a)==find(b)), fail-safe
        // by returning what was collected so far.
        let mut node = b;
        while node != a {
            let Some(&(p, lit)) = prev.get(&node) else {
                return;
            };
            out.push((lit.term, lit.value));
            node = p;
        }
    }

    /// Union the classes of `a` and `b`, recording `lit` (the asserting
    /// equality `a = b`) on the ORIGINAL argument edge `a <-> b`. No-op if
    /// already in the same class (keeps the edge graph a forest).
    fn union(&mut self, a: TermId, b: TermId, lit: TheoryLit) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return;
        }
        // Record the exact argument edge (both directions) for reason recovery.
        self.edges.entry(a).or_default().push((b, lit));
        self.edges.entry(b).or_default().push((a, lit));
        // Maintain `find` connectivity by attaching one root under the other.
        // Direction is arbitrary for correctness; deterministic by TermId. The
        // literal stored here is a placeholder (reasons come from `edges`).
        let (child, parent) = if ra.0 <= rb.0 { (rb, ra) } else { (ra, rb) };
        self.parent.insert(child, (parent, lit));
    }
}

#[cfg(test)]
mod eq_union_find_tests {
    use super::EqUnionFind;
    use ay_core::term::TermId;
    use ay_core::TheoryLit;

    fn lit(t: u32) -> TheoryLit {
        TheoryLit {
            term: TermId(t),
            value: true,
        }
    }

    /// Regression for the #nia-congruence-reasons wrong-UNSAT: two terms made
    /// equal *transitively* through a shared third term must report BOTH
    /// justifying literals, even when one endpoint becomes the class root.
    ///
    /// Models the bug shape: assert `z = x*z` (litA) then `m = x*z` (litB).
    /// `z` and `m` are then equal, but only because of BOTH equalities;
    /// `path_reasons(z, m)` must include litA AND litB, never just one.
    #[test]
    fn path_reasons_are_complete_through_a_shared_term() {
        let (z, m, xz) = (TermId(4), TermId(6), TermId(22));
        let (lit_a, lit_b) = (lit(23), lit(24));

        let mut uf = EqUnionFind::default();
        uf.union(z, xz, lit_a); // z = x*z
        uf.union(m, xz, lit_b); // m = x*z

        // z and m are in the same class.
        assert_eq!(uf.find(z), uf.find(m));

        let mut reasons = Vec::new();
        uf.path_reasons(z, m, &mut reasons);
        reasons.sort_unstable();
        reasons.dedup();

        assert!(
            reasons.contains(&(lit_a.term, lit_a.value)),
            "reasons for z=m must cite z=x*z (litA); got {reasons:?}"
        );
        assert!(
            reasons.contains(&(lit_b.term, lit_b.value)),
            "reasons for z=m must cite m=x*z (litB); got {reasons:?}"
        );
    }

    /// A longer transitive chain a=b=c=d: reasons for a=d must list every edge.
    #[test]
    fn path_reasons_cover_a_full_chain() {
        let (a, b, c, d) = (TermId(1), TermId(2), TermId(3), TermId(4));
        let mut uf = EqUnionFind::default();
        uf.union(a, b, lit(10));
        uf.union(b, c, lit(11));
        uf.union(c, d, lit(12));

        let mut reasons = Vec::new();
        uf.path_reasons(a, d, &mut reasons);
        reasons.sort_unstable();
        for t in [10u32, 11, 12] {
            assert!(
                reasons.contains(&(TermId(t), true)),
                "chain reason {t} missing; got {reasons:?}"
            );
        }
    }

    /// Identical endpoints need no justification.
    #[test]
    fn path_reasons_reflexive_is_empty() {
        let uf = EqUnionFind::default();
        let mut reasons = Vec::new();
        uf.path_reasons(TermId(7), TermId(7), &mut reasons);
        assert!(reasons.is_empty());
    }
}
