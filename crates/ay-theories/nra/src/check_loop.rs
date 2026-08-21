// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NRA check loop: LRA check -> sign -> patch -> tangent refinement.
//!
//! Contains the main iteration loop and its supporting methods:
//! tentative scope management, sign injection, division refinement,
//! monomial consistency checks, and sign checking.
//!
//! Extracted from lib.rs as part of #5970 code-health splits.

use ay_core::term::{Constant, TermData, TermId};
use ay_core::{TheoryLit, TheoryResult, TheorySolver};
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::NraSolver;
use crate::sign;

mod factor_definition;
mod global_recheck;

impl NraSolver<'_> {
    /// Undo all tentative scopes (sign-cut + patch) if any are active.
    /// Both the sign-cut scope (pushed at lib.rs:322) and the patch scope
    /// (pushed at patch.rs:245) must be popped to prevent model-dependent
    /// bounds from leaking into future queries.
    pub(crate) fn undo_tentative_patch(&mut self) {
        while self.tentative_depth > 0 {
            self.lra.pop();
            self.tentative_depth -= 1;
        }
        self.compound_defs_emitted.clear();
        self.linearization_rows.clear();
    }

    /// Add one linearization row, suppressing a row whose linear content is
    /// already live in the current tentative scope.  Returns `true` when the
    /// row is NEW.
    ///
    /// This is what makes the refinement loop's own `added == 0` stop honest.
    /// [`NraSolver::add_mccormick_constraints`] builds its rows from the LRA
    /// BOUNDS, not from the model point, so on a half-bounded monomial
    /// (`x >= 0` with no upper bound — the whole zankl matrix-interpretation
    /// shape) it re-emits the identical `m >= 0` row on every iteration and
    /// returns a positive count.  `added` therefore never reached 0, the
    /// "no new lemma" stop could never fire, and the loop burned all 500
    /// iterations re-deriving one constraint before declining anyway
    /// (measured: zankl/matrix-1-all-01 logs the same eight
    /// `McCormick envelope: 1 constraints` at iteration 1 and at iteration
    /// 500).  A duplicate row cannot tighten the relaxation, so suppressing it
    /// removes work, not information.
    pub(crate) fn add_linearization_cut(
        &mut self,
        cut: &ay_lra::GomoryCut,
        source: TermId,
    ) -> bool {
        // This cache deliberately keys only the reasonless, source-free rows
        // emitted by the model-guided linearization loop.  A future caller may
        // attach proof/conflict metadata that distinguishes two otherwise
        // identical inequalities.  Never let a release build erase that
        // evidence merely because the debug assertion which used to guard this
        // contract is compiled out: metadata-bearing rows bypass the cache and
        // are reported as progress.
        if !cut.reasons.is_empty() || cut.source_term.is_some() {
            self.lra.add_gomory_cut(cut, source);
            return true;
        }
        let key = (source, cut.coeffs.clone(), cut.bound.clone(), cut.is_lower);
        if !self.linearization_rows.insert(key) {
            return false;
        }
        self.lra.add_gomory_cut(cut, source);
        true
    }

    /// Inject model-derived sign bounds for original variables into a tentative
    /// LRA scope. Based on Z3's `nla_basics_lemmas.cpp:sign_lemma()`.
    ///
    /// Returns the number of NEW rows, on the same contract as
    /// [`NraSolver::add_linearization_cut`]: a sign cut identical to one already
    /// live in this scope leaves LRA unchanged, so counting it would report
    /// progress the loop did not make.
    fn inject_tentative_sign_cuts(&mut self) -> usize {
        use ay_lra::GomoryCut;
        let vars = sign::vars_needing_model_sign(
            &self.monomials,
            &self.aux_to_monomial,
            &self.var_sign_constraints,
        );
        let zero = BigRational::zero();
        let mut added = 0;
        for var_id in vars {
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
            let lra_var = self.lra.ensure_var_registered(var_id);
            added += usize::from(self.add_linearization_cut(
                &GomoryCut {
                    coeffs: vec![(lra_var, BigRational::one())],
                    bound: zero.clone(),
                    is_lower,
                    reasons: Vec::new(),
                    source_term: None,
                },
                var_id,
            ));
        }
        added
    }

    /// Get the value of a term: tries LRA model first, then constant extraction.
    /// Handles rational and integer constants that may not have LRA variables (#6811).
    pub(crate) fn term_value(&self, term: TermId) -> Option<BigRational> {
        if let Some(val) = self.lra.get_value(term) {
            return Some(val);
        }
        match self.terms.get(term) {
            TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
            TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
            _ => None,
        }
    }

    /// #div0-soundness: returns true when the candidate model's zero-divisor
    /// divisions cannot be certified as a sound SAT witness. SMT-LIB makes `/`
    /// total but leaves `(/ a 0)` UNCONSTRAINED — an arbitrary value that must
    /// still be a consistent FUNCTION of the arguments. The purification
    /// constraint `denom * div = num` is vacuous at `denom = 0` (it becomes
    /// `0 = num`, leaving `div` free), and constant-zero divisors are never
    /// purified at all, so distinct `(/ a 0)` occurrences are over-approximated
    /// as independent free LRA variables. That would let e.g.
    /// `(< (/ 0 x) (/ x 0))` with `x = 0` pass as SAT even though both sides
    /// denote the same unspecified `(/ 0 0)` value.
    ///
    /// The model IS a genuine witness when every pair of zero-denominator
    /// divisions whose numerators agree in the model also agree on the division
    /// value: the division function can then be extended to those points
    /// exactly as the model chose (the `unconstrained-but-consistent value`
    /// machinery promised in 28f8ca51; unblocks e.g. `x = 0 ∧ (/ 1 x) != 5`,
    /// Z3 #9319). We group zero-denominator divisions by numerator model value
    /// and fail closed (return true → Unknown) only when a group disagrees, or
    /// when a numerator has no model value at all (nothing to certify against).
    ///
    /// A division whose value is unconstrained by the model (`None`) is
    /// consistent with any group: a total extension can pick the group value.
    /// A denominator with no model value cannot be confirmed zero and is left
    /// to the purification refinement (it does not force Unknown on its own;
    /// literal constants always have a value via `term_value`).
    pub(crate) fn zero_divisor_model_is_unsound(&self) -> bool {
        // (numerator model value) -> division value chosen by the model, if
        // any member of the group has one. Few divisions per problem, so a
        // linear scan beats hashing rationals.
        let mut groups: Vec<(BigRational, Option<BigRational>)> = Vec::new();
        for div in &self.div_terms {
            let Some(denom_val) = self.term_value(div.denominator) else {
                continue;
            };
            if !denom_val.is_zero() {
                continue;
            }
            let Some(num_val) = self.term_value(div.numerator) else {
                // Zero divisor with an unvalued numerator: the functional
                // grouping cannot be established — fail closed.
                return true;
            };
            let div_val = self.term_value(div.div_term);
            if let Some((_, group_val)) = groups.iter_mut().find(|(n, _)| *n == num_val) {
                match (&group_val, &div_val) {
                    (Some(u), Some(v)) if u != v => return true,
                    (None, Some(_)) => *group_val = div_val,
                    _ => {}
                }
            } else {
                groups.push((num_val, div_val));
            }
        }
        false
    }

    /// Check if any tracked division has an inconsistent model value.
    /// Returns true if `model(denom) * model(div_term) != model(num)`.
    /// # Fail-open surface, PROBED and found unreached — but structurally present
    ///
    /// The three `else { continue; }` guards below are the same shape as the
    /// defect fixed in `check_monomial_consistency`: when a value cannot be
    /// resolved, the loop skips that purification, which reports the division
    /// CONSISTENT having checked nothing. `term_value` resolves only an LRA
    /// column or a literal constant, so any COMPOUND numerator — a Horner
    /// polynomial, exactly what broke the monomial check — returns `None` here.
    ///
    /// MEASURED 2026-08-06 with an env-gated probe on both `term_value`
    /// numerator guards: **0 of 145 files reach it** (the 17 invalid-model
    /// files, the 8 `wrong_unsat_metitarski_exp` canaries, and a 120-file
    /// random sample of the MV QF_NRA selection). So this is a latent hazard,
    /// not a live defect, and it is deliberately NOT being "fixed" — swapping in
    /// the structural resolver would change refinement behaviour on a path with
    /// no measured problem, which is how a lane trades a real asset for a
    /// speculative one.
    ///
    /// What to do if it ever IS reached: use the structural resolver
    /// (`factor_value`) for the numerator, exactly as `monomial_factor_value`
    /// does, and re-measure the whole MV selection for refinement regressions.
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
            // #div0-soundness: at denom = 0 the purification constraint
            // `denom * div = num` does NOT hold semantically — SMT-LIB leaves
            // `(/ num 0)` unconstrained — so enforcing `0 * div = num` here
            // would wrongly reject every zero-divisor model. Functional
            // consistency of zero-divisor divisions is checked separately by
            // `zero_divisor_model_is_unsound` at each Sat exit.
            if denom_val.is_zero() {
                continue;
            }
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
    fn generate_division_refinement(&mut self) -> usize {
        use ay_lra::GomoryCut;

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

            // #div0-soundness: the tangent plane below linearizes the
            // purification constraint `denom * div = num`, which is vacuous at
            // `denom = 0` (`(/ num 0)` is unconstrained). A lemma derived from
            // it at `d = 0` (e.g. `k * denom >= num`) excludes genuine
            // zero-divisor models and can drive a spurious UNSAT on the
            // trusted recheck path. Skip; `zero_divisor_model_is_unsound`
            // guards the Sat exits instead.
            if d.is_zero() {
                continue;
            }
            let product = &d * &k;
            if product == num_val {
                continue; // consistent
            }

            // Tangent plane: k*denom + d*div_term - d*k [cmp] num_val
            // Rearranged: k*denom + d*div_term [cmp] num_val + d*k
            let denom_var = self.lra.ensure_var_registered(purif.denominator);
            let div_var = self.lra.ensure_var_registered(purif.div_term);

            let coeffs = vec![(denom_var, k.clone()), (div_var, d.clone())];
            let bound = &num_val + &product;
            let is_lower = product < num_val;

            self.lra.add_gomory_cut(
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
                tracing::debug!(
                    "[NRA] division refinement: denom={:?}, div={:?}, d={}, k={}, num={}",
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

    /// Exact value of a monomial FACTOR under the current linear model.
    ///
    /// A factor is NOT always a simplex-rowed term. `lra.get_value` answers only
    /// for terms the tableau actually carries — the declared variables and the
    /// opaque aux terms that stand for whole nonlinear products. MetiTarski-style
    /// Taylor polynomials are emitted in HORNER form, so every product nests a
    /// compound `+` term as its last factor:
    ///
    /// ```text
    /// (* skoX skoX (+ (* skoX skoX (+ (* skoX skoX 1/720) -1/24)) 1/2))
    /// ```
    ///
    /// That inner `(+ ...)` is a linear combination, not a tableau column, so
    /// `lra.get_value` returns `None` for it — and the caller used to read that
    /// `None` as "consistent" (see [`Self::check_monomial_consistency`]).
    ///
    /// Resolution order matters and is deliberate:
    ///
    /// 1. `lra.get_value` FIRST, so a nested product aux term contributes the
    ///    OPAQUE value the linear abstraction assigned it. That keeps the check
    ///    local — each monomial is verified against its immediate factors, and
    ///    global consistency follows by induction over the monomial set. It is
    ///    also what makes the check able to FAIL: recomputing a nested product
    ///    structurally would make every monomial trivially agree with itself.
    /// 2. Structural evaluation only for terms the tableau does not carry:
    ///    constants and `+`/`-`/`*`/`/` nodes over factors that resolve.
    ///
    /// Returns `None` when the value genuinely cannot be determined. See
    /// [`Self::check_monomial_consistency`] for what the caller does with that.
    ///
    /// Call through [`Self::monomial_factor_value`] rather than passing a depth
    /// by hand.
    fn factor_value(&self, term: TermId, depth: u32) -> Option<BigRational> {
        if let Some(v) = self.lra.get_value(term) {
            return Some(v);
        }
        // Depth guard: term graphs are DAGs and can nest arbitrarily. Horner
        // chains in this corpus reach ~12; 64 leaves headroom while keeping a
        // hostile input from exhausting the stack.
        if depth == 0 {
            return None;
        }
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
            TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
            TermData::App(ay_core::term::Symbol::Named(name), args) => match name.as_str() {
                "+" if !args.is_empty() => {
                    let mut acc = BigRational::zero();
                    for &a in args {
                        acc += self.factor_value(a, depth - 1)?;
                    }
                    Some(acc)
                }
                "*" if !args.is_empty() => {
                    let mut acc = BigRational::one();
                    for &a in args {
                        acc *= self.factor_value(a, depth - 1)?;
                    }
                    Some(acc)
                }
                "-" if args.len() == 1 => Some(-self.factor_value(args[0], depth - 1)?),
                "-" if args.len() >= 2 => {
                    let mut acc = self.factor_value(args[0], depth - 1)?;
                    for &a in &args[1..] {
                        acc -= self.factor_value(a, depth - 1)?;
                    }
                    Some(acc)
                }
                "/" if args.len() == 2 => {
                    let num = self.factor_value(args[0], depth - 1)?;
                    let den = self.factor_value(args[1], depth - 1)?;
                    // Division by zero is left to the dedicated zero-divisor
                    // machinery (`zero_divisor_model_is_unsound`); do not
                    // invent a quotient here.
                    if den.is_zero() {
                        None
                    } else {
                        Some(num / den)
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Value of a monomial factor at the standard evaluation depth. Single
    /// entry point so every consumer of a monomial (consistency check, model
    /// patcher, tangent refinement) resolves factors identically — they used to
    /// disagree only by each having its own copy of the same blind spot.
    pub(crate) fn monomial_factor_value(&self, term: TermId) -> Option<BigRational> {
        // Depth guard: term graphs are DAGs and can nest arbitrarily. Horner
        // chains in this corpus reach ~12; 64 leaves headroom while keeping a
        // hostile input from exhausting the stack.
        const FACTOR_EVAL_MAX_DEPTH: u32 = 64;
        self.factor_value(term, FACTOR_EVAL_MAX_DEPTH)
    }

    // `check_monomial_consistency` lives in `check_loop/factor_definition.rs`,
    // and resolves its factors through `monomial_factor_value` above. See that
    // function for why the two halves — this resolver and that residual policy —
    // belong together.

    /// Generate refinement lemmas for inconsistent monomials.
    ///
    /// Uses McCormick envelopes (sound, globally valid for bounded variables)
    /// and tangent hyperplanes (model-point approximations) as Gomory cuts.
    ///
    /// Returns the number of constraints added.
    fn generate_refinement_lemmas(&mut self) -> usize {
        let definitions = self.emit_factor_definitions();
        // McCormick envelopes + tangent hyperplanes
        let (tangent_added, _) = self.add_tangent_constraints_for_incorrect_monomials();
        self.tangent_lemma_count += tangent_added as u64;

        definitions + tangent_added
    }

    /// Check sign consistency: propagate factor signs, then detect conflicts.
    fn check_signs(&mut self) -> Option<TheoryResult> {
        sign::propagate_product_signs(
            self.monomials.values().chain(self.scaled_aliases.iter()),
            &mut self.var_sign_constraints,
        );
        if let Some(conflict) = sign::check_sign_consistency(
            &self.monomials,
            &self.sign_constraints,
            &self.var_sign_constraints,
            &self.asserted,
            self.debug,
        ) {
            self.conflict_count += 1;
            return Some(TheoryResult::Unsat(conflict));
        }
        None
    }

    /// Normalize the LRA check result for the NRA check loop.
    ///
    /// LRA's `check()` may return `NeedModelEquality` or `NeedModelEqualities`
    /// when it discovers that two terms have the same model value (Z3's
    /// `assume_eqs`). In the standalone LRA pipeline, the DPLL(T) layer
    /// handles these by creating equality atoms in the SAT solver.
    ///
    /// Inside the NRA check loop, however, these equality requests are
    /// irrelevant: the NRA solver manages the nonlinear relationship between
    /// variables and their monomials directly. Passing NeedModelEquality
    /// through to the outer DPLL(T) loop causes an infinite refinement cycle
    /// because LRA re-discovers the same model-value equalities on every
    /// re-entry. The linear constraints are satisfied (LRA found Sat before
    /// discovering the equalities), so treating these as Sat is sound.
    pub(crate) fn normalize_lra_result(&self, result: TheoryResult) -> TheoryResult {
        match &result {
            TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_) => {
                // LRA found Sat but also wants model equalities. Inside NRA,
                // we only care about the linear Sat — the nonlinear part is
                // checked by the monomial consistency loop.
                if self.debug {
                    tracing::debug!("[NRA] Suppressing LRA NeedModelEquality — treating as Sat");
                }
                TheoryResult::Sat
            }
            _ => result,
        }
    }

    /// Run the NRA check loop and, on an UNSAT verdict, attempt to attach a
    /// replayable rational Positivstellensatz / SOS certificate of infeasibility
    /// (see [`crate::sos`]). The certificate — when the degree-2 search finds one
    /// — replaces the audited `:rule trust` hole for that theory conflict with an
    /// independently checkable algebraic proof. When the search declines (its
    /// search is sound but incomplete), the interval-exhaustion UNSAT stands with
    /// its existing `:rule trust`; no verdict is regressed.
    pub(crate) fn nra_check_loop(&mut self) -> TheoryResult {
        self.last_unsat_certificate = None;
        let result = self.nra_check_loop_impl();
        if matches!(result, TheoryResult::Unsat(_)) {
            let cert = self.try_build_unsat_sos_certificate();
            if let Some(c) = &cert {
                if self.debug {
                    tracing::info!("[NRA] {}", c.summary());
                    tracing::info!(
                        "[NRA] {}",
                        c.render_alethe("t_nra_unsat", |t| self.var_print_name(t))
                    );
                }
            }
            self.last_unsat_certificate = cert;
        }
        result
    }

    /// Print name for a variable term, for certificate rendering.
    fn var_print_name(&self, t: TermId) -> String {
        match self.terms.get(t) {
            TermData::Var(name, _) => name.clone(),
            _ => format!("v{}", t.0),
        }
    }

    /// Build a Positivstellensatz certificate for the current (refuted) asserted
    /// set, or `None` if the degree-2 rational search does not find one. Reads
    /// only `self.asserted`, so it works uniformly for every UNSAT surface
    /// (interval exhaustion, ICP branch-and-prune, linear substitution, the
    /// univariate decider). The returned certificate is guaranteed to pass the
    /// independent checker ([`crate::sos::SosCertificate::verify`]).
    fn try_build_unsat_sos_certificate(&self) -> Option<crate::sos::SosCertificate> {
        let mut constraints = Vec::new();
        for &(atom, value) in &self.asserted {
            match self.atom_to_multi(atom, value) {
                // A pure-constant false atom is a degenerate UNSAT with no
                // polynomial refutation to certify; leave the trust fallback.
                Some(crate::univariate::MultiAtom::ConstFalse) => return None,
                Some(crate::univariate::MultiAtom::ConstTrue) => {}
                Some(crate::univariate::MultiAtom::Constraint(c)) => constraints.push(c),
                // An unsupported atom means the polynomial view is incomplete, so
                // any certificate over the parsed subset would not refute the
                // full conjunction — decline.
                None => return None,
            }
        }
        if constraints.is_empty() {
            return None;
        }
        let mut vars: Vec<TermId> = Vec::new();
        for c in &constraints {
            for v in c.poly.variables() {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        vars.sort_unstable_by_key(|t| t.0);
        crate::sos::search(&constraints, &vars)
    }

    /// Run the NRA check loop: LRA check -> sign -> patch -> tangent.
    ///
    /// Following Z3's NLA check sequence (nla_core.cpp):
    /// sign consistency, model patching, then tangent plane refinement.
    fn nra_check_loop_impl(&mut self) -> TheoryResult {
        // Capture asserted-pin authority at iteration 0 in the clean base state.
        // The snapshot trusts asserted atoms, never LRA bounds or tentative scope.
        self.fixed_factor_values.clear();
        self.fixed_lin_emitted.clear();
        self.compound_defs_emitted.clear();

        // Exact INTERVAL-PROPAGATION UNSAT pre-phase (sound, BigRational-only).
        // A forward exact-interval pass decides bounded multivariate infeasibilities such as
        // `x>2 ∧ x^2+y^2<1`, left `unknown` by tangent/McCormick and
        // univariate / linear-substitution paths cannot reach (the constraint
        // genuinely couples two variables). It computes a SOUND interval
        // over-approximation of each constraint polynomial over the per-variable
        // bound box and reports UNSAT only when one constraint lies wholly outside its relation.
        // It NEVER emits SAT (interval feasibility gives no witness).
        // See univariate.rs (`try_interval_unsat`).
        match self.try_interval_unsat() {
            crate::univariate::UniResult::Unsat => {
                let conflict: Vec<TheoryLit> = self
                    .asserted
                    .iter()
                    .map(|&(t, v)| TheoryLit { term: t, value: v })
                    .collect();
                return TheoryResult::Unsat(conflict);
            }
            // Sat/SatAlgebraic are never produced here; Unknown falls through
            // unchanged.
            crate::univariate::UniResult::Sat(_)
            | crate::univariate::UniResult::SatAlgebraic(_)
            | crate::univariate::UniResult::Unknown => {}
        }

        // Exact BigRational sum-of-squares/quadratic positivity UNSAT pre-phase.
        // Decides multivariate infeasibilities that
        // couple variables through a cross term and so escape the interval phase
        // — e.g. `(x+y)^2 < 0`, `x^2+y^2 < 0`, `x^2+y^2+1 = 0`. For a single
        // constraint whose polynomial is a homogeneous quadratic form plus a
        // constant, it computes a SOUND global range via an exact LDL^T
        // PSD/NSD test and reports UNSAT only when the range misses the relation.
        // It NEVER emits SAT; Unknown falls through. See `try_sos_unsat`.
        match self.try_sos_unsat() {
            crate::univariate::UniResult::Unsat => {
                let conflict: Vec<TheoryLit> = self
                    .asserted
                    .iter()
                    .map(|&(t, v)| TheoryLit { term: t, value: v })
                    .collect();
                return TheoryResult::Unsat(conflict);
            }
            // Sat is never produced here; Unknown/SatAlgebraic fall through unchanged.
            crate::univariate::UniResult::Sat(_)
            | crate::univariate::UniResult::SatAlgebraic(_)
            | crate::univariate::UniResult::Unknown => {}
        }

        // Exact `is_int` decision pre-phase (sound, BigRational-only, #9139).
        // Decides affine/univariate `is_int(a*x+c)`, linear comparisons, and nonzero self-division
        // `(/ e e) -> 1` — that pure LRA cannot settle (it ignores integrality).
        // Like the other exact pre-phases it can ONLY turn unknown into a
        // correct sat/unsat: SAT is gated by re-verifying a concrete rational
        // witness against every atom; UNSAT requires an empty integrality region.
        // Uncertainty falls through unchanged. See `try_is_int_decide`.
        match self.try_is_int_decide() {
            crate::univariate::UniResult::Sat(model) => {
                self.inject_univariate_model(&model);
                return TheoryResult::Sat;
            }
            crate::univariate::UniResult::Unsat => {
                let conflict: Vec<TheoryLit> = self
                    .asserted
                    .iter()
                    .map(|&(t, v)| TheoryLit { term: t, value: v })
                    .collect();
                return TheoryResult::Unsat(conflict);
            }
            // The `is_int` fragment only ever produces rational SAT models (it
            // searches concrete integer-valued witnesses); it never emits an
            // algebraic certificate. Fail closed to fall-through if it ever does.
            crate::univariate::UniResult::SatAlgebraic(_)
            | crate::univariate::UniResult::Unknown => {
                // Out of fragment / uncertain — fall through unchanged.
            }
        }

        // Exact LINEAR-EQUALITY SUBSTITUTION pre-phase (sound, BigRational-only).
        // Eliminates variables fixed by `xi = (linear expr)`, reducing to the univariate decider
        // below can settle (e.g. `y=2 ; x^2+y^2=5`). Like the univariate path it
        // can ONLY convert unknown -> correct sat/unsat: SAT is gated by
        // re-verifying the full back-substituted model against every original
        // atom; UNSAT only propagates a genuine univariate UNSAT through a
        // satisfiability-preserving substitution; anything else is Unknown and
        // falls through unchanged. See univariate.rs.
        match self.try_linear_substitution_decide() {
            crate::univariate::UniResult::Sat(model) => {
                self.inject_univariate_model(&model);
                return TheoryResult::Sat;
            }
            // SAT proven by the exact Sturm/IVT irrational-root certificate
            // (e.g. `y=2 ; x*x=2`), with the FULL mixed witness assignment:
            // inject the rational witnesses into the LRA model and hand the
            // exact algebraic witnesses to the executor's model, where
            // evaluation/printing/validation handle them exactly.
            crate::univariate::UniResult::SatAlgebraic(witnesses) => {
                self.accept_algebraic_witnesses(witnesses);
                return TheoryResult::Sat;
            }
            crate::univariate::UniResult::Unsat => {
                let conflict: Vec<TheoryLit> = self
                    .asserted
                    .iter()
                    .map(|&(t, v)| TheoryLit { term: t, value: v })
                    .collect();
                return TheoryResult::Unsat(conflict);
            }
            // Out of fragment / uncertain — fall through to the univariate
            // path (which may itself certify, or to tangent).
            crate::univariate::UniResult::Unknown => {
                // Out of fragment or uncertain — fall through to univariate.
            }
        }

        // Exact univariate decision procedure (sound, BigRational-only).
        // Fires when the problem decomposes into independent single-variable
        // polynomial subproblems that the tangent/McCormick linearization
        // cannot decide (e.g. `x*x > 2`). It can ONLY convert unknown ->
        // correct sat/unsat; any uncertainty returns Unknown and we fall
        // through to the existing tangent path unchanged. See univariate.rs.
        match self.try_univariate_decide() {
            crate::univariate::UniResult::Sat(model) => {
                // Inject the exact rational witnesses as tight LRA bounds so the
                // extracted model reports the verified values, then report Sat.
                // The model was already verified by exact substitution against
                // every asserted atom inside try_univariate_decide.
                self.inject_univariate_model(&model);
                return TheoryResult::Sat;
            }
            // SAT proven by the exact Sturm/IVT irrational-root certificate
            // (e.g. `x*x=2`, `x*x=3 ∧ x<0`), with the FULL witness assignment
            // (exact algebraic values for the irrational variables, rationals
            // for the rest). Inject the rational part into the LRA model and
            // hand the algebraic part to the executor's model for exact
            // evaluation, z3-parity `root-obj` printing and full validation.
            crate::univariate::UniResult::SatAlgebraic(witnesses) => {
                self.accept_algebraic_witnesses(witnesses);
                return TheoryResult::Sat;
            }
            crate::univariate::UniResult::Unsat => {
                let conflict: Vec<TheoryLit> = self
                    .asserted
                    .iter()
                    .map(|&(t, v)| TheoryLit { term: t, value: v })
                    .collect();
                return TheoryResult::Unsat(conflict);
            }
            // Out of fragment / uncertain — fall through to the existing
            // tangent path unchanged (sound: never a wrong verdict).
            crate::univariate::UniResult::Unknown => {
                // Out of fragment or uncertain — fall through unchanged.
            }
        }

        // Bounded MULTIVARIATE rational-witness SEARCH (sound, SAT only).
        // Decides genuinely coupled two-variable SAT cases the linearization
        // misses — e.g. `x^2+y^2=1 ∧ x>1/2`, `x^2+y^2=25 ∧ x>0 ∧ y>0` — by
        // grounding one variable to rational candidates from a SOUND feasible
        // box and solving the remaining univariate system exactly. SAT is gated
        // by full model re-verification against every original atom; UNSAT is
        // NEVER emitted here (a bounded grid proves nothing). Unknown falls
        // through unchanged. See univariate.rs (`try_multivariate_witness_search`).
        match self.try_multivariate_witness_search() {
            crate::univariate::UniResult::Sat(model) => {
                self.inject_univariate_model(&model);
                return TheoryResult::Sat;
            }
            // SAT with a MIXED witness: the grounded variables are exact
            // rationals and the final variable's witness is the exact
            // algebraic root of the residual univariate system, leaf-verified
            // by Sturm sign determination (e.g. `x^2 = y^2 + 2` with `y = q`,
            // `x = root(x^2 - (q^2+2))`). Same channel as the univariate
            // Sturm/IVT certificate.
            crate::univariate::UniResult::SatAlgebraic(witnesses) => {
                self.accept_algebraic_witnesses(witnesses);
                return TheoryResult::Sat;
            }
            // Unsat is never produced here; Unknown falls through unchanged.
            crate::univariate::UniResult::Unsat | crate::univariate::UniResult::Unknown => {}
        }

        // INTERVAL BRANCH-AND-PRUNE decision procedure (sound, exact
        // BigRational, SAT and UNSAT). Decides genuinely coupled SMALL
        // MULTIVARIATE polynomial systems (2..=12 real unknowns) — the
        // sketch-geometry cluster fragment (triangulation distance loops,
        // tangency + closure systems, slider-crank couplings) — that every
        // earlier exact phase leaves unknown. HC4-style projection contraction
        // plus bisection refutes boxes with sound interval arithmetic; SAT is
        // certified either by a concrete rational point re-verified by exact
        // substitution into EVERY asserted atom, or by a Krawczyk
        // interval-Newton EXISTENCE certificate for an irrational witness
        // (reported through the same algebraic-certificate channel as the
        // univariate Sturm/IVT path). UNSAT is claimed ONLY when the box tree
        // is exhausted with every leaf refuted. Anything else — budget
        // exhaustion, unbounded variables, unsupported atoms — falls through
        // unchanged as Unknown. See icp.rs.
        match self.try_icp_branch_and_prune() {
            crate::univariate::UniResult::Sat(model) => {
                self.inject_univariate_model(&model);
                return TheoryResult::Sat;
            }
            // SAT proven by the Krawczyk existence certificate, with the full
            // witness assignment: the pinned variables are exact rationals and
            // the single free variable's witness is the exact algebraic root
            // of the pinned equality (icp.rs builds and re-verifies it).
            // Handled exactly like the Sturm/IVT certificate above.
            crate::univariate::UniResult::SatAlgebraic(witnesses) => {
                self.accept_algebraic_witnesses(witnesses);
                return TheoryResult::Sat;
            }
            crate::univariate::UniResult::Unsat => {
                let conflict: Vec<TheoryLit> = self
                    .asserted
                    .iter()
                    .map(|&(t, v)| TheoryLit { term: t, value: v })
                    .collect();
                return TheoryResult::Unsat(conflict);
            }
            // Out of fragment / uncertain — fall through to the tangent path
            // unchanged (sound: never a wrong verdict).
            crate::univariate::UniResult::Unknown => {}
        }

        // In debug mode, unoptimized BigRational arithmetic and
        // debug_assert_tableau_consistency checks make each LRA call ~100x
        // slower. 50 iterations with a growing tableau causes multi-minute
        // hangs (#6785). 15 iterations is enough to validate convergence
        // patterns without blocking the test suite.
        #[cfg(debug_assertions)]
        const MAX_ITERATIONS: usize = 15;
        // Release: 500 iterations to handle hard nonlinear problems.
        // The caller's deadline/interrupt handles timeout; this cap only
        // fires on genuinely pathological cases.
        #[cfg(not(debug_assertions))]
        const MAX_ITERATIONS: usize = 500;

        // SAT-only bilinear-template fallback: private exact residuals, gated
        // by original-atom verification; see `grounding` for its full contract.
        let mut grounding = self.build_grounding_plan();
        for iteration in 0..=MAX_ITERATIONS {
            let lra_result = self.lra.check();
            let lra_result = self.normalize_lra_result(lra_result);

            self.snapshot_fixed_factors_on_first_iteration(iteration);

            match &lra_result {
                TheoryResult::Sat | TheoryResult::Unknown => {
                    if self.debug {
                        tracing::debug!(
                            "[NRA] check iter={}, monomials={}, sign_constraints={}, var_sign_constraints={}",
                            iteration, self.monomials.len(), self.sign_constraints.len(),
                            self.var_sign_constraints.len()
                        );
                    }

                    if let Some(conflict) = self.check_signs() {
                        return conflict;
                    }

                    let monomial_ok = !self.has_inconsistent_monomials();
                    let division_ok = !self.has_inconsistent_divisions();
                    if monomial_ok && division_ok {
                        // #div0-soundness: zero-divisor divisions are
                        // unconstrained but must stay functionally consistent;
                        // fail closed to Unknown when the model cannot be
                        // certified (see `zero_divisor_model_is_unsound`).
                        if self.zero_divisor_model_is_unsound() {
                            return TheoryResult::Unknown;
                        }
                        if matches!(lra_result, TheoryResult::Unknown) {
                            return TheoryResult::Unknown;
                        }
                        return TheoryResult::Sat;
                    }

                    // Try early points densely, then sparse fresh points.
                    if crate::grounding::scheduled(iteration) {
                        if let Some(plan) = grounding.as_mut() {
                            if self.try_model_guided_grounding(plan) {
                                return TheoryResult::Sat;
                            }
                        }
                    }

                    // clauseSMT Technique 1 (#8445): feasible-set look-ahead.
                    // If any tracked variable has an empty feasible set (blocked),
                    // conflicts are unavoidable -- continue to refinement immediately
                    // rather than trying patches that will fail.
                    if !self.blocked_vars.is_empty() && self.debug {
                        tracing::debug!(
                            "[NRA] feasible-set look-ahead: {} blocked vars, skipping patch",
                            self.blocked_vars.len()
                        );
                    }

                    // clauseSMT Technique 1 (#8445): feasible-set path case.
                    // If a variable has a non-empty feasible set with a picked
                    // value, inject that value as a tentative bound to accelerate
                    // convergence. This is the "path case" from the clauseSMT
                    // paper — we already know a feasible value and direct the
                    // LRA solver toward it.
                    //
                    // Counted as progress on the same contract as every other
                    // row source: these bounds change the LRA state the next
                    // `check()` reads, so an iteration that adds one is NOT
                    // stalled even when the relaxation itself has saturated.
                    let mut look_ahead_rows = 0usize;
                    if let Some((var, suggested_val)) = self.feasible_set_look_ahead() {
                        if self.tentative_depth == 0 {
                            self.lra.push();
                            self.tentative_depth += 1;
                        }
                        // Inject both lower and upper bounds to fix the variable
                        // at the suggested value.
                        let lra_var = self.lra.ensure_var_registered(var);
                        look_ahead_rows += usize::from(self.add_linearization_cut(
                            &ay_lra::GomoryCut {
                                coeffs: vec![(lra_var, BigRational::one())],
                                bound: suggested_val.clone(),
                                is_lower: true,
                                reasons: Vec::new(),
                                source_term: None,
                            },
                            var,
                        ));
                        look_ahead_rows += usize::from(self.add_linearization_cut(
                            &ay_lra::GomoryCut {
                                coeffs: vec![(lra_var, BigRational::one())],
                                bound: suggested_val,
                                is_lower: false,
                                reasons: Vec::new(),
                                source_term: None,
                            },
                            var,
                        ));
                    }

                    // Step 5a: Tentative sign cuts for variables with unknown
                    // assertion-based sign. Push scope, add sign cuts, then
                    // proceed to tentative patch. If patch succeeds, sign cuts
                    // are kept. If not, undo_tentative_patch() pops everything.
                    // Based on Z3 nla_basics_lemmas.cpp:sign_lemma().
                    if self.tentative_depth == 0 {
                        self.lra.push();
                        self.tentative_depth += 1;
                    }
                    let sign_cuts = self.inject_tentative_sign_cuts();
                    self.sign_cut_count += sign_cuts as u64;

                    // Re-check consistency after sign cuts tightened LRA
                    if sign_cuts > 0
                        && !self.has_inconsistent_monomials()
                        && !self.has_inconsistent_divisions()
                    {
                        // #div0-soundness: fail closed on an uncertifiable
                        // zero-divisor model.
                        if self.zero_divisor_model_is_unsound() {
                            return TheoryResult::Unknown;
                        }
                        return TheoryResult::Sat;
                    }

                    // Model patching (Z3 nla_core.cpp:patch_monomials):
                    // tentative push/pop with Gomory cuts (#4125 soundness fix)
                    if self.try_tentative_patch() {
                        self.patch_count += 1;
                        if !self.has_inconsistent_divisions() {
                            // #div0-soundness: fail closed on an uncertifiable
                            // zero-divisor model.
                            if self.zero_divisor_model_is_unsound() {
                                return TheoryResult::Unknown;
                            }
                            return TheoryResult::Sat;
                        }
                    }

                    let mut added = self.generate_refinement_lemmas();
                    // Division refinement: tangent planes for denom * div = num (#6811).
                    // These are model-point approximations (same class as tangent planes).
                    let div_added = self.generate_division_refinement();
                    if div_added > 0 {
                        added += div_added;
                    }
                    // Progress is "a row entered LRA this iteration", from ANY
                    // source. The look-ahead pin and the sign cuts move the state
                    // the next `check()` reads just as a tangent plane does, so
                    // an iteration that produced one must not be reported as
                    // stalled — otherwise making the relaxation's stop honest
                    // would cost the loop the iterations those phases need.
                    added += look_ahead_rows + sign_cuts;
                    if added == 0 && iteration < MAX_ITERATIONS {
                        // A bound or tentative patch may make the current model
                        // consistent while adding no refinement. Re-enter so a
                        // fresh LRA check plus the ordinary consistency gates
                        // decides it; otherwise decline below.
                        if !self.has_inconsistent_monomials() && !self.has_inconsistent_divisions()
                        {
                            continue;
                        }
                    }
                    if added == 0 || iteration == MAX_ITERATIONS {
                        // Distinct SAT-only last chance after the exact
                        // fixed-factor retry; duplicate points are free.
                        if let Some(plan) = grounding.as_mut() {
                            if self.try_model_guided_grounding(plan) {
                                return TheoryResult::Sat;
                            }
                        }
                        if self.debug {
                            let bad = self
                                .products()
                                .filter(|m| !self.check_monomial_consistency(m))
                                .count();
                            tracing::debug!(
                                "[NRA] give up at iter={} (added={}, {} monomials still inconsistent)",
                                iteration,
                                added,
                                bad
                            );
                        }
                        return TheoryResult::Unknown;
                    }
                    continue;
                }
                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                    self.conflict_count += 1;
                    if iteration == 0 {
                        // Pre-refinement: pure linear UNSAT is a genuine UNSAT.
                        return lra_result.clone();
                    }
                    // Any post-refinement UNSAT may depend on a model-sign
                    // branch, model-derived bound, or division tangent plane.
                    // Re-establish it from the base state with authenticated
                    // global lemmas only.
                    return self.recheck_with_global_lemmas();
                }
                _ => return lra_result.clone(),
            }
        }

        TheoryResult::Unknown
    }

    /// Inject the exact rational witnesses found by the univariate decision
    /// procedure as tight (lower == upper) LRA bounds, so the extracted model
    /// reports the verified values. Pushed into a tentative scope that is
    /// cleaned up on the next assertion/check via `undo_tentative_patch`.
    ///
    /// After injecting, we re-run `lra.check()` so the simplex assignment (and
    /// hence the extracted model and the downstream SAT model validation) sees
    /// the witness values rather than stale defaults. This is purely a
    /// model-reporting convenience: satisfiability was already proven exactly by
    /// substitution in `try_univariate_decide`.
    pub(crate) fn inject_univariate_model(&mut self, model: &[(TermId, BigRational)]) {
        use ay_lra::GomoryCut;
        if model.is_empty() {
            return;
        }
        if self.tentative_depth == 0 {
            self.lra.push();
            self.tentative_depth += 1;
        }
        for (var, val) in model {
            let lra_var = self.lra.ensure_var_registered(*var);
            self.lra.add_gomory_cut(
                &GomoryCut {
                    coeffs: vec![(lra_var, BigRational::one())],
                    bound: val.clone(),
                    is_lower: true,
                    reasons: Vec::new(),
                    source_term: None,
                },
                *var,
            );
            self.lra.add_gomory_cut(
                &GomoryCut {
                    coeffs: vec![(lra_var, BigRational::one())],
                    bound: val.clone(),
                    is_lower: false,
                    reasons: Vec::new(),
                    source_term: None,
                },
                *var,
            );
        }
        // Refresh the simplex model so the extracted values reflect the witness.
        let _ = self.lra.check();
    }

    /// Accept a mixed rational/algebraic witness assignment from an exact
    /// decision procedure: inject the rational witnesses into the LRA model
    /// (so `extract_model` reports them) and record the exact algebraic
    /// witnesses in `self.algebraic_model` for the executor to store in its
    /// model, where evaluation, z3-parity `root-obj` printing and FULL model
    /// validation handle them exactly.
    fn accept_algebraic_witnesses(
        &mut self,
        witnesses: Vec<(TermId, crate::univariate::UniWitness)>,
    ) {
        let mut rational: Vec<(TermId, BigRational)> = Vec::new();
        let mut algebraic: Vec<(TermId, crate::RealAlgebraicValue)> = Vec::new();
        for (var, w) in witnesses {
            match w {
                crate::univariate::UniWitness::Rational(r) => rational.push((var, r)),
                crate::univariate::UniWitness::Algebraic(a) => algebraic.push((var, a)),
            }
        }
        self.inject_univariate_model(&rational);
        self.algebraic_model = algebraic;
    }
}
