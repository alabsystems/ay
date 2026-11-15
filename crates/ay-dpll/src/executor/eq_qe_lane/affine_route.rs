// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The lane's affine route: quantified roots over `Int` binders that the
//! proof-free affine elimination grounds (#qmv-affine-route).
//!
//! # The gap
//!
//! `∀v. c·v − v = 0` is `c = 1`: the body is affine in the binder, and an
//! affine form that holds for every integer has a zero coefficient and a zero
//! rest. The raw posture (`--z3-mode`) rewrites the assertion that way before
//! the quantifier loop (`simplify_vacuous_quantifiers` →
//! `simplify_infeasible_forall_eq`) and answers `sat`. The default posture
//! withholds that rewrite from the legacy window, because it emits no proof
//! step and a refutation of the rewritten window would have no authored-scope
//! derivation. The quantifier then reaches CEGQI, whose counterexample lemma
//! `c·k − k ≠ 0` is NONLINEAR; the NIA ground solve cannot settle it (measured
//! 2026-09-30: 11-15 s in the NIA local-search lane, then `Unknown`), so the
//! query ends `unknown (incomplete)` before any candidate model exists for the
//! quantified model gate to check. The model gate never refused anything: it
//! was never asked.
//!
//! # The route
//!
//! In the proof-carrying posture only (the raw posture already applies the
//! rewrite in place), a quantified root that is not in the equality fragment
//! is admitted when its binders are all `Int` and it is small enough for the
//! unmemoised rewrite ([`admits_root`]); it is replaced by
//! [`Executor::proof_free_quantifier_elimination`], and the root declines
//! unless that leaves it quantifier-free. Everything after the elimination is
//! the lane's unchanged discipline: the disposable ground probe, the in-place
//! solve, and the quantified model gate, which re-decides every AUTHORED
//! quantified conjunct against the model. The elimination only proposes the
//! model. The route never answers `unsat`.
//!
//! # What confirms a sat (and what the record says)
//!
//! Traced on every affine shape measured (2026-10-01 verification): the
//! lane's gate (`check_quantified_conjunct_against_model`) does NOT run a
//! nested solve. It folds each binder-free subterm (`c`, `(select A a)`,
//! `(f a)`, `(abs c)`, ...) to its exact model value with the independent
//! evaluator (step 1b), rebuilds the body with the term store's normalising
//! builders (`mk_app_simplified` → `mk_add`/`mk_mul`/`mk_eq`), which cancel
//! the binder terms of a satisfied affine body to `true`, drops the now
//! vacuous binder (1c2) and evaluates (1d). Exact (BigInt/BigRational), but
//! NOT code-independent of the elimination: `Executor::fold_linear_eqs` and
//! the affine split compute their coefficients with that same normaliser, so
//! a normaliser defect would hit both sides at once. Only a body that does
//! not reduce goes on to the gate's nested checked solve.
//!
//! The independent half comes later, in the SAT emission: the generic
//! quantified model check (FMQ `qmc`, `finite_model_mbqi/generic.rs`) fixes
//! the model, refutes each universal's negated substituted body in a nested
//! solve, re-checks the staged witness against the original residual, and
//! installs the full-domain grant the publication gate defers to. When it
//! certifies, its record is `model_check_gate.quantified` =
//! `deferred-certified-bv-full-domain`: every nested refutation was admitted
//! as checked (strict proof or independently re-checked); the label's `bv`
//! names the grant's first producer, not the binder sort.
//!
//! A nested refutation admitted only as `discharged-trust` (a fresh executor
//! running the SAME code re-decided the obligation) decides nothing, so FMQ
//! installs no grant on it. Measured on coefficients containing `abs`, `mod`
//! or `ite` (`∀v. |c|·v = v`, `(mod c 3)`, `(ite (> c 0) c (- c))`): the
//! nested proof is a single trust step. Those were published on that
//! same-engine re-solve until the probe mode refused the class.
//!
//! Where FMQ does not install a grant, the publication gate decides the
//! authored conjunct itself and records `confirmed`. For the measured shapes
//! (array-read and UF coefficients, `(div c (- 2))`, and the trust-step
//! coefficients above) that rests on the same fold and normaliser as the
//! lane's gate. Where the gate needs a nested refutation instead and that
//! refutation rests on `discharged-trust`, it records
//! `confirmed-discharged-trust` (and refuses it under strict rigor).
//!
//! A body that stays nonlinear in its binder (`∀v. c·v·v ≥ 0`) is not affine,
//! keeps its quantifier, and declines to the legacy path unchanged.

use ay_core::{Sort, TermData, TermId, TermStore};

use super::super::Executor;

/// Tree-walk visits a root may take before the route declines it: the
/// elimination recurses without memoisation, so a large shared DAG would be
/// re-walked once per path.
const MAX_AFFINE_ROOT_VISITS: usize = 1 << 14;

/// Whether the affine route may try `root`: every binder of every quantifier
/// in it is `Int`, and its tree has at most [`MAX_AFFINE_ROOT_VISITS`] nodes.
/// Reads the store only; nothing is minted.
pub(super) fn admits_root(terms: &TermStore, root: TermId) -> bool {
    let mut stack = vec![root];
    let mut visits = 0usize;
    while let Some(term) = stack.pop() {
        visits += 1;
        if visits > MAX_AFFINE_ROOT_VISITS {
            return false;
        }
        match terms.get(term) {
            TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                if !vars.iter().all(|(_, sort)| matches!(sort, Sort::Int)) {
                    return false;
                }
                stack.push(*body);
            }
            TermData::Let(..) => return false,
            _ => stack.extend(terms.children(term)),
        }
    }
    true
}

impl Executor {
    /// The affine route's quantifier-free equivalent of `root`, or `None`
    /// when a quantifier survives the elimination or it drops a symbol the
    /// lane cannot give a model value.
    pub(super) fn affine_route_eliminate(&mut self, root: TermId) -> Option<TermId> {
        let eliminated = self.proof_free_quantifier_elimination(root)?;
        (!self.affine_elimination_drops_unpinnable_symbol(root, eliminated)).then_some(eliminated)
    }

    /// Whether the elimination `eliminated` of `root` dropped a free symbol
    /// the lane cannot give a model value: anything but a scalar constant
    /// (`eq_qe_pin_vanished_constants` pins those). The in-place solve never
    /// sees a dropped symbol, so its model would print no value for it, and a
    /// `sat` must come with a total model (measured: `∀v. v·w = 0 ∨ 2v + h(s)
    /// = 1` eliminates to `w = 0` and lost `h` and `s`). Declining is the
    /// whole remedy; the root stays with the legacy path.
    fn affine_elimination_drops_unpinnable_symbol(&self, root: TermId, eliminated: TermId) -> bool {
        let kept = self.affine_route_symbols(eliminated);
        self.affine_route_symbols(root)
            .into_iter()
            .any(|(name, scalar)| !scalar && !kept.iter().any(|(k, _)| *k == name))
    }

    /// Free user symbols of `root` by name, each with whether it is a scalar
    /// (`Int`/`Real`/`Bool`) constant: unbound `Var` leaves, and applications
    /// whose head the frontend declared. Binder scope is tracked by name.
    fn affine_route_symbols(&self, root: TermId) -> Vec<(String, bool)> {
        let terms = &self.ctx.terms;
        let mut out: Vec<(String, bool)> = Vec::new();
        let mut stack: Vec<(TermId, Vec<String>)> = vec![(root, Vec::new())];
        while let Some((term, scope)) = stack.pop() {
            match terms.get(term) {
                TermData::Var(name, _) if !scope.contains(name) => {
                    let scalar = matches!(terms.sort(term), Sort::Int | Sort::Real | Sort::Bool);
                    if !out.iter().any(|(n, _)| n == name) {
                        out.push((name.clone(), scalar));
                    }
                }
                TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                    let mut inner = scope.clone();
                    inner.extend(vars.iter().map(|(name, _)| name.clone()));
                    stack.push((*body, inner));
                }
                TermData::App(sym, args) => {
                    let name = sym.name();
                    let declared = self.ctx.symbol_info_by_identity(name).is_some()
                        || self.ctx.symbol_info(name).is_some();
                    if declared && !out.iter().any(|(n, _)| n == name) {
                        out.push((name.to_string(), false));
                    }
                    stack.extend(args.iter().map(|&arg| (arg, scope.clone())));
                }
                _ => stack.extend(terms.children(term).into_iter().map(|c| (c, scope.clone()))),
            }
        }
        out
    }
}

#[cfg(test)]
mod tests;
