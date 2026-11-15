// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked array-to-UF abstraction: an authority rung of the nested-array
//! UNSAT quarantine (`nested_array_quarantine.rs`).
//!
//! # The class it admits
//!
//! A nested-array problem whose refutation needs no array axiom at all:
//!
//! ```text
//! (assert (= (select u 0) v))   ; u : (Array Int (Array Int Int))
//! (assert (= (select u 0) w))
//! (assert (not (= v w)))
//! ```
//!
//! `v = (select u 0) = w` contradicts `v != w` by congruence alone. Under
//! `--rigor fast` / `--no-proof` / `--z3-mode` the outer solve records no
//! proof, the entailed residue (`(not (= v w))`) is satisfiable and the query
//! is not Bool/BV, so every earlier rung declines and the quarantine used to
//! degrade this to `unknown`.
//!
//! # The abstraction `alpha`
//!
//! Every array SORT becomes a fresh uninterpreted sort, every array-sorted
//! constant a fresh constant of that sort, and every `select` / `store` /
//! `const-array` application a fresh uninterpreted function keyed on its full
//! typed signature. `=` and `distinct` are kept at the changed sorts. Nothing
//! else changes: the propositional skeleton, arithmetic, quantifier prefix and
//! every array-free subterm survive as the SAME term.
//!
//! # Why `alpha(phi)` UNSAT proves `phi` UNSAT
//!
//! Take any model `M` of `phi`. Build `M'` by interpreting each fresh sort as
//! the carrier of the array sort it replaced, each fresh constant as `M`'s
//! value of the constant it replaced, each fresh function as `M`'s
//! interpretation of the operation it replaced (at that one signature), and
//! everything else exactly as `M` does. Equality on a fresh sort is equality on
//! the array carrier, so `M'` gives every node of `alpha(phi)` the value `M`
//! gives the node it came from, and `M'` satisfies `alpha(phi)`. Dropping the
//! array axioms can only ADD models; it can never remove one.
//!
//! That argument holds only when `alpha` really is a renaming. Three things
//! could break it, and each is excluded by a check rather than by argument:
//!
//! * **Collapsing two identities onto one fresh name** would assert them equal
//!   (a strengthening). Every witness map must be injective, and every fresh
//!   name must be absent from `phi`.
//! * **A renamed head that is not a function of its argument VALUES** has no
//!   interpretation `M'` can copy. `lambda-array` is exactly that (a binder
//!   hidden in an `App`), as are `(_ map f)`, `default` and every other
//!   array-touching head not on the short [`build::RENAMED_ARRAY_OPS`] list: all of
//!   them decline.
//! * **Variable capture.** A quantifier that binds an array-sorted variable
//!   declines, and so does an array-sorted constant whose name any binder in
//!   `phi` reuses; renamed constants are therefore free on both sides.
//!
//! # Where the authority comes from
//!
//! Nothing above is trusted on the builder's say-so. [`is_pure_renaming`]
//! re-walks the original and abstract DAGs in lockstep and accepts only the
//! image of `phi` under the witness maps, node for node. The abstract roots are
//! then refuted by [`Executor::checked_strict_exact_unsat_solve`], a disposable
//! standard-posture solve whose UNSAT is accepted only when its complete
//! refutation proof passes the strict checker, and the resulting token is bound
//! to the exact ordered roots and the term-store snapshot.
//! [`CheckedArrayUfAbstractionUnsat`] carries that token together with the
//! original roots and the renaming witness, and its `consume` re-runs the
//! renaming check against the SAME snapshot the certificate is sealed to. The
//! abstract problem contains no array at all, so the refutation cannot rest on
//! the array combination the quarantine distrusts.
//!
//! # Declared carriers and axiom instances (#nested-array-checked-rung)
//!
//! A `declare-datatype` carrier that reaches an array (`Row` with an array
//! field, so `(Array I Row)` is nested) is renamed like an array sort, and its
//! constructors and selectors like `select`/`store`; the argument above is
//! unchanged, since each is a function of its argument values. A binary `=`
//! image lists its arguments in the TermId order `mk_eq` interns (the only
//! orientation the solver's equality-atom lookups find; the witness records
//! each swap, and equality is symmetric in `M'` as anywhere). Refuting a
//! record-boxed MODEL_CHECKER_CONSUMER obligation usually needs one datatype or array axiom
//! the renaming forgot, so a bounded set of ground axiom instances over the
//! fresh functions is appended (`instances.rs`: selector over constructor,
//! read over write, read over constant). Each holds in `M'` whatever its
//! arguments denote, because `M'` interprets every fresh function as the
//! operation it renames; so the abstraction still keeps every model of `phi`.
//! [`check_instances::instances_are_valid`] re-derives that from the witness
//! and the store, beside [`is_pure_renaming`], at preflight and at `consume`.
//! Extensionality and symbolic-index reasoning stay out of reach: an UNSAT
//! that needs them stays withheld.
//!
//! # Why strict proof only
//!
//! `checked_exact_unsat_solve` also admits the independently checked classes,
//! among them `DischargedTrust`, whose evidence is a fresh executor re-deriving
//! the same verdict. That is the solver agreeing with itself, and it is exactly
//! what the quantified Ultimate Automizer pin
//! (`test_nested_array_quantified_instance_unsat_without_authority_is_quarantined`)
//! says is not authority for a nested-array verdict: its abstraction certifies
//! only as `DischargedTrust`, so this rung leaves it withheld. The congruence
//! refutation above certifies as a strict proof.

mod build;
mod check;
mod check_instances;
mod instances;

use super::*;
use crate::executor::quantifier_loop::result_mapping::CheckedExactUnsat;
use build::ArrayUfAbstraction;
use check::is_pure_renaming;
use check_instances::instances_are_valid;

/// Wall-clock cap on the checked abstraction solve. A pure-EUF refutation of the
/// shape this rung exists for certifies in milliseconds.
const ABSTRACTION_MAX_BUDGET: Duration = Duration::from_millis(500);

/// The probe may claim at most 1/N of the outer solve's remaining budget.
const ABSTRACTION_BUDGET_SHARE: u32 = 4;

/// How many FAILED attempts a session tolerates before this rung stands down.
/// Same economics as `RESIDUE_MAX_FAILURES`: a conversion is cheap and buys a
/// verdict, a failure pays the whole budget and buys nothing, and an
/// incremental script reaches the quarantine once per check-sat.
const ABSTRACTION_MAX_FAILURES: u32 = 2;

/// Checked UNSAT authority for the ORIGINAL hard roots, derived from a
/// strict-proof refutation of their array-to-UF abstraction.
///
/// Linear and module-private in construction: the only way to obtain one is
/// [`Executor::nested_array_uf_abstraction_unsat`], and the only way to use it
/// is [`Self::consume`], which re-verifies the renaming against the exact
/// snapshot the inner certificate is sealed to.
#[must_use = "checked abstraction UNSAT authority must be consumed against its exact roots"]
#[derive(Debug)]
struct CheckedArrayUfAbstractionUnsat {
    checked: CheckedExactUnsat,
    original: Box<[TermId]>,
    abstraction: ArrayUfAbstraction,
    /// Axiom instances appended after the renamed roots (possibly none).
    instances: Box<[TermId]>,
}

impl CheckedArrayUfAbstractionUnsat {
    /// Accept iff all four hold, in this order:
    ///
    /// 1. `hard` is exactly the root vector the abstraction was built from;
    /// 2. the abstract roots are still a pure renaming of `hard` under the
    ///    carried witness ([`is_pure_renaming`], read-only);
    /// 3. every appended root is an axiom instance over that witness
    ///    ([`instances_are_valid`], read-only);
    /// 4. the inner certificate is current for exactly the renamed roots
    ///    followed by the instances: same query epoch, source context,
    ///    ordered roots and term-store snapshot, so checks 2 and 3 ran on the
    ///    store the refutation was sealed to.
    fn consume(self, executor: &mut Executor, hard: &[TermId]) -> bool {
        self.original.as_ref() == hard
            && is_pure_renaming(&executor.ctx.terms, hard, &self.abstraction)
            && instances_are_valid(&executor.ctx.terms, &self.abstraction, &self.instances)
            && self.checked.consume(
                executor,
                &abstract_problem(&self.abstraction, &self.instances),
            )
    }
}

/// The problem the probe refutes: the renamed roots, then the instances.
fn abstract_problem(abstraction: &ArrayUfAbstraction, instances: &[TermId]) -> Vec<TermId> {
    [abstraction.roots(), instances].concat()
}

impl Executor {
    /// Re-derive a quarantined nested-array UNSAT from a strict-proof
    /// refutation of the array-to-UF abstraction of the hard assertions. See
    /// the module docs for the soundness argument and for what is checked.
    ///
    /// Declines (returns `false`) after an external stop, inside another
    /// quarantine-rescue probe, when a proof artifact was requested (this rung
    /// has no proof of the ORIGINAL problem to hand back), and once the session
    /// has spent its failure allowance.
    pub(in crate::executor) fn nested_array_uf_abstraction_unsat(
        &mut self,
        hard: &[TermId],
    ) -> bool {
        if hard.is_empty()
            || self.external_stop_reason().is_some()
            || self.in_nested_array_residue_probe
            || self.is_producing_proofs()
            || self.array_uf_abstraction_failures >= ABSTRACTION_MAX_FAILURES
        {
            return false;
        }
        let refuted = self.try_checked_array_uf_abstraction(hard);
        if !refuted {
            self.array_uf_abstraction_failures =
                self.array_uf_abstraction_failures.saturating_add(1);
        }
        refuted
    }

    fn try_checked_array_uf_abstraction(&mut self, hard: &[TermId]) -> bool {
        let Some(abstraction) = ArrayUfAbstraction::build(&mut self.ctx.terms, hard) else {
            return false;
        };
        // Preflight only: a builder bug declines here instead of spending the
        // probe budget. The authoritative checks are the ones `consume` repeats.
        if !is_pure_renaming(&self.ctx.terms, hard, &abstraction) {
            tracing::warn!(
                "array-to-UF abstraction failed its renaming check; declining to the quarantine"
            );
            return false;
        }
        let instances = instances::axiom_instances(&mut self.ctx.terms, &abstraction);
        if !instances_are_valid(&self.ctx.terms, &abstraction, &instances) {
            tracing::warn!(
                "array-to-UF abstraction failed its axiom-instance check; declining to the quarantine"
            );
            return false;
        }
        let Some(budget_ms) = self.array_uf_abstraction_budget_ms() else {
            return false;
        };
        let problem = abstract_problem(&abstraction, &instances);
        let Some(checked) = self.checked_strict_exact_unsat_solve(problem, budget_ms) else {
            return false;
        };
        CheckedArrayUfAbstractionUnsat {
            checked,
            original: hard.into(),
            abstraction,
            instances,
        }
        .consume(self, hard)
    }

    /// A quarter of what the outer solve has left, capped at
    /// [`ABSTRACTION_MAX_BUDGET`]; `None` when nothing is left.
    fn array_uf_abstraction_budget_ms(&self) -> Option<u64> {
        let budget = match self.solve_deadline.get() {
            Some(deadline) => (deadline.saturating_duration_since(Instant::now())
                / ABSTRACTION_BUDGET_SHARE)
                .min(ABSTRACTION_MAX_BUDGET),
            None => ABSTRACTION_MAX_BUDGET,
        };
        let millis = u64::try_from(budget.as_millis()).unwrap_or(u64::MAX);
        (millis > 0).then_some(millis)
    }
}

#[cfg(test)]
#[path = "nested_array_uf_abstraction/tests.rs"]
mod tests;
