// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground-instantiation artifact-firewall translation for authored NEGATED
//! EXISTENTIALS (#inc-fparith-negated-exists-inst).
//!
//! THE GAP THIS CLOSES. `quantified_semantic_unsat_or_unknown` demands an
//! authored-scope translated refutation for every public query under mandatory
//! certification. On the Inc FPArith shape
//!
//! ```smt2
//! (assert (= ((_ to_fp 8 24) RNE (_ bv0 32)) y))
//! (assert (not (exists ((d (_ FloatingPoint 8 24)))
//!   (and (fp.geq d (_ +zero 8 24))
//!        (fp.leq d ((_ to_fp 8 24) RNE 16.0))
//!        (= (fp.sub RNE ((_ to_fp 8 24) RNE (_ bv0 32)) d) y)))))
//! ```
//!
//! AY reaches the correct semantic `Unsat` and then discards it: all three
//! firewall rescue legs decline (no trace-bound re-solve sidecar; the qpf lane
//! needs a bare `Forall` root AND a standalone-refutable instance; the authored
//! ground core alone is `sat`). The engine is not short of reasoning — it is
//! short of a CERTIFICATE.
//!
//! THE FIX IS A DERIVATION, NOT A RELAXATION. `¬∃x⃗.φ` classically entails the
//! universal `∀x⃗.¬φ`, and a universal entails every GROUND instance of its
//! body — `∀x⃗.P(x⃗) ⊨ P(t⃗)` — so for ground `t⃗` drawn from the problem's own
//! term set, `¬φ[t⃗]` is a sound consequence of the authored root. Adding those
//! consequences to the authored quantifier-free conjuncts yields a purely
//! GROUND refutation, which the existing consequence-replay stitcher
//! (`authored_consequence_replay`) re-solves on a disposable same-context probe
//! and stitches onto authored-scope derivations:
//!
//! ```text
//! (assume h0 (not E))                        ; E = (exists (x⃗) φ), authored
//! (assume h1 R1) ... (assume hk Rk)          ; authored ground conjuncts
//! (step d0 (cl E F)         :rule qnt_neg_exists)   ; F = (forall (x⃗) (not φ))
//! (step d1 (cl F)           :rule resolution :premises (h0 d0))
//! (step i0 (cl (or (not F) I)) :rule forall_inst :args (t⃗))  ; I = (not φ)[t⃗]
//! (step i1 (cl (not F) I)   :rule or :premises (i0))
//! (step i2 (cl I)           :rule resolution :premises (i1 d1))
//! ... the probe's own strict ground refutation of { R1..Rk, I, ... } ...
//! (step  z (cl))
//! ```
//!
//! WHY THE NAMED BLOCKER DOES NOT BITE. The known obstacle
//! (`forall_ids_in_conjunctive_position` NNF-converts `Not(Exists)` into a
//! FRESHLY BUILT `Forall` whose id is not the authored node, so `refinable` is
//! false for an `Exists` under a `not`) is deliberate and load-bearing — it is
//! what fixed a real wrong-UNSAT. This lane never consults it. It reads the
//! authored root's own structure (`TermData::Not(Exists(..))`), keeps the
//! authored `TermId` as the certificate's `assume`, and mints the dual `F`
//! only as the CONCLUSION of a `qnt_neg_exists` step that the strict checker
//! re-derives from `E` itself. The refinability flag is untouched.
//!
//! NOTHING IS TAKEN ON THE PRODUCER'S WORD. The witness tuple is a pure hint:
//! `validate_forall_inst` re-derives binder/argument arity and sorts, argument
//! groundness w.r.t. the source binders, and the EXACT simultaneous
//! substitution; `validate_qnt_neg_exists` re-derives that `F` is the exact De
//! Morgan dual of `E`; the probe's ground steps are replayed by the outer
//! strict checker over the authored scope. A wrong witness or a non-refuting
//! consequence set can only cost a declined candidate.
//!
//! UNSAT-ONLY. The lane is consulted at exactly one place — the artifact
//! firewall's downgrade — so its only reachable transition is
//! `unknown -> unsat`, and it installs `last_proof` only through the shared
//! consequence-replay installation boundary. Kill switch:
//! `--no-negated-exists-ground-inst` (and the parent `--no-consequence-replay`).

//! CARCARA CANNOT ADJUDICATE THIS LANE'S ARTIFACTS, and the reason is not this
//! lane. Two pre-existing limits, both reproduced on the BASE binary:
//!
//!   1. carcara cannot parse `FloatingPoint` at all — "parser error: sort
//!      'FloatingPoint' is not defined". Control: a 4-line QF_FP unsat that AY
//!      already refutes on the base binary is equally `invalid`. So no FP
//!      artifact from any lane can be checked by it.
//!   2. AY prints the ALPHA-RENAMED binder in the `assume` of a quantified
//!      authored root, and carcara's assume matching is not up to
//!      alpha-equivalence. Measured precisely: `=`-argument reordering IS
//!      tolerated, alpha-renaming is NOT. Reproduced on the base binary via the
//!      already-landed `authored_negated_exists` lane.
//!
//! In a theory carcara DOES parse, this lane's certificate checks `holey`:
//! every `forall_inst`, `or` and `resolution` step VALID, with exactly two
//! holes — `qnt_neg_exists` (an AY-internal rule with no Alethe counterpart)
//! and the probe's theory lemma. No `:rule trust` anywhere; a test asserts it.
//!
//! Fixing (2) is the single change that would take BOTH negated-exists lanes
//! from carcara-`invalid` to carcara-`holey`. It needs authored binder names
//! carried into the printer, which the printer's own docs say it cannot do
//! against an immutable `TermStore`.

use super::authored_consequence_replay::NegatedExistsDual;
use super::*;

/// Authored-scope size beyond which this lane declines.
const MAX_AUTHORED_ROOTS: usize = 64;
/// Negated-existential roots considered per public query.
const MAX_NEGATED_EXISTS_ROOTS: usize = 4;
/// Distinct ground witnesses proposed per binder sort.
const MAX_WITNESSES_PER_SORT: usize = 8;
/// Ground instances added to the probe's consequence set, across all roots.
/// Every instance is one more assertion the bounded probe must bit-blast.
const MAX_GROUND_INSTANCES: usize = 12;
/// Binder count beyond which the tuple enumeration declines outright.
const MAX_BINDERS: usize = 2;
/// Probe attempts this lane may consume per public check-sat.
const MAX_LANE_ATTEMPTS: u8 = 1;
/// Node budget for the binder-name and groundness scans.
const MAX_SCAN_WORK: usize = 20_000;

/// Decline attribution.
///
/// Deliberately `tracing`, not a `--debug-cert` `eprintln!`: the per-check-sat
/// leg attribution this lane feeds is printed once, at the firewall itself
/// (`quantified_semantic_unsat_or_unknown`), so a second stderr channel here
/// would only duplicate it — and every production stderr site is a ratcheted
/// construct in this repository.
fn note(message: impl FnOnce() -> String) {
    tracing::debug!(target: "ay::cert::neg_exists_inst", "{}", message());
}

impl Executor {
    /// Artifact-firewall translation: turn the semantic refutation of a query
    /// whose only quantifier is an authored `(not (exists ...))` into an
    /// authored-scope strict certificate and install it as `last_proof`.
    ///
    /// Returns `true` only when a complete, scope-authorized, strict-checkable
    /// certificate was installed; on `false` the caller keeps the fail-closed
    /// firewall path and every byte of proof state is left as found.
    ///
    /// SOUNDNESS: the installed proof is re-checked from scratch by the
    /// mandatory certification mint (`mint_unsat_certificate` →
    /// `check_strict_unsat_presentation`) before any verdict is published, so a
    /// mis-built certificate can only cost the firewall's `unknown`, never an
    /// unsound `unsat`.
    pub(in crate::executor) fn try_translate_negated_exists_ground_instantiation_unsat(
        &mut self,
    ) -> bool {
        if !crate::quant_unit_authority::negated_exists_ground_inst_enabled() {
            return false;
        }
        let attempts = self.negated_exists_ground_inst_attempts.get();
        if attempts >= MAX_LANE_ATTEMPTS {
            note(|| "decline: lane attempt budget exhausted".into());
            return false;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return false;
        }
        let Some((duals, records)) = self.plan_negated_exists_ground_instances(&authored) else {
            return false;
        };
        self.negated_exists_ground_inst_attempts.set(attempts + 1);
        let installed =
            self.try_translate_authored_consequence_replay_unsat_with_duals(&records, &duals);
        note(|| {
            format!(
                "translate: duals={} instances={} installed={installed}",
                duals.len(),
                records.len()
            )
        });
        installed
    }

    /// Build the dual/instance plan, or `None` when nothing is proposable.
    ///
    /// Every returned record is a HINT. The stitcher and the strict checker
    /// re-derive all of it; this function's only obligations are to stay
    /// bounded and to propose instances that are genuinely quantifier-free.
    fn plan_negated_exists_ground_instances(
        &mut self,
        authored: &[TermId],
    ) -> Option<(
        Vec<NegatedExistsDual>,
        Vec<crate::ematching::ForallInstantiationProvenance>,
    )> {
        let roots = self.exact_authored_negated_exists_roots(authored);
        if roots.is_empty() {
            note(|| "decline: no authored (not (exists ...)) root".into());
            return None;
        }
        // Any binder name bound ANYWHERE in the authored scope disqualifies a
        // witness that mentions it. The strict `forall_inst` validator applies
        // the precise per-source rule; this is the cheap conservative filter
        // that keeps the probe from ever seeing an open term.
        let bound_names = self.authored_binder_names(authored);

        let mut duals: Vec<NegatedExistsDual> = Vec::new();
        let mut records: Vec<crate::ematching::ForallInstantiationProvenance> = Vec::new();
        for (not_exists_root, exists, bindings, body) in
            roots.into_iter().take(MAX_NEGATED_EXISTS_ROOTS)
        {
            if bindings.is_empty()
                || bindings.len() > MAX_BINDERS
                || crate::ematching::contains_quantifier(&self.ctx.terms, body)
            {
                continue;
            }
            // F = (forall x⃗ (not φ)) — the exact dual `validate_qnt_neg_exists`
            // recomputes from E. `mk_not_raw` is required: a folding negation
            // would make the emitted step's conclusion not the dual.
            let negated_body = self.ctx.terms.mk_not_raw(body);
            let forall = self.ctx.terms.mk_forall(bindings.clone(), negated_body);

            let mut per_binder: Vec<Vec<TermId>> = Vec::with_capacity(bindings.len());
            for (_, sort) in &bindings {
                let candidates = self.ground_witnesses_for_sort(authored, sort, &bound_names);
                if candidates.is_empty() {
                    break;
                }
                per_binder.push(candidates);
            }
            if per_binder.len() != bindings.len() {
                note(|| {
                    "decline: a binder sort has no ground witness in the authored scope".into()
                });
                continue;
            }

            let mut minted = 0usize;
            for tuple in bounded_tuples(&per_binder, MAX_GROUND_INSTANCES - records.len()) {
                let mut substitution: ay_core::kani_compat::DetHashMap<String, TermId> =
                    ay_core::kani_compat::DetHashMap::default();
                for ((name, _), &value) in bindings.iter().zip(&tuple) {
                    substitution.insert(name.clone(), value);
                }
                let Some(instance) = crate::ematching::subst_vars_exact_qf(
                    &mut self.ctx.terms,
                    negated_body,
                    &substitution,
                ) else {
                    continue;
                };
                if crate::ematching::contains_quantifier(&self.ctx.terms, instance) {
                    continue;
                }
                records.push(crate::ematching::ForallInstantiationProvenance {
                    quantifier: forall,
                    binding: tuple,
                    instance,
                });
                minted += 1;
                if records.len() >= MAX_GROUND_INSTANCES {
                    break;
                }
            }
            if minted > 0 {
                duals.push(NegatedExistsDual {
                    not_exists_root,
                    exists,
                    forall,
                });
            }
            if records.len() >= MAX_GROUND_INSTANCES {
                break;
            }
        }
        if records.is_empty() {
            note(|| "decline: no ground instance proposable".into());
            return None;
        }
        Some((duals, records))
    }

    /// Ground terms of `sort` occurring anywhere in the authored scope,
    /// EXCLUDING under binders — review measured that `ground_instantiation_candidates` has no `Forall`/`Exists` arm (`_ => {}`), so it never descends and can never return a term containing a `Var`. The `term_avoids_names` filter below is therefore a NO-OP on every input it can receive, kept as a guard against a future arm being added, not as an active filter. Consequence: `+zero` and `16.0`, which occur only inside the existential body, are NEVER proposed as instantiation terms — on this shape every interesting constant
    /// (`+zero`, the bound `16.0`) occurs only inside the existential body —
    /// minus anything mentioning a bound name.
    pub(super) fn ground_witnesses_for_sort(
        &self,
        authored: &[TermId],
        sort: &Sort,
        bound_names: &ay_core::kani_compat::DetHashSet<String>,
    ) -> Vec<TermId> {
        Self::ground_instantiation_candidates(
            &self.ctx.terms,
            authored,
            sort,
            // Over-collect, then filter: the raw scan returns body subterms
            // that mention the binder, which are exactly what must be dropped.
            MAX_WITNESSES_PER_SORT * 8,
        )
        .into_iter()
        .filter(|&candidate| self.term_avoids_names(candidate, bound_names))
        .take(MAX_WITNESSES_PER_SORT)
        .collect()
    }

    /// Every binder name bound by any quantifier reachable from the authored
    /// roots. Bounded; an exhausted scan reports "everything is bound" by
    /// returning `None`-equivalent behaviour through an over-full set is not
    /// possible, so it fails closed by leaving the scan incomplete only after
    /// the work cap, which can at worst admit a candidate the strict
    /// `forall_inst` validator then refuses.
    pub(super) fn authored_binder_names(
        &self,
        authored: &[TermId],
    ) -> ay_core::kani_compat::DetHashSet<String> {
        let mut names = ay_core::kani_compat::DetHashSet::default();
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut stack = authored.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) || seen.len() > MAX_SCAN_WORK {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::Forall(bindings, body, _) | TermData::Exists(bindings, body, _) => {
                    for (name, _) in bindings {
                        names.insert(name.clone());
                    }
                    stack.push(*body);
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                _ => {}
            }
        }
        names
    }

    /// Whether `term` mentions no variable named in `names` and contains no
    /// binder of its own. Conservative: an exhausted scan answers `false`.
    pub(super) fn term_avoids_names(
        &self,
        term: TermId,
        names: &ay_core::kani_compat::DetHashSet<String>,
    ) -> bool {
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut stack = vec![term];
        while let Some(node) = stack.pop() {
            if !seen.insert(node) {
                continue;
            }
            if seen.len() > MAX_SCAN_WORK {
                return false;
            }
            match self.ctx.terms.get(node) {
                TermData::Var(name, _) if names.contains(name) => return false,
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return false,
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                _ => {}
            }
        }
        true
    }
}

/// Deterministic bounded cartesian product of the per-binder candidate lists.
///
/// Diagonal-first: for a multi-binder existential the tuples that repeat one
/// candidate across every position come before the mixed ones, because the
/// diagonal is what closes the shapes this lane exists for. Never yields more
/// than `limit` tuples.
pub(super) fn bounded_tuples(per_binder: &[Vec<TermId>], limit: usize) -> Vec<Vec<TermId>> {
    let mut out: Vec<Vec<TermId>> = Vec::new();
    if per_binder.is_empty() || limit == 0 {
        return out;
    }
    if per_binder.len() == 1 {
        for &candidate in per_binder[0].iter().take(limit) {
            out.push(vec![candidate]);
        }
        return out;
    }
    // Diagonal first.
    for &candidate in &per_binder[0] {
        if out.len() >= limit {
            return out;
        }
        if per_binder.iter().all(|column| column.contains(&candidate)) {
            out.push(vec![candidate; per_binder.len()]);
        }
    }
    // Then the plain product, skipping tuples already emitted.
    let mut indices = vec![0usize; per_binder.len()];
    loop {
        if out.len() >= limit {
            return out;
        }
        let tuple: Vec<TermId> = indices
            .iter()
            .enumerate()
            .map(|(position, &index)| per_binder[position][index])
            .collect();
        if !out.contains(&tuple) {
            out.push(tuple);
        }
        let mut position = per_binder.len();
        loop {
            if position == 0 {
                return out;
            }
            position -= 1;
            indices[position] += 1;
            if indices[position] < per_binder[position].len() {
                break;
            }
            indices[position] = 0;
        }
    }
}

#[cfg(test)]
#[path = "authored_negated_exists_ground_inst_tests.rs"]
mod tests;
