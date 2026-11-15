// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-authored Bool/BV refutation: an independently replayed bit-blast
//! theorem, or a natively checked modular affine identity, resolved against
//! exact authored roots.

use super::*;
use crate::executor::model::NativeBvRefutationScope;
use ay_frontend::NativeAssertionSurfaces;

pub(in crate::executor::proof) mod control;
mod native;
#[cfg(test)]
mod tests;

impl Executor {
    /// Replace a non-strict provisional BV refutation with a complete,
    /// independently replayed Bool/BV refutation of the exact authored roots.
    ///
    /// The checker first proves the clause `¬A1 ∨ ... ∨ ¬An` with its bounded
    /// bit-blast/LRAT producer. Exact `Assume(Ai)` leaves then resolve that
    /// theorem to the empty clause. Unsupported roots, too many roots, SAT
    /// authored conjunctions, resource exhaustion, or any whole-proof replay
    /// failure leave the original trust-bearing proof untouched.
    ///
    /// A unit clause that is an exact modular affine identity is proved by the
    /// native arithmetic checker instead: elaboration's shift/add rewrite of
    /// constant multipliers turns `(not (= a b))` over sums of scaled operands
    /// into exactly such an identity, and reassociated 64-bit adder networks
    /// are out of the bit-blast producer's reach — it spends its whole
    /// three-second deadline and declines, and every later certification lane
    /// then repeats that attempt. With no proof document to print, the wire
    /// spelling is moot and the algebraic theorem goes first; a session that
    /// prints proofs keeps the bit-blast first (its checked circuits print
    /// where a native-only identity is a hole) and falls back to the identity.
    pub(super) fn replace_with_exact_authored_bv_refutation(&mut self, proof: &mut Proof) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        if let Some(candidate) = self.exact_authored_bv_refutation(|_, _| true) {
            *proof = candidate;
        }
    }

    /// The concrete-root source of `repair_wire_gap_with_authored_root_refutation`:
    /// replace a native-strict proof whose document carries an unproved step
    /// with this lane's refutation, when that refutation prints without one
    /// (`wire_repair_candidate_prints_clean`).
    ///
    /// The guarded collapse at the head of the cascade repairs a rejected
    /// incumbent of an observed document with one `BvBitBlast` lemma over the
    /// conjunction of the raw authored roots. Its clause keeps every authored
    /// array read, which no checked Alethe lowering spells, so it prints as
    /// `hole`; and because it is native-strict, every later cascade member
    /// returns before trying. This lane's lemma is over the concrete authored
    /// roots, where elaboration has already folded the read, and prints as a
    /// complete blast. Measured under `--strict-proofs` on `(= x #x00000000)`
    /// and `(bvugt (select (store a #x00 (bvmul x y)) #x00) #x00000000)` with
    /// `a : (Array (_ BitVec i) (_ BitVec 32))`: at 1c4ed9d77, where the strict
    /// checker could not bit-blast the read for `i` = 7 or 8, the collapse was
    /// refused and this lane's refutation published trust-free; for `i` = 4,
    /// 9, 16 and 32 the collapse was installed and the answer was `unknown
    /// (incomplete proof-trusted)`, and `i` = 7 and 8 joined them as soon as
    /// the checker could bit-blast those reads too.
    ///
    /// The known-wire-gap screen alone would refuse exactly these candidates:
    /// it reports every multi-literal bit-blast lemma as a gap on purpose, so
    /// the shared admission rule asks an observable document for its render.
    pub(super) fn repair_wire_gap_with_exact_authored_bv_refutation(&mut self, proof: &mut Proof) {
        if let Some(candidate) = self.exact_authored_bv_refutation(|executor, candidate| {
            executor.wire_repair_candidate_prints_clean(candidate)
        }) {
            *proof = candidate;
        }
    }

    /// Build the exact authored Bool/BV refutation. `admit` is deny-only
    /// presentation advice, asked about each actual proposed lemma kind BEFORE
    /// its semantic producer. It cannot authorize a theorem: exact recognition,
    /// authored-scope validation and the whole strict replay remain mandatory.
    fn exact_authored_bv_refutation(
        &mut self,
        admit: impl Fn(&Self, &Proof) -> bool,
    ) -> Option<Proof> {
        let control = control::Continuation::capture(self);
        let _scope = control.enter();
        let source_kind = self.native_bv_source_kind(&|| control.stopped());
        // Only identified native input uses the new authenticated scope.
        // Genuine/mixed/retention-off Other keeps the old deduplicated source
        // path, whose <=64 cap applies to distinct roots rather than raw rows.
        let canonical_input = source_kind == Some(NativeAssertionSurfaces::Native);
        let native = if !control.stopped() && canonical_input {
            NativeBvRefutationScope::capture(self).filter(|scope| {
                !self
                    .evaluation_attempt()
                    .native_bv_refutation_attempted(scope)
            })
        } else {
            None
        };
        let authored = if control.stopped()
            || !matches!(
                source_kind,
                Some(NativeAssertionSurfaces::Native | NativeAssertionSurfaces::Other)
            ) {
            Vec::new()
        } else if canonical_input {
            native
                .as_ref()
                .map(|scope| scope.roots().to_vec())
                .unwrap_or_default()
        } else {
            self.exact_concrete_authored_scope()
        };
        let candidate = self
            .exact_bv_candidate_with_control(&authored, admit, &control)
            .filter(|_| {
                native.as_ref().is_none_or(|scope| {
                    NativeBvRefutationScope::capture(self)
                        .is_some_and(|current| current.matches(scope))
                        && self.native_bv_source_kind(&|| control.stopped()) == source_kind
                })
            });
        let stopped = control.stopped();
        // Retain the observed stop at the existing publication boundary too.
        // The shared evaluation attempt already holds it if a callback unwinds.
        if let Some(reason) = control.reason() {
            self.note_certification_stop(reason);
        }
        if stopped {
            None
        } else {
            candidate
        }
    }

    fn exact_bv_candidate_with_control(
        &mut self,
        authored: &[TermId],
        admit: impl Fn(&Self, &Proof) -> bool,
        control: &control::Continuation,
    ) -> Option<Proof> {
        const MAX_AUTHORED_ROOTS: usize = 64;
        if control.stopped() {
            return None;
        }
        if authored.is_empty()
            || authored.len() > MAX_AUTHORED_ROOTS
            || authored
                .iter()
                .any(|&term| !matches!(self.ctx.terms.sort(term), Sort::Bool))
        {
            return None;
        }

        let mut exact_roots = Vec::with_capacity(authored.len());
        let mut opposites = Vec::with_capacity(authored.len());
        for &assertion in authored {
            let opposite = match self.ctx.terms.get(assertion).clone() {
                TermData::Not(inner) => inner,
                _ => self.ctx.terms.mk_not_raw(assertion),
            };
            // Resolution removes one complementary literal per assumption.
            // Distinct authored syntax can normalize to the same opposite;
            // retain the first exact root only so one resolution removes one
            // occurrence and the final residual is structurally honest.
            if opposites.contains(&opposite) {
                continue;
            }
            exact_roots.push(assertion);
            opposites.push(opposite);
        }
        let affine = ay_proof::recognize_native_bv_affine_identity(&self.ctx.terms, &opposites);
        if control.stopped() {
            return None;
        }
        if !affine || self.is_producing_proofs() {
            let candidate = exact_candidate(&exact_roots, &opposites, TheoryLemmaKind::BvBitBlast);
            // The concrete wire-gap fallback formerly paid the exact native
            // producer even when the following render necessarily declined.
            // Mirror the raw-authored fallback: reject that search first.
            let offered = admit(self, &candidate);
            if control.stopped() {
                return None;
            }
            if offered && {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    format!(
                        "exact authored BV: bitblast probe roots={} literals={}",
                        exact_roots.len(),
                        opposites.len()
                    )
                });
                self.recognize_bv_bitblast_until_stopped(&opposites)
            } {
                return self.finish_exact_bv_candidate(candidate, authored, control);
            }
            if control.stopped() {
                return None;
            }
        }
        if !affine {
            return None;
        }
        // A BV wire refusal says nothing about the arithmetic spelling.
        // Offer its actual kind independently; neither denial is authority.
        let candidate = exact_candidate(
            &exact_roots,
            &opposites,
            TheoryLemmaKind::ArithClauseTautology,
        );
        let offered = admit(self, &candidate);
        if control.stopped() || !offered {
            return None;
        }
        self.finish_exact_bv_candidate(candidate, authored, control)
    }

    fn finish_exact_bv_candidate(
        &self,
        candidate: Proof,
        authored: &[TermId],
        control: &control::Continuation,
    ) -> Option<Proof> {
        (!control.stopped()
            && ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, authored).is_ok()
            && Self::proof_derives_empty_clause(&candidate)
            && self
                .check_proof_strict_with_datatypes(&candidate)
                .is_ok_and(|quality| quality.is_complete())
            && !control.stopped())
        .then_some(candidate)
    }
}

/// Preserve the existing exact assumes, clause order and resolution spelling.
fn exact_candidate(roots: &[TermId], opposites: &[TermId], kind: TheoryLemmaKind) -> Proof {
    let mut candidate = Proof::new();
    let assumptions: Vec<ProofId> = roots
        .iter()
        .enumerate()
        .map(|(index, &root)| candidate.add_assume(root, Some(format!("authored_bv_{index}"))))
        .collect();
    let mut current = candidate.add_theory_lemma_with_kind("bv", opposites.to_vec(), kind);
    let mut residual = opposites.to_vec();
    for (&assumption, &opposite) in assumptions.iter().zip(opposites) {
        residual.retain(|&literal| literal != opposite);
        current = candidate.add_rule_step(
            AletheRule::ThResolution,
            residual.clone(),
            vec![current, assumption],
            Vec::new(),
        );
    }
    candidate
}
