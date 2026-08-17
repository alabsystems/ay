// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordered arithmetic proof-reconstruction fallbacks.

use ay_core::Proof;

use super::super::Executor;

impl Executor {
    pub(super) fn run_arithmetic_reconstruction_fallbacks(&mut self, proof: &mut Proof) {
        // Genuine Farkas reconstruction for a relaxation-encoded LIA/LRA UNSAT
        // (MaxSMT / optimization feasibility probes) that collapsed to a
        // whole-problem `trust` step. The checked isolated probe injects its
        // assertion vector as raw TermIds (no parsed-command provenance, no SAT
        // trace), so the forced-theory-literal conflict behind the relaxation
        // clauses cannot be rebuilt by any source-provenance cascade. This runs
        // BEFORE the internal `BvLiaTautology` fallback because it emits an
        // `la_generic`-printable certificate (carcara-checkable), superior to
        // that fallback's Alethe hole. Guarded to touch only a non-strict proof
        // and to accept only after an independent strict re-check; fail-closed.
        self.rebuild_relaxation_forced_arith_farkas(proof);

        // Genuine Farkas reconstruction for a formula-level arithmetic-ITE UNSAT
        // (`(ite c (= I a) (= I b))` over linear bounds with a nonnegativity /
        // successor contradiction) whose exported proof collapsed onto `trust`
        // leaves. Preprocessing substitutes the derived variables away, so the
        // ITE tautology, the derived ITE fact, and the fused theory conflict all
        // land as `trust` steps that no authored / provenance-surgery cascade
        // can rebuild. This pass reseeds the ITE's genuine `ite1`/`ite2`
        // implication clauses (plus the linear bounds/contradiction) directly
        // from the authorized assertions and lets the bounded DPLL(T) closer
        // case-split the condition and Farkas-certify each branch. Guarded to
        // touch only a trust-bearing proof and to accept only after an
        // independent strict re-check; fail-closed.
        self.rebuild_arith_ite_case_split_farkas(proof);

        // TRUE last resort: the internal-certificate BV/LIA fallback
        // (`BvLiaTautology`, replayed by AY's bounded source interpreter). It
        // must run AFTER the authored replacement cascade above: the cascade's
        // `replace_with_exact_authored_bv_refutation` emits a real, externally
        // surfaceable `bv_bitblast` certificate, while this fallback's
        // `BvLiaTautology` renders as an honest `hole` on the Alethe wire.
        // When it ran earlier in publication it claimed pure QF_BV refutations
        // the cascade could certify externally, silently downgrading the
        // artifact (see `rebuild_trust_leaf_proof_from_original_assertions`).
        // A proof that is already strict-complete over the authored scope is
        // preserved byte-identically; everything else is replaced only after
        // the candidate's premise scope and every step replay strictly.
        self.rebuild_authenticated_bv_lia_internal_certificate_last_resort(proof);
    }
}
