// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The early attempt for a pure bit-vector query, and the lane's
//! `--probe-cert-reject` notes.

use super::*;

/// `--probe-cert-reject` note naming what the raw ground closure decided.
pub(super) fn closure_note(message: impl FnOnce() -> String) {
    crate::executor::unsat_cert::probe_cert_reject(|| format!("raw ground closure: {}", message()));
}

impl Executor {
    /// The early attempt for a PURE bit-vector query (every raw root
    /// Bool/BitVec-sorted throughout, no binder); returns whether it
    /// committed. It runs just before the replacement cascade and before the
    /// bit-blast collapse rescue of a degenerate one-`trust` proof.
    ///
    /// The cascade's first member, the guarded collapse, the bit-blast
    /// members after it and the collapse rescue re-derive such a refutation
    /// as ONE bit-level lemma over the whole root. That is complete, but its
    /// cost follows the circuit: on external-codegen's x86-64 body theorems a 32-bit
    /// `imul` against its zero-extended register lowering kept the guarded
    /// collapse's proof-producing bit-blast busy until the query's 30 s timeout
    /// (census `101fca904a102615`, sampled on 57ea58ca3), and the queries it
    /// did certify shipped 3 to 15 MB documents in up to 26 s. The ground
    /// closure decides the same roots by congruence and slice identities in
    /// a bounded number of polynomial rounds and declines fast, so it goes
    /// first; a decline leaves `proof` exactly as it was for the members
    /// that follow. Nothing is admitted on this path that the lane's usual
    /// gates (strict replay, empty clause, wire screen) would not admit.
    pub(in crate::executor::proof) fn try_pure_bit_vector_ground_closure_first(
        &mut self,
        proof: &mut Proof,
    ) -> bool {
        let Some(roots) = self.ground_closure_roots() else {
            closure_note(|| "cascade head: no raw roots".to_string());
            return false;
        };
        if !self.roots_are_pure_bit_vector(&roots) {
            closure_note(|| "cascade head: not a pure bit-vector query".to_string());
            return false;
        }
        if !false_source::rests_on_unattributed_false(self, proof)
            && self.authored_cascade_publishable(proof)
        {
            closure_note(|| "cascade head: the incumbent is publishable".to_string());
            return false;
        }
        self.rebuild_raw_ground_closure_from(proof, &roots)
    }

    /// Whether [`Self::try_pure_bit_vector_ground_closure_first`] passes its
    /// two gates that do not read the incumbent: the query has raw roots and
    /// every one is a pure bit-vector root. Asked without a note, by the
    /// guarded collapse that would otherwise run ahead of the closure
    /// (`bv_identity_promotion/guarded/before_promotion.rs`).
    pub(in crate::executor::proof) fn pure_bit_vector_ground_closure_applies(&mut self) -> bool {
        self.ground_closure_roots()
            .is_some_and(|roots| self.roots_are_pure_bit_vector(&roots))
    }

    /// Whether every elaborated hard assertion is a pure bit-vector root, read
    /// off the terms the session already holds. Unlike
    /// [`Self::pure_bit_vector_ground_closure_applies`] it interns nothing:
    /// the closure's roots are raw re-interns of the parsed assertions, and
    /// minting them ahead of the passes that run before the cascade head
    /// renumbers every term those passes and the session's later checks
    /// mint. Asked before the early attempt that precedes the Generic
    /// promotion, so a query that is not pure bit-vector leaves that pass
    /// exactly as it found the term store.
    pub(in crate::executor::proof) fn elaborated_assertions_are_pure_bit_vector(&self) -> bool {
        self.ctx
            .assertions
            .iter()
            .all(|&assertion| self.is_pure_bit_vector_ground_root(assertion))
    }

    fn roots_are_pure_bit_vector(&self, roots: &GroundRoots) -> bool {
        roots
            .search
            .iter()
            .all(|&root| self.is_pure_bit_vector_ground_root(root))
    }

    /// Whether every node below `root` is Bool- or BitVec-sorted and no
    /// binder occurs, within a bounded walk (a larger root is not pure).
    pub(in crate::executor::proof) fn is_pure_bit_vector_ground_root(&self, root: TermId) -> bool {
        const MAX_PURITY_NODES: usize = 1 << 16;
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut pending = vec![root];
        while let Some(term) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_PURITY_NODES
                || !matches!(self.ctx.terms.sort(term), Sort::Bool | Sort::BitVec(_))
            {
                return false;
            }
            match self.ctx.terms.get(term) {
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return false,
                TermData::App(_, args) => pending.extend(args.iter().copied()),
                TermData::Not(inner) => pending.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    pending.extend([*condition, *then_term, *else_term]);
                }
                _ => {}
            }
        }
        true
    }
}
