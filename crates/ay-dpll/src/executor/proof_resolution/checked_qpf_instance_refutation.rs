// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trace-free checked refutation for qpf premise-forced instances
//! (#bitblast-original-clause-authority, the P3b "bit-blast UnmappedVariable"
//! class scoped out by L2).
//!
//! The UFBV route's SAT trace carries original bit-blast gate clauses over
//! SAT variables absent from `var_to_term`, so the trace-bound
//! [`super::CheckedSatRefutation`] sidecar can never mint for this family —
//! the failure is at clause TRANSLATION, upstream of every unit-authority
//! channel. This module supplies the missing outer-query authority WITHOUT
//! the trace: for a recorded qpf premise-forced instance it re-derives, at
//! the exact moment of publication,
//!
//! 1. that the refuted `forall` is literally one of the frozen ordered
//!    authored roots of the exact public query (refuting one conjunct of the
//!    authored conjunction refutes the query, under any assumption slice);
//! 2. the `forall_inst` reduction, by strictly replaying the recorded
//!    simultaneous substitution against the live quantifier body
//!    (sort-checked, exact term identity — the same replay the sealed c7
//!    instance-root evidence performs); and
//! 3. the instance refutation itself, through
//!    [`ay_proof::authenticate_uf_leaf_bool_bv_unsat_query`]: an independent
//!    re-lowering of the exact instance into provenance-bearing gate CNF
//!    whose pure-RUP refutation is fully replayed, with ground uninterpreted
//!    applications abstracted as canonical-identity free leaves (sound for
//!    UNSAT: any model of the instance induces a leaf valuation).
//!
//! No producer verdict participates: the record is a pure HINT naming which
//! quantifier/values to try, and all three legs are re-derived from the live
//! term store inside the bounded ay-proof envelope (three-second clamp,
//! node/gate/work caps), clamped further by the caller's solve deadline. No
//! state is minted or retained — the authority is consumed by the caller in
//! the same instant — so nothing can cross a solve boundary. Covered by the
//! #quant-unit-authority kill switch at both the call site and here: with
//! `--no-quant-unit-authority` nothing is recorded upstream AND nothing is
//! consulted, restoring the baseline downgrade byte-for-byte.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{TermData, TermId};

use crate::executor::{Executor, QpfPremiseForcedInstanceRecord};

/// Bounded number of records re-derived per publication. Each attempt is
/// individually clamped by the ay-proof three-second ceiling and the solve
/// deadline; the qpf lane records at most one instance per successful probe,
/// so this cap exists only to bound adversarial record growth.
const MAX_QPF_INSTANCE_REFUTATION_ATTEMPTS: usize = 4;

impl Executor {
    /// Whether one recorded qpf premise-forced instance re-derives a complete
    /// checked refutation of the exact current public query.
    ///
    /// Fail-closed on every leg: missing/stale query scope, an unregistered
    /// quantifier, a substitution that does not replay, or an instance the
    /// bounded Bool/BV+UF-leaf checker cannot refute all decline without
    /// publishing anything.
    pub(in crate::executor) fn checked_qpf_instance_refutation_authorizes_current_query(
        &mut self,
    ) -> bool {
        if !crate::quant_unit_authority::quant_unit_authority_enabled() {
            return false;
        }
        // Exact public query identity: the same scope the trace-bound sidecar
        // binds to (current epoch, bound assumptions, no obligation
        // extension). A missing scope disables this path entirely.
        let Some(roots) = self
            .checked_sat_refutation_query_roots()
            .map(<[TermId]>::to_vec)
        else {
            return false;
        };
        if self.checked_sat_refutation_query_scope().is_none()
            || self.checked_sat_refutation_query_assumptions().is_none()
        {
            return false;
        }
        let records = self.qpf_premise_forced_instance_records.clone();
        for record in records.iter().take(MAX_QPF_INSTANCE_REFUTATION_ATTEMPTS) {
            if self.qpf_instance_refutation_proves(record, &roots) {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    "checked qpf instance refutation MINTED for the exact public query".to_string()
                });
                return true;
            }
        }
        false
    }

    /// Re-derive all three legs for one record against the live term store.
    fn qpf_instance_refutation_proves(
        &mut self,
        record: &QpfPremiseForcedInstanceRecord,
        roots: &[TermId],
    ) -> bool {
        // Leg 1: the quantifier must be an exact frozen authored root.
        if !roots.contains(&record.quantifier) {
            return false;
        }
        // Leg 2: strict `forall_inst` replay — non-empty binders, positional
        // sort agreement, and exact raw-substitution identity.
        let TermData::Forall(bindings, body, _) = self.ctx.terms.get(record.quantifier).clone()
        else {
            return false;
        };
        if bindings.is_empty() || bindings.len() != record.values.len() {
            return false;
        }
        let mut substitution = HashMap::default();
        for ((name, sort), &value) in bindings.iter().zip(&record.values) {
            if self.ctx.terms.sort(value) != sort {
                return false;
            }
            substitution.insert(name.clone(), value);
        }
        let Some(instance) =
            crate::ematching::subst_vars_exact_qf(&mut self.ctx.terms, body, &substitution)
        else {
            return false;
        };
        if instance != record.instance {
            return false;
        }
        // Leg 3: independent whole-instance refutation. The UF-leaf checker
        // re-lowers the exact instance term, re-bit-blasts it with
        // provenance-bearing gates, and replays a complete gate+RUP
        // refutation; a satisfiable abstraction, unsupported operator, or
        // exhausted envelope all DECLINE. The snapshot re-check pins the
        // evidence to the exact live store it was minted from.
        match ay_proof::authenticate_uf_leaf_bool_bv_unsat_query(
            &self.ctx.terms,
            &[record.instance],
            self.current_solve_deadline(),
        ) {
            Ok(evidence) => evidence.is_current_for(&self.ctx.terms, &[record.instance]),
            Err(error) => {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    format!("checked qpf instance refutation unavailable: {error}")
                });
                false
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ay_core::Sort;

    use super::*;

    const FIXPOINT_QUERY: &str = r#"
        (set-logic UFBV)
        (declare-fun fa0 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa1 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa2 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((a0 (_ BitVec 8)) (a1 (_ BitVec 8)) (a2 (_ BitVec 8)))
          (=> (and (= a0 #x01) (= a1 (bvadd a0 #x01)) (= a2 (bvadd a1 #x01)))
              (and (= (fa0 a2 a1 a0) #x01)
                   (= (fa1 a2 a1 a0) (bvadd (fa0 a2 a1 a0) #x01))
                   (= (fa2 a2 a1 a0) (bvadd (fa1 a2 a1 a0) #x01))
                   (or (= a2 (fa0 a2 a1 a0)) (= a2 (fa1 a2 a1 a0)))))))
    "#;

    fn loaded_executor(script: &str) -> Executor {
        let commands = ay_frontend::parse(script).expect("fixture script must parse");
        let mut executor = Executor::new();
        for command in &commands {
            let output = executor
                .execute(command)
                .expect("fixture commands must execute");
            assert!(output.is_none(), "fixture must not contain a query command");
        }
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        executor
    }

    fn solved_fixpoint_executor() -> Executor {
        let mut executor = loaded_executor(FIXPOINT_QUERY);
        let result = executor.check_sat().expect("fixture must solve");
        assert!(
            result.is_unsat(),
            "the qpf lane must decide the fixpoint fixture UNSAT, got {result:?}"
        );
        executor
    }

    /// End-to-end positive: after the qpf lane refutes the fixture, the
    /// recorded instance re-derives a checked refutation of the public query.
    #[test]
    fn recorded_fixpoint_instance_authorizes_the_exact_query() {
        let mut executor = solved_fixpoint_executor();
        assert!(
            !executor.qpf_premise_forced_instance_records.is_empty(),
            "the qpf success site must record its instance"
        );
        assert!(executor.checked_qpf_instance_refutation_authorizes_current_query());
    }

    /// A record whose quantifier is not a frozen authored root must decline
    /// even though its OTHER two legs fully replay: the fabricated record
    /// below carries an exact substitution (leg 2 passes) whose instance
    /// `(= #x02 #x01)` the Bool/BV checker refutes (leg 3 passes), so ONLY
    /// authored-root membership blocks it — deleting the `roots.contains`
    /// guard makes this fail (guard-removal proof for leg 1).
    #[test]
    fn foreign_quantifier_record_never_authorizes() {
        let mut executor = solved_fixpoint_executor();
        let binder_sort = Sort::bitvec(8);
        let bound = executor
            .ctx
            .terms
            .mk_var("qpf_foreign", binder_sort.clone());
        let one = executor.ctx.terms.mk_bitvec(1u8.into(), 8);
        let two = executor.ctx.terms.mk_bitvec(2u8.into(), 8);
        let body = executor.ctx.terms.mk_eq(bound, one);
        let foreign = executor
            .ctx
            .terms
            .mk_forall(vec![("qpf_foreign".to_string(), binder_sort)], body);
        let mut substitution = HashMap::default();
        substitution.insert("qpf_foreign".to_string(), two);
        let instance =
            crate::ematching::subst_vars_exact_qf(&mut executor.ctx.terms, body, &substitution)
                .expect("the foreign instance must substitute exactly");
        executor.qpf_premise_forced_instance_records = vec![QpfPremiseForcedInstanceRecord {
            quantifier: foreign,
            values: vec![two],
            instance,
            asserted: instance,
        }];
        assert!(!executor.checked_qpf_instance_refutation_authorizes_current_query());
    }

    /// A record whose instance is not the exact raw substitution must decline
    /// (guard-removal proof for leg 2).
    #[test]
    fn tampered_instance_record_never_authorizes() {
        let mut executor = solved_fixpoint_executor();
        let record = executor.qpf_premise_forced_instance_records[0].clone();
        let tampered = executor.ctx.terms.false_term();
        executor.qpf_premise_forced_instance_records = vec![QpfPremiseForcedInstanceRecord {
            instance: tampered,
            ..record
        }];
        assert!(!executor.checked_qpf_instance_refutation_authorizes_current_query());
    }

    /// A record whose binder values have the wrong sort must decline
    /// (guard-removal proof for the positional sort check).
    #[test]
    fn wrong_sort_values_record_never_authorizes() {
        let mut executor = solved_fixpoint_executor();
        let record = executor.qpf_premise_forced_instance_records[0].clone();
        let wrong_width = executor.ctx.terms.mk_bitvec(1u8.into(), 16);
        let mut values = record.values.clone();
        values[0] = wrong_width;
        executor.qpf_premise_forced_instance_records =
            vec![QpfPremiseForcedInstanceRecord { values, ..record }];
        assert!(!executor.checked_qpf_instance_refutation_authorizes_current_query());
    }

    /// Without any record nothing is consulted and nothing authorizes.
    #[test]
    fn no_records_never_authorizes() {
        let mut executor = solved_fixpoint_executor();
        executor.qpf_premise_forced_instance_records.clear();
        assert!(!executor.checked_qpf_instance_refutation_authorizes_current_query());
    }

    /// The satisfiable sibling shape (the fixpoint disjunction includes the
    /// reached value) must never mint: the qpf lane refuses to refute it, so
    /// no record exists, and a fabricated record for its universal fails the
    /// UF-leaf refutation leg.
    #[test]
    fn satisfiable_variant_never_authorizes() {
        let script = FIXPOINT_QUERY.replace(
            "(or (= a2 (fa0 a2 a1 a0)) (= a2 (fa1 a2 a1 a0)))",
            "(or (= a2 (fa0 a2 a1 a0)) (= a2 (fa2 a2 a1 a0)))",
        );
        let mut executor = loaded_executor(&script);
        let result = executor.check_sat().expect("sibling must solve");
        assert!(
            !result.is_unsat(),
            "the satisfiable sibling must never be refuted, got {result:?}"
        );
        assert!(!executor.checked_qpf_instance_refutation_authorizes_current_query());
    }
}
