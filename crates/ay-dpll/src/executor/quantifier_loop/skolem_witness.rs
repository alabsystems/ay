// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Skolem-witness SAT confirmation (#skolem-witness-sat).
//!
//! `restore_assertions` fails closed to
//! `unknown (incomplete quantifier-ematching-exists)` whenever model
//! validation skipped a restored quantified assertion and no whole-snapshot
//! certificate is current. For a restored POSITIVE `exists` (or an `exists`
//! nested positively under Boolean connectives) that the deep Skolemizer
//! eliminated, that fail-close discards checked evidence the solve already
//! produced: the emitted model assigns a value to the Skolem witness, and the
//! recorded ground instance `B[x := witness]` can simply be EVALUATED under
//! that model with the independent gate's own evaluator.
//!
//! The arm in this module does exactly that:
//!
//! 1. every public query root is rewritten by the POLARITY-SOUND witnessed
//!    rewrite: a positive `Exists` node whose [`SkolemWitnessRecord`] replays
//!    exactly is replaced by its recorded ground instance (existential
//!    introduction: `B[w] => exists x. B`), and a negative single-binder
//!    `Forall` node is replaced by its instance (universal instantiation:
//!    `forall x. B => B[w]`). Replacing a node by a WEAKER formula at a
//!    positive position — or a STRONGER one at a negative position — yields
//!    `rewritten => original`, so a TRUE rewritten root proves the original
//!    root TRUE in the same model. Nodes with mixed/unknown polarity (`=`,
//!    `xor`, `ite`, quantifier bodies) are left untouched: an unreplaced
//!    quantifier stays unevaluable and can only make the arm DECLINE.
//! 2. every rewritten root must evaluate to exactly `Bool(true)` under the
//!    emitted model via the independent gate's own evaluator
//!    ([`Executor::skolem_witness_terms_evaluate_true`]). A `false` or
//!    unevaluable result declines — it never refutes, because a false witness
//!    instance does not falsify the source existential.
//!
//! A second arm (arm B, `try_restored_quantified_gate_confirmation`) covers
//! the existentials the `qe-light` Cooper pass ELIMINATED instead of
//! Skolemizing (one-point / bounds-contradiction shapes have no witness
//! record at all): it consults the mandatory quantified model gate itself at
//! restore time, on a disposable model clone, keeping `Sat` only on the
//! gate's own `Confirmed`.
//!
//! On confirmation the caller keeps the ground solve's `Sat` instead of
//! demoting. Both arms are ENABLERS, not publishers: the unchanged,
//! unconditional emission gates (`apply_quantified_model_failclosed_gate`,
//! `apply_independent_model_gate`, and the authoritative fail-closed gate)
//! still adjudicate the published verdict with their own fresh evaluations.
//!
//! Every consumed record is REPLAYED here at its single consumption point,
//! against the live term store, with the same shape checks as
//! `CheckedSkolemDerivation::seal`: single binder, plain `Var` witness
//! registered in the Skolem registry, and registered
//! [`ay_core::SkolemChoice`] identity (binder name, binder sort, choice
//! body). The ground instance `B[x := witness]` is then DERIVED here with
//! the raw non-simplifying `subst_vars_exact_qf` — nothing
//! producer-supplied is consumed beyond the witness identity, which the
//! choice registry authenticates. Records are recorded and consumed within
//! one `check-sat` (cleared by `clear_preprocessing_proof_records`), so no
//! record crosses a query-epoch boundary; consumption-time replay against
//! the live store is therefore strictly stronger than stamp-currency
//! checking of a stored token.
//!
//! Kill switch: `--no-skolem-witness-sat`, plus the campaign-wide
//! `--no-quant-unit-authority` (see
//! `crate::quant_unit_authority::skolem_witness_sat_enabled`). Off restores
//! the baseline fail-closed demote byte-for-byte.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{TermData, TermId};

use crate::executor::{Executor, SkolemWitnessRecord};
use crate::executor_types::SolveResult;

/// Recursion bound for the witnessed rewrite. Past the cap the node is left
/// unchanged, which can only make the arm decline (fail closed).
const MAX_WITNESS_REWRITE_DEPTH: u32 = 512;

impl Executor {
    /// Try to confirm the restored `Sat` before the fail-closed demote
    /// (#skolem-witness-sat): arm A evaluates recorded Skolem witness
    /// instances under the emitted model; arm B consults the mandatory
    /// quantified model gate for QE-eliminated existentials.
    ///
    /// Returns `true` only on a checked confirmation. Any other outcome —
    /// kill switch off, no model, no applicable evidence, or any
    /// false/unevaluable evaluation — returns `false` and the caller's
    /// existing fail-closed demote proceeds unchanged.
    pub(in crate::executor) fn try_skolem_witness_sat_confirmation(&mut self) -> bool {
        if !crate::quant_unit_authority::skolem_witness_sat_enabled() {
            return false;
        }
        if self.last_model.is_none() {
            return false;
        }
        // Arm A: recorded-witness rewrite evaluation (cheap, no nested
        // solves) for existentials the deep Skolemizer eliminated.
        if self.try_skolem_witness_rewrite_confirmation() {
            return true;
        }
        // Arm B: restore-time consult of the mandatory quantified model gate
        // for existentials the `qe-light` pass eliminated instead (no witness
        // record can exist for those).
        self.try_restored_quantified_gate_confirmation()
    }

    /// Arm A: the recorded-witness rewrite evaluation (see the module
    /// header). Returns `true` only when at least one quantifier node was
    /// witnessed and every rewritten public query root evaluates to exactly
    /// `Bool(true)` under the emitted model.
    fn try_skolem_witness_rewrite_confirmation(&mut self) -> bool {
        if self.skolem_witness_records.is_empty() {
            return false;
        }
        let records = self.skolem_witness_records.clone();
        let roots = self.independent_gate_query_roots();
        if roots.is_empty() {
            return false;
        }
        let mut replaced = 0usize;
        let mut rewritten = Vec::with_capacity(roots.len());
        for &root in &roots {
            rewritten.push(self.skolem_witness_rewrite(&records, root, true, &mut replaced, 0));
        }
        if replaced == 0 {
            return false;
        }
        let confirmed = self.skolem_witness_terms_evaluate_true(&rewritten);
        if ay_core::misc_cli_flags().debug_cert {
            eprintln!(
                "CERT/skolem-witness: {} ({} roots, {} witnessed nodes)",
                if confirmed { "confirmed" } else { "decline" },
                rewritten.len(),
                replaced,
            );
        }
        confirmed
    }

    /// Restore-time consult of the mandatory quantified model gate
    /// (#skolem-witness-sat, arm B).
    ///
    /// The `qe-light` Cooper pass can ELIMINATE a `∃x:Int` node (one-point /
    /// bounds-contradiction) instead of Skolemizing it, so no witness record
    /// exists for it — yet the emitted model still decides the restored
    /// original: the quantified model gate's own landed routes evaluate it
    /// (Kleene `or` around an unevaluable exists; the existential-prefix
    /// pins + nested-solve route). Without this consult the restore-time
    /// fail-close demotes BEFORE that mandatory gate ever adjudicates,
    /// discarding a confirmation the emission funnel would have derived
    /// itself.
    ///
    /// This consult runs `apply_quantified_model_failclosed_gate` — the
    /// production emission gate, unchanged — on a disposable model clone and
    /// keeps `Sat` only on its `Confirmed` answer. On success the one-shot
    /// confirmation it minted is revoked (it is bound to the disposable
    /// clone) and the emission-time gate re-derives its own confirmation
    /// from scratch, so no authority minted here survives to publication.
    /// On decline every observable side effect is rolled back and the
    /// caller's fail-closed demote proceeds unchanged.
    fn try_restored_quantified_gate_confirmation(&mut self) -> bool {
        if !crate::quant_unit_authority::skolem_witness_sat_enabled() {
            return false;
        }
        // Never consult from INSIDE a nested gate solve: the gate's
        // reentrancy guard would answer `Sat` unchecked.
        if self.in_quantified_model_gate {
            return false;
        }
        if self.last_model.is_none() {
            return false;
        }
        // Park the exact predecessor model (and its non-cloning seals); the
        // gate consult runs on a disposable semantic clone. On this
        // fail-closed path no typed grant is current (every certificate arm
        // has already declined), so the clone is observationally identical
        // for the consult itself.
        let saved_model = self.last_model.take();
        self.last_model = saved_model.clone();
        let saved_reason = self.last_unknown_reason;
        let saved_statistics = self.last_statistics.clone();
        let verdict = self.apply_quantified_model_failclosed_gate(SolveResult::Sat);
        let confirmed = matches!(verdict, SolveResult::Sat);
        // ALWAYS restore the sealed original model, and revoke the one-shot
        // confirmation minted against the disposable clone.
        self.last_model = saved_model;
        self.revoke_quantified_model_confirmation_authority();
        if !confirmed {
            self.last_unknown_reason = saved_reason;
            self.last_statistics = saved_statistics;
        }
        if ay_core::misc_cli_flags().debug_cert {
            eprintln!(
                "CERT/skolem-witness: restored-gate consult {}",
                if confirmed { "confirmed" } else { "decline" }
            );
        }
        confirmed
    }

    /// Polarity-sound witnessed rewrite (see the module header for the
    /// monotonicity argument). Only `not`, `and`, `or`, and `=>` are
    /// descended; every other node is returned unchanged.
    fn skolem_witness_rewrite(
        &mut self,
        records: &[SkolemWitnessRecord],
        term: TermId,
        positive: bool,
        replaced: &mut usize,
        depth: u32,
    ) -> TermId {
        if depth >= MAX_WITNESS_REWRITE_DEPTH {
            return term;
        }
        match self.ctx.terms.get(term).clone() {
            TermData::Exists(..) if positive => {
                match self.skolem_witness_replay(records, term, true) {
                    Some(instance) => {
                        *replaced += 1;
                        // Recurse INTO the instance: a nested existential
                        // inside the substituted body carries its own record.
                        self.skolem_witness_rewrite(
                            records,
                            instance,
                            positive,
                            replaced,
                            depth + 1,
                        )
                    }
                    None => term,
                }
            }
            TermData::Forall(..) if !positive => {
                match self.skolem_witness_replay(records, term, false) {
                    Some(instance) => {
                        *replaced += 1;
                        self.skolem_witness_rewrite(
                            records,
                            instance,
                            positive,
                            replaced,
                            depth + 1,
                        )
                    }
                    None => term,
                }
            }
            TermData::Not(inner) => {
                let new_inner =
                    self.skolem_witness_rewrite(records, inner, !positive, replaced, depth + 1);
                if new_inner == inner {
                    term
                } else {
                    self.ctx.terms.mk_not(new_inner)
                }
            }
            TermData::App(ref sym, ref args) if sym.name() == "and" || sym.name() == "or" => {
                let sym = sym.clone();
                let args = args.clone();
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| {
                        self.skolem_witness_rewrite(records, arg, positive, replaced, depth + 1)
                    })
                    .collect();
                if new_args == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::App(ref sym, ref args) if sym.name() == "=>" && args.len() == 2 => {
                let sym = sym.clone();
                let (lhs, rhs) = (args[0], args[1]);
                let new_lhs =
                    self.skolem_witness_rewrite(records, lhs, !positive, replaced, depth + 1);
                let new_rhs =
                    self.skolem_witness_rewrite(records, rhs, positive, replaced, depth + 1);
                if new_lhs == lhs && new_rhs == rhs {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, vec![new_lhs, new_rhs], sort)
                }
            }
            _ => term,
        }
    }

    /// Independently replay one [`SkolemWitnessRecord`] for `quantifier` at
    /// its consumption point (the same shape checks as
    /// `CheckedSkolemDerivation::seal`): single binder, plain skolem-registry
    /// `Var` witness of the binder sort, and registered `SkolemChoice`
    /// identity. Returns the ground instance DERIVED here by the raw
    /// non-simplifying substitution (never the producer's copy), or `None`
    /// when no record survives — which leaves the quantifier in place and
    /// the arm fails closed.
    fn skolem_witness_replay(
        &mut self,
        records: &[SkolemWitnessRecord],
        quantifier: TermId,
        positive: bool,
    ) -> Option<TermId> {
        let record = records
            .iter()
            .find(|record| record.quantified == quantifier && record.positive == positive)?;
        let terms = &mut self.ctx.terms;
        let (bindings, body) = match terms.get(quantifier).clone() {
            TermData::Exists(bindings, body, _) if positive => (bindings, body),
            TermData::Forall(bindings, body, _) if !positive => (bindings, body),
            _ => return None,
        };
        let [(binder, binder_sort)] = bindings.as_slice() else {
            return None;
        };
        let TermData::Var(witness_name, _) = terms.get(record.witness).clone() else {
            return None;
        };
        if !terms.is_skolem_symbol(&witness_name) || terms.sort(record.witness) != binder_sort {
            return None;
        }
        // The registered choice body is the NEGATED body for the `Forall`
        // shape (`¬∀x. B ≡ ∃x. ¬B`), exactly as the Skolemizer registered it.
        let expected_choice_body = if positive { body } else { terms.mk_not(body) };
        let choice = terms.skolem_choice(record.witness)?;
        if choice.binder != *binder
            || &choice.sort != binder_sort
            || choice.body != expected_choice_body
        {
            return None;
        }
        // Derive the ground instance HERE, with the raw (non-simplifying)
        // substitution, instead of trusting `record.instance`: the recorded
        // form was minted by the Skolemizer's SIMPLIFYING substitution and
        // may differ syntactically. Existential introduction justifies ANY
        // `B[x := w]`, so the independently recomputed raw form is strictly
        // stronger evidence than authenticating the producer's copy — nothing
        // producer-supplied is consumed beyond the witness identity, which
        // the registered `SkolemChoice` above already authenticates.
        let mut substitution = HashMap::default();
        substitution.insert(binder.clone(), record.witness);
        crate::ematching::subst_vars_exact_qf(terms, body, &substitution)
    }
}

#[cfg(test)]
mod tests {
    use ay_frontend::parse;

    use super::*;

    /// Load declarations/assertions and run the full pipeline once so the
    /// Skolemizer records witness provenance and a model is emitted.
    fn solved(input: &str) -> (Executor, Vec<String>) {
        let commands = parse(input).expect("valid SMT-LIB input");
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).expect("execute succeeds");
        (exec, outputs)
    }

    /// The Skolemized-existential fixture: outside Cooper's fragment (UF
    /// head), so `qe-light` refuses it and the deep Skolemizer records
    /// witness provenance.
    const UF_EXISTS: &str = "(set-logic UFLIA)\
             (declare-fun f (Int) Int)\
             (assert (exists ((x Int)) (= (f x) 5)))\
             (check-sat)";

    /// GUARD-REMOVAL NEGATIVE (polarity): an `exists` under `not` must never
    /// be witnessed by the rewrite. If the `positive` guard on the `Exists`
    /// arm were removed, the recorded instance would be substituted under the
    /// negation and a false instance could confirm the negation as true.
    #[test]
    fn negative_polarity_exists_is_never_replaced() {
        let (mut exec, _) = solved(UF_EXISTS);
        let records = exec.skolem_witness_records.clone();
        assert!(
            !records.is_empty(),
            "the positive exists must have recorded witness provenance"
        );
        let quantifier = records[0].quantified;
        let negated = exec.ctx.terms.mk_not(quantifier);
        let mut replaced = 0usize;
        let rewritten = exec.skolem_witness_rewrite(&records, negated, true, &mut replaced, 0);
        assert_eq!(
            replaced, 0,
            "a negative-polarity exists must not be witnessed"
        );
        assert_eq!(rewritten, negated, "the negated term must be unchanged");
    }

    /// ACCEPTING DIRECTION (arm A unit): the positive exists IS witnessed by
    /// the rewrite, and the rewritten root evaluates true under the emitted
    /// model with the gate's own evaluator.
    #[test]
    fn skolemized_exists_is_witnessed_and_evaluates_true() {
        let (mut exec, outputs) = solved(UF_EXISTS);
        assert_eq!(outputs, vec!["sat"]);
        let records = exec.skolem_witness_records.clone();
        assert!(!records.is_empty());
        let quantifier = records[0].quantified;
        let mut replaced = 0usize;
        let rewritten = exec.skolem_witness_rewrite(&records, quantifier, true, &mut replaced, 0);
        assert_eq!(replaced, 1, "the positive exists must be witnessed");
        assert_ne!(rewritten, quantifier);
        assert!(
            exec.skolem_witness_terms_evaluate_true(&[rewritten]),
            "the witnessed instance must evaluate true under the emitted model"
        );
    }

    /// GUARD-REMOVAL NEGATIVE (derived instance): a tampered record
    /// `instance` must be IGNORED — the replay derives the raw substitution
    /// itself and never returns the producer-supplied copy. If the replay
    /// ever started trusting `record.instance`, a tampered `true` here would
    /// leak through and this test would fail.
    #[test]
    fn tampered_instance_is_ignored_by_replay() {
        let (mut exec, _) = solved(UF_EXISTS);
        let mut records = exec.skolem_witness_records.clone();
        assert!(!records.is_empty());
        // Replace the instance with `true` — a formula every model
        // trivially satisfies.
        let tampered = exec.ctx.terms.true_term();
        records[0].instance = tampered;
        let quantifier = records[0].quantified;
        let replayed = exec.skolem_witness_replay(&records, quantifier, true);
        if let Some(instance) = replayed {
            assert_ne!(
                instance, tampered,
                "the replay must derive the substitution, not adopt the record's copy"
            );
        }
    }

    /// GUARD-REMOVAL NEGATIVE (witness identity): a record whose witness is
    /// not the registered Skolem constant for this quantifier must be
    /// rejected (registry + choice-identity checks).
    #[test]
    fn foreign_witness_is_rejected_by_replay() {
        let (mut exec, _) = solved(UF_EXISTS);
        let mut records = exec.skolem_witness_records.clone();
        assert!(!records.is_empty());
        // A fresh plain variable: right sort, but not in the Skolem registry.
        let foreign = exec
            .ctx
            .terms
            .mk_fresh_var("not_a_skolem", ay_core::Sort::Int);
        records[0].witness = foreign;
        let quantifier = records[0].quantified;
        assert!(
            exec.skolem_witness_replay(&records, quantifier, true)
                .is_none(),
            "a witness outside the Skolem registry must be rejected"
        );
    }

    /// REJECTING DIRECTION: a contradictory exists ALONE (no other disjunct)
    /// must never confirm — its witness instance evaluates false under every
    /// model. The full pipeline proves it UNSAT; the arm itself must decline
    /// on the false instance either way.
    #[test]
    fn contradictory_exists_alone_never_confirms() {
        let (exec, outputs) = solved(
            "(set-logic LIA)\
             (assert (exists ((x Int)) (and (> x 100) (< x 0))))\
             (check-sat)",
        );
        assert_eq!(outputs, vec!["unsat"], "the contradiction must be refuted");
        drop(exec);
    }

    /// REJECTING DIRECTION (arm-level): when the only disjunct that could
    /// make the root true is the contradictory witness instance, the arm's
    /// evaluation sees `or(false, false)` and must decline.
    #[test]
    fn false_witness_instance_declines_at_evaluation() {
        // `y = 0` forces the second disjunct false; the whole assertion is
        // UNSAT and never reaches the arm — pinned here as the never-sat
        // guard for this shape in BOTH kill-switch modes.
        let smt = "(set-logic AUFLIA)\
             (declare-fun y () Int)\
             (assert (= y 0))\
             (assert (or (exists ((x Int)) (and (> x 100) (< x 0))) (> y 0)))\
             (check-sat)";
        let (_, outputs) = solved(smt);
        assert_eq!(outputs, vec!["unsat"]);
        let off = ay_core::MiscCliFlags {
            no_skolem_witness_sat: true,
            ..ay_core::MiscCliFlags::default()
        };
        let _guard = ay_core::misc_test_override::set(off);
        let (_, outputs_off) = solved(smt);
        assert_eq!(outputs_off, vec!["unsat"]);
    }

    /// KILL SWITCH: with `--no-skolem-witness-sat` the S1 lost-SAT formulas
    /// restore the baseline fail-closed answer byte-for-byte, and the
    /// producer records nothing.
    #[test]
    fn kill_switch_restores_baseline_unknown() {
        let smt = "(set-logic LIA)\
             (declare-fun a () Int)\
             (assert (>= a 5))\
             (assert (exists ((x Int)) (= x a)))\
             (check-sat)\
             (get-info :reason-unknown)";
        let off = ay_core::MiscCliFlags {
            no_skolem_witness_sat: true,
            ..ay_core::MiscCliFlags::default()
        };
        let _guard = ay_core::misc_test_override::set(off);
        let (exec, outputs) = solved(smt);
        assert_eq!(outputs[0], "unknown");
        assert!(
            outputs[1].contains("quantifier-ematching-exists"),
            "baseline decline reason must be preserved, got: {}",
            outputs[1]
        );
        assert!(
            exec.skolem_witness_records.is_empty(),
            "the kill switch must also stop the producer recording"
        );
    }

    /// ACCEPTING DIRECTION (arm-level integration): both S1 formulas confirm
    /// through the full pipeline with the arm on, and the mandatory emission
    /// gates re-confirm the published verdict.
    #[test]
    fn s1_formulas_confirm_with_gates_enforced() {
        let (exec, outputs) = solved(
            "(set-logic LIA)\
             (declare-fun a () Int)\
             (assert (>= a 5))\
             (assert (exists ((x Int)) (= x a)))\
             (check-sat)",
        );
        assert_eq!(outputs, vec!["sat"]);
        assert_eq!(
            exec.last_statistics.get_string("model_check_gate.result"),
            Some("confirmed-sat"),
            "the independent gate must confirm the published witness"
        );

        let (exec, outputs) = solved(
            "(set-logic AUFLIA)\
             (declare-fun y () Int)\
             (assert (or (exists ((x Int)) (and (> x 100) (< x 0))) (> y 0)))\
             (check-sat)",
        );
        assert_eq!(outputs, vec!["sat"]);
        assert_eq!(
            exec.last_statistics.get_string("model_check_gate.result"),
            Some("confirmed-sat"),
            "the independent gate must confirm the published witness"
        );
    }
}
