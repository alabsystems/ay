// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! UNSAT proof orchestration and API; checking, synthesis, resolution, and rewriting live in focused siblings.

mod authored_array_row1;
mod authored_array_row_value;
mod authored_bv_lia_refutation;
mod authored_cascade;
mod authored_collection_subset;
mod authored_congruence;
mod authored_conjunct_eval;
mod authored_consequence_replay;
mod authored_datatype;
mod authored_divisibility;
mod authored_equality_closure;
mod authored_forall;
mod authored_forall_inst_conflict;
mod authored_forall_inst_equality;
mod authored_forall_substitution;
mod authored_forall_witness;
mod authored_guarded_linear;
mod authored_helpers;
mod authored_linear;
mod authored_negated_exists;
mod authored_nested_forall;
mod authored_nested_forall_search;
mod authored_store_permutation;
mod authored_string_length;
mod authored_string_word_identity;
mod bv_bitblast_collapse;
mod bvand_commutative_congruence;
mod check;
mod collection_axiom_promotion;
mod contextual_array_row2;
mod decline;
mod double_negation;
mod emission_budget;
mod eq_transitive_surface;
mod exact_array_row2;
mod extensionality_surface;
mod false_source;
mod finite_enum;
mod finite_enum_surface;
#[cfg(test)]
mod finite_enum_tests;
mod generic_promotion;
mod lane_policy;
mod lifecycle;
mod reconstruction_fallbacks;
mod surface_bv_rebuild;
mod terminal_trust;

use authored_cascade::RepairEntry;
use authored_helpers::{
    collect_select_terms_local, pair_other_side_local, DerivedUnit, GroundBinding,
    StringLengthFactProvenance, StringRelevantSubterms,
};
use ay_core::term::{Constant, TermData};
use ay_core::{
    AletheRule, FarkasAnnotation, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore,
    TheoryLemmaKind, TheoryLit,
};
use ay_frontend::command::{
    Constant as FrontendConstant, Index as FrontendIndex, Term as FrontendTerm,
};
use ay_frontend::{Command, CommandResult, OptionValue};
#[cfg(not(feature = "proof-checker"))]
use ay_proof::{check_proof_partial, PartialProofCheck};
use ay_proof::{export_alethe_with_problem_scope_and_overrides, AlethePrintError};
use bvand_commutative_congruence::add_bvand_commutative_congruence_proof;
pub use decline::ProofDeclineMechanism;
use emission_budget::DEFAULT_ALETHE_EMISSION_WORK_BUDGET;
use num_bigint::BigInt;
use surface_bv_rebuild::{
    build_bv_atom_pterm, build_bv_const, build_bv_pterm, build_qfbv_ite_pterm,
    build_qfbv_select_pterm, match_and_self_eq_contradiction, match_and_true_eq_contradiction,
    match_eq_negation, parse_rendered_assertion,
};

use crate::executor_types::SolveResult;

use super::Executor;
pub(in crate::executor) use finite_enum::CheckedFiniteEnumPigeonholeProof;
use finite_enum::MAX_RENDER_WORK as MAX_FINITE_ENUM_RENDER_WORK;

impl Executor {
    /// Build a proof for UNSAT result
    ///
    /// Creates an Alethe-compatible proof with assumptions for each assertion
    /// and a final step deriving the empty clause.
    pub(super) fn build_unsat_proof(&mut self) {
        // A checked SAT sidecar authorizes one immutable trace/mapping/query bundle.
        // Retire any prior candidate before inspecting it, including on suppressed exits.
        //
        // ...but ONLY when there IS a current bundle to inspect
        // (#checked-sat-sidecar-second-call). This method is NOT idempotent: it `take()`s
        // `last_clause_trace`, `last_var_to_term`, and `last_negations`, so a second call on the same
        // query arrives with the trace already consumed. Retiring
        // unconditionally then destroyed the sidecar the FIRST call had
        // correctly minted and could not re-mint it, and the certification
        // funnel fell through to the Alethe presentation, which on the DT
        // lanes is a `Generic` trust stub that strict mode rejects. Measured on
        // QF_DT `vlsat3_b83`: "no SAT clause trace is available" printed TWICE,
        // and a correct `unsat` published as `unknown`.
        //
        // Keeping it is not weaker. The sidecar carries its own authority and
        // is checked at USE by `is_current_for` against the query epoch, the
        // frontend source stamp, the ordered roots and the ordered assumption
        // slice, so a sidecar that no longer denotes this query is rejected
        // there regardless of what happens here.
        if self.last_clause_trace.is_some() {
            self.last_checked_sat_refutation = None;
        }
        if self.last_unsat_proof_reconstruction_suppressed {
            self.clear_finite_enum_proof_state();
            return;
        }
        // `build_unsat_proof` consumes its generic SAT trace, so callers may
        // invoke it twice for one query. Preserve an already checked bounded
        // proof only when the sealed capability still authenticates the exact
        // stored canonical proof.
        if self.current_checked_finite_enum_proof().is_some() {
            return;
        }
        self.last_checked_finite_enum_pigeonhole = None;
        // The sealed path is an exception only to the existing oversized-
        // source poison. Bounded queries retain the ordinary reconstruction
        // path (including its broader accepted finite-enum source shapes).
        if let Some(mechanism) = self.proof_source_decline() {
            if self.last_finite_enum_pigeonhole.is_some()
                && self.try_install_bounded_finite_enum_pigeonhole_proof()
            {
                return;
            }
            self.install_uncertifiable_proof_poison(mechanism);
            return;
        }
        if self.last_clause_trace.is_some() {
            self.refresh_checked_sat_refutation();
        }
        let mut proof = if self.proof_tracker.num_steps() > 0 {
            let mut tracker_proof = self.proof_tracker.take_proof();
            // (#7913 Phase C) When LIA preprocessing substituted variables,
            // the tracker's Assume terms may be degenerate (e.g. `true`,
            // `false`) rather than the original user assertions. This happens
            // when VariableSubstitution replaces `(= x 3)` -> `(= 3 3)` ->
            // `true`, making the SAT solver see trivial constants instead of
            // the original equality atoms. Detect this by checking if ALL
            // assume terms are boolean constants, and if so replace them with
            // the original problem assertions.
            let true_id = self.ctx.terms.true_term();
            let false_id = self.ctx.terms.false_term();
            let assume_terms: Vec<TermId> = tracker_proof
                .steps
                .iter()
                .filter_map(|s| match s {
                    ProofStep::Assume(t) => Some(*t),
                    _ => None,
                })
                .collect();
            let all_degenerate = !assume_terms.is_empty()
                && assume_terms.iter().all(|t| *t == true_id || *t == false_id);
            if all_degenerate {
                let original_assertions = self.proof_original_problem_assertions();
                if !original_assertions.is_empty() {
                    let non_assume_steps: Vec<_> = tracker_proof
                        .steps
                        .into_iter()
                        .filter(|s| !matches!(s, ProofStep::Assume(_)))
                        .collect();
                    tracker_proof = Proof::new();
                    for (idx, assertion) in original_assertions.into_iter().enumerate() {
                        tracker_proof.add_assume(assertion, Some(format!("h{idx}")));
                    }
                    for step in non_assume_steps {
                        tracker_proof.add_step(step);
                    }
                }
            }
            tracker_proof
        } else {
            let mut proof = Proof::new();
            let problem_assertions = self.proof_problem_assertions();
            let mut assertions = if problem_assertions.is_empty() {
                self.proof_original_problem_assertions()
            } else {
                problem_assertions
            };
            // (#h10/b22) check-sat-assuming holds the assumptions in
            // `last_assumptions`, not in `ctx.assertions`. When the UNSAT verdict
            // comes from a trivial fold of contradictory assumptions (e.g. two
            // `(= x ..)` BV equalities) the SAT solver records no clause-level
            // conflict, so the proof reconstructs with no Assume leaves at all and
            // every empty-clause strategy fails, yielding an empty proof. Seed the
            // assumptions as Assume steps so the contradictory-assumption /
            // trust-lemma fallbacks can close the proof.
            if let Some(assumptions) = self.last_assumptions.clone() {
                for assumption in assumptions {
                    if !assertions.contains(&assumption) {
                        assertions.push(assumption);
                    }
                }
            }
            for (idx, assertion) in assertions.into_iter().enumerate() {
                proof.add_assume(assertion, Some(format!("h{idx}")));
            }
            proof
        };

        // Capture the SAT-level LRAT bytes before SAT proof reconstruction
        // consumes `last_clause_trace`. This is best-effort: traces with
        // truncation or non-contiguous original clause IDs do not export a
        // standalone LRAT certificate.
        self.last_lrat_certificate = self
            .last_clause_trace
            .as_ref()
            .and_then(clause_trace_to_lrat_bytes);

        // Decompose single Generic/trust theory lemmas for combined real
        // conflicts into EUF + arithmetic bridge pairs (#6756 Packet 2).
        // Must run BEFORE ensure_empty_clause_derivation so the two-lemma
        // closer (Packet 3) can find both lemmas.
        Self::decompose_combined_real_conflict_lemmas(&mut self.ctx.terms, &mut proof);

        // Build initial empty clause derivation (pre-rewrite).
        self.ensure_empty_clause_derivation(&mut proof);

        let hidden_equality_assertions = self.collect_hidden_problem_equality_assertions();

        // Reconstruct missing Farkas coefficients for arithmetic theory lemmas
        // (#6757). Must run AFTER ensure_empty_clause_derivation (which may
        // create new TheoryLemma steps via SAT resolution reconstruction) but
        // BEFORE apply_input_syntax_rewrites_to_proof (which can simplify
        // linking equalities like `(= (select a 0) x)` to `true`, destroying
        // the constraint that makes the conjunction infeasible for Farkas).
        self.reconstruct_missing_farkas_and_demote(&mut proof, &hidden_equality_assertions);

        if !crate::executor::proof_resolution::proof_structure_is_well_formed(&proof) {
            tracing::warn!("proof contains dangling premise IDs before rewrite");
        }
        self.apply_input_syntax_rewrites_to_proof(&mut proof);

        // Rewriting changes arithmetic rows and can merge literals. Transport
        // preserves a positional certificate only when rebinding plus exact
        // replay succeeds; this whole-proof sanitation is the final authority
        // boundary for any annotation created outside that chokepoint. Clear
        // and demote stale certificates before attempting reconstruction on the
        // final syntax (#6757).
        self.sanitize_rewritten_farkas_and_demote(&mut proof);

        // Post-rewrite promotion (#6756): theory lemmas that were classified as
        // Generic before surface-syntax rewrites may now have clause terms that
        // match a more specific kind (e.g., LIA integer equality after array
        // select/store rewriting). Re-infer the kind from the rewritten clause.
        // #trust->0 C3: supply the datatype registries so DT shapes promote too.
        let c3_dt_data = crate::theory_inference::dt_funnel_registry_data(&self.ctx);
        let c3_dt = c3_dt_data
            .as_ref()
            .map(crate::theory_inference::DatatypeRegistries::from_data);
        Self::promote_generic_theory_lemma_kinds_after_rewrite(
            &self.ctx.terms,
            &mut proof,
            c3_dt.as_ref(),
        );
        // Post-rewrite Farkas for lemmas just promoted from Generic (#6756).
        // Note: may fail for combined-theory clauses where rewriting simplified
        // linking equalities; the pre-rewrite pass above is primary.
        self.reconstruct_missing_farkas_and_demote(&mut proof, &hidden_equality_assertions);

        // Term rewriting can merge distinct auxiliary variables into the same
        // surface term, invalidating pre-rewrite resolution chains. Strip
        // stale resolution steps and rebuild from the rewritten proof.
        if !Self::proof_derives_valid_empty_clause(&self.ctx.terms, &proof) {
            crate::executor::proof_resolution::strip_resolution_steps(&mut proof);
            self.ensure_empty_clause_derivation(&mut proof);
            // Reconstruct Farkas for any trust lemmas created by rebuild (#6757).
            self.reconstruct_missing_farkas_and_demote(&mut proof, &hidden_equality_assertions);
        }

        // More than one subsystem may close the same solve. In particular, a
        // quantified-instance producer can derive an authored `forall_inst`
        // refutation before the ground solver later appends a weaker
        // `Assume(instance) + trust` contradiction. Selecting the last empty
        // clause would discard the certified proof and retain the foreign
        // assumption. Prefer the first dependency cone that the independent
        // strict checker accepts; bounded failure falls back to the historical
        // final-empty selection and therefore remains fail closed.
        const MAX_STRICT_EMPTY_CANDIDATES: usize = 32;
        let empty_clause_roots: Vec<usize> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| match step {
                ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. }
                    if clause.is_empty() =>
                {
                    Some(index)
                }
                _ => None,
            })
            .collect();
        let mut selected_strict_root = false;
        if empty_clause_roots.len() > 1 {
            for target in empty_clause_roots
                .iter()
                .copied()
                .take(MAX_STRICT_EMPTY_CANDIDATES)
            {
                let mut candidate = proof.clone();
                if crate::executor::proof_resolution::prune_to_empty_clause_derivation_at(
                    &mut candidate,
                    target,
                ) {
                    match self.check_proof_strict_with_datatypes(&candidate) {
                        Ok(_) => {
                            proof = candidate;
                            selected_strict_root = true;
                            break;
                        }
                        Err(error) if ay_core::misc_cli_flags().trace_cegqi_attr => {
                            eprintln!(
                                "[quant-proof] empty root {target} strict selection declined: {error}"
                            );
                            for (index, step) in candidate.steps.iter().take(64).enumerate() {
                                eprintln!("[quant-proof] candidate[{index}] = {step:?}");
                            }
                        }
                        Err(_) => {}
                    }
                }
            }
        }
        if !selected_strict_root {
            crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);
        }

        // RoundingMode finite-domain certification. The core represents
        // SMT-LIB's built-in five-element sort as uninterpreted and injects its
        // domain axioms before solving. SAT reconstruction can surface those
        // roots either as Generic theory lemmas or as premiseless `trust`
        // leaves. Promote only exact instances accepted by the proof checker's
        // own five-mode recognizer; every other generated leaf remains trust.
        self.rebuild_finite_enum_pigeonhole_refutation(&mut proof);
        // The generic rebuild gets one ownership-checked opportunity. Do not
        // retain a potentially large detector graph beside the final proof.
        self.clear_finite_enum_proof_state();
        self.rebuild_rounding_mode_pigeonhole_refutation(&mut proof);
        Self::promote_rounding_mode_domain_lemmas(&self.ctx.terms, &mut proof);

        // Contextual ROW2 repair (#trust-count→0): the eager array lane can
        // record the context-dependent unit `select(store(a,i,v),j)=select(a,j)`
        // and let SAT use the separate `i≠j` assertion.  A unit ROW2 equality
        // is not a theorem.  Rebuild the load-bearing proof from the two original
        // assertions with the self-contained guarded ROW2 clause before any
        // quality/strictness decisions are made.
        self.promote_contextual_array_row2_lemmas(&mut proof);
        self.replace_with_exact_authored_array_row2_refutation(&mut proof);

        // Datatype constructor-distinctness promotion (#8419 / trust_count→0).
        // The live conflict classifier emits `(not (= C1(..) C2(..)))` for
        // distinct constructors as Generic/trust because it does not carry the
        // datatype registry. Now — on the pruned, load-bearing proof, with the
        // elaboration context's declarations available — promote the confirmed
        // distinctness lemmas to the strict-checkable `DatatypeDistinct` kind so
        // the strict checker validates them and the terminal-trust gate no
        // longer downgrades these UNSATs to unknown. Mirrors the existing
        // `promote_generic_theory_lemma_kinds_after_rewrite` pass.
        self.promote_datatype_distinct_lemmas(&mut proof);

        // Integer-divisibility promotion (#trust-count→0): a linear conflict that
        // is RATIONALLY satisfiable but INTEGER-infeasible (`2y = 7`: gcd 2 ∤ 7)
        // is missed by Farkas reconstruction (rational) and, in a nonlinear
        // context, emitted as `Generic`/trust. Promote each such single-literal
        // lemma the checker's own recognizer confirms to the strict-checkable
        // `LiaGeneric` + `Divisibility`. SOUND: the recognizer IS the strict
        // checker's `validate_divisibility` (gcd test with an integer-sort guard),
        // so a promoted step is independently re-validated; non-matching lemmas
        // stay trust. No verdict change — the lemma is already a valid tautology.
        Self::promote_lia_divisibility_lemmas(&self.ctx.terms, &mut proof);

        // FP classification promotion (#trust-count→0): re-tag a Generic/trust FP
        // classification/identity lemma to the strict-checkable `FpClassification`
        // kind iff the checker's own recognizer confirms it (exhaustive bounded
        // exact-IEEE evaluation). SOUND + fail-closed; see method.
        Self::promote_fp_classification_lemmas(&self.ctx.terms, &mut proof);

        // FP forward-error promotion (#trust-count→0): re-tag the Generic/trust
        // lemma that closes a forward-error refutation (negated input facts +
        // negated rounding-error goal) to the strict-checkable `FpForwardError`
        // kind iff the checker's own analytic recognizer confirms it (full
        // exact-rational re-derivation of the enclosure/error propagation).
        // SOUND + fail-closed; see method.
        Self::promote_fp_forward_error_lemmas(&self.ctx.terms, &mut proof);

        // RoundingMode finite-domain proof promotion. The solve path injects
        // exact five-value distinctness/coverage axioms because the core stores
        // `RoundingMode` as an uninterpreted sort. Those formulas are FP-theory
        // theorems, not authored assumptions. Promote only units accepted by
        // the strict checker's exact schema recognizer; malformed or partial
        // lookalikes remain trust/unauthorized and fail closed.
        Self::promote_fp_rounding_mode_domain_axioms(&self.ctx.terms, &mut proof);

        // Packed propositional clauses introduced by top-level connective
        // flattening are generated tautologies, not authored assumptions.
        // Promote only units accepted by the strict checker's structural
        // complement/and-projection recognizer. This is deliberately separate
        // from the RM-domain rule: one certifies Boolean clausification, the
        // other certifies the fixed IEEE domain.
        Self::promote_bool_tautology_leaves(&self.ctx.terms, &mut proof);

        // str.len length-axiom promotion (#selfcert-strlen): the solver injects
        // universally-valid str.len theorems (concat-length sum, empty↔zero,
        // non-negativity, constant/equal length, containment bounds) during
        // QF_SLIA/QF_S preprocessing. Being no authored premise, they surfaced as
        // foreign `assume` leaves the #8821 provenance gate rejected, degrading a
        // correct UNSAT to `unknown`. Re-tag each such leaf as the strict
        // checker's independently re-derived `StringLengthLemma` rule; malformed
        // lookalikes stay `assume` and fail closed.
        Self::promote_string_length_lemma_axioms(&self.ctx.terms, &mut proof);

        // Array read-over-write collapse (#trust-count→0): an assertion that is
        // the negation of a ROW1 instance folds to `false` during elaboration,
        // degenerating the UNSAT proof to a single empty-clause `trust` step.
        // Reconstruct the assume + strict-checkable `ArraySelectStore` lemma +
        // resolution from the parsed assertion. SOUND + fail-closed; see method.
        self.promote_array_row_collapse(&mut proof);
        self.promote_array_row_value_mismatch(&mut proof);

        // Datatype selector-projection collapse (#trust-count→0): an assertion
        // `(not (= (sel_i (C a..)) a_i))` folds to `false` during elaboration,
        // degenerating the proof to a single empty-clause trust step.
        // Reconstruct assume + strict-checkable `DatatypeSelectorProject` lemma +
        // resolution from the parsed assertion. SOUND + fail-closed; see method.
        self.promote_dt_selector_collapse(&mut proof);

        self.promote_reflexive_collapse_family(&mut proof);

        // Bitvector identity collapse (#trust-count→0): a small-width BV assertion
        // `(not (= (OP a b) c))` whose equality is a bounded tautology folds to
        // `false`, degenerating the proof to a single empty-clause trust step.
        // Reconstruct assume + strict-checkable `BvBitBlast` lemma (re-validated
        // by exhaustive bounded evaluation) + resolution. SOUND + fail-closed;
        // see method.
        self.promote_bv_identity_collapse(&mut proof);

        // Linear-arithmetic identity collapse (#trust-count→0): an integer
        // assertion `(not (= L R))` whose equality is a linear tautology (e.g.
        // `(* x 0) = 0`) folds to `false`, degenerating the proof to a single
        // empty-clause trust step. Reconstruct assume + strict-checkable
        // `LiaGeneric`/`LinearIdentity` lemma + resolution. SOUND + fail-closed;
        // see method.
        self.promote_nia_linear_identity_collapse(&mut proof);

        // Euclidean `mod` range collapse (#trust-count→0): an authored
        // equality such as `(= (mod x 3) 4)` is rejected by the LIA encoder
        // before a checkable range certificate survives, leaving a trust-backed
        // terminal derivation. Rebuild the exact authored equality plus a
        // strict-checkable `LiaModRange` theorem. The checker independently
        // requires a non-zero constant divisor and an out-of-range constant
        // remainder.
        self.promote_lia_mod_range_collapse(&mut proof);

        // If-then-else identical-branches collapse (#trust-count→0): an assertion
        // `(not (= (ite c x x) x))` folds to `false`, degenerating the proof to a
        // single empty-clause trust step. Reconstruct assume + strict-checkable
        // `IteSame` lemma (raw `mk_ite_raw` keeps the ite) + resolution. SOUND +
        // fail-closed; see method.
        self.promote_ite_same_collapse(&mut proof);

        // Boolean tautology collapse (#trust-count→0): a propositional
        // contradiction assertion (e.g. `(not (= (not (not p)) p))`) folds to
        // `false`, degenerating the proof to a single empty-clause trust step.
        // Run this general bounded fallback after the more specific IteSame
        // reconstruction so the latter retains its dedicated certificate and
        // Lean firewall artifact. Reconstruct assume(A) + strict-checkable
        // `BoolTautology` lemma `(not A)` (re-validated by exhaustive bounded
        // evaluation) + resolution. SOUND + fail-closed; see method.
        self.promote_bool_tautology_collapse(&mut proof);

        // BV bit-blast whole-proof collapse (C5): a QF_BV UNSAT established
        // through the eager bit-blast + SAT lane whose reconstructed proof
        // degenerated to the single empty-clause `trust` step (and that none
        // of the specific collapse promotions above could reconstruct).
        // Faithfully rebuild every parsed assertion, then prefer an internal
        // `BvBitBlast` lemma only when the checker independently recognizes
        // the joint-negation clause and the assembled proof replays strict-
        // complete. The Alethe printer still lowers this general lemma to an
        // attributed `hole`: carcara's BV support requires cvc5's `@bbterm`
        // convention, which ay's blaster does not produce.
        // If either gate declines, preserve real `assume`s plus ONE attributed
        // `hole` for the exact joint negation/closing chain. Every checkable
        // step remains valid, and the unchecked gap remains explicit.
        // Fail-closed: fires only on the degenerate shape, only when EVERY
        // assertion faithfully rebuilds inside the QF_BV bool/BV fragment
        // (per-node raw-application guards), and only when BV content is
        // present. The strict gate rejects the fallback hole while accepting
        // the independently checked `BvBitBlast` candidate.
        self.rescue_bv_bitblast_collapse(&mut proof);

        // NIA pin-substitution collapse (#trust-count→0): the residual trust step
        // in pinned-multiplication infeasibility. After divisibility promotion the
        // proof is trust(= k (* v c)) + divisibility(¬…) + resolution; the trust
        // step derives the substituted equation from (= (* a b) k) ∧ (= a c).
        // Reconstruct it as assume + eq_congruent + LinearIdentity bridge +
        // eq_transitive + resolution. MUST run after promote_lia_divisibility_lemmas
        // (the detection keys on step[1] already being LiaGeneric/Divisibility) and
        // is orthogonal to split_euf_congruence_lemmas (that pass rewrites trust
        // *TheoryLemma*s; this trust step is a *Step*). SOUND + fail-closed with a
        // whole-proof check_proof_strict revert gate; see method.
        self.promote_nia_pin_substitution(&mut proof);

        // EUF fused-congruence split (#trust-count→0): the congruence closure
        // emits `a=b ∧ b=c → f(a)=f(c)` as ONE `trust` lemma; split it into a
        // checker-validated `eq_transitive` + `eq_congruent` + their resolution
        // so the proof carries no trust step here. Fail-safe: only fires on the
        // recognized unary-congruence-over-chain shape, reproduces the original
        // clause exactly, and leaves any other lemma untouched.
        Self::split_euf_congruence_lemmas(&mut self.ctx.terms, &mut proof);

        // General certified EUF-leaf promotion. Unlike the all-or-nothing
        // original-assertion surgery, this replaces only individually
        // recognized Generic EUF leaves and preserves every Assume verbatim.
        // That keeps independent proof obligations separate: an unrelated
        // preprocessing-authority gap remains visible, while the EUF clause
        // itself carries eq_congruent/eq_transitive/eq_congruent_pred plus an
        // explicit weakening for unused conflict literals. Atomic strict
        // validation prevents partial promotion from masking any other trust.
        // Authenticated array-extensionality leaves are deferred: the EUF pass
        // promotes them only on its strict-check clone, while the real proof's
        // final extensionality pass below remains after every surgery.
        self.promote_certified_generic_euf_leaves(&mut proof);

        // Shadowed-store equality expansion: the eager array fixpoint uses the
        // compact, solve-friendly theorem
        //
        //   store(store(a,i,v),j,x) = store(store(a,i,w),j,x)
        //     -> i=j OR v=w.
        //
        // It is a derived theorem, not a primitive ROW rule.  Replace only the
        // exact Generic schema with a strict proof composed from equality
        // congruence, ROW1/ROW2, transitivity, and resolution.  This runs after
        // the generic EUF splitter so the whole-proof strict/revert gate is not
        // defeated by another congruence lemma that the preceding pass can
        // already discharge.
        self.split_shadowed_store_equality_lemmas(&mut proof);

        // Array extensionality certification (#ext-diff-cert). The eager array
        // lane INJECTS the Skolemized extensionality axiom
        // `(= a b) ∨ ¬(= (select a k) (select b k))` as an assertion; being no
        // problem premise, it ended up either demoted to `trust` or rejected at
        // export as a non-problem `assume`, and the `--self-check` gate degraded
        // the whole (correct) UNSAT to `unknown`.
        //
        // The clause is NOT a tautology, so it cannot simply be relabelled a
        // theory lemma. This pass instead records the WITNESS PROVENANCE as
        // proof content — an `array_ext_diff_intro` step binding `k` to the
        // pair it was minted for — which `ay-proof` then independently checks
        // (bound once, not self-referential, and FRESH against the problem's
        // own symbols). This second, idempotent call runs last: it appends steps
        // that must survive every prune and matches the axiom in whichever shape
        // the passes above left it. Fail-closed; see `proof_array_ext`.
        self.promote_array_extensionality_axioms(&mut proof);

        // Final RM authority boundary. Late proof surgery may retain the
        // solver's weakened six-term conflict clause even after the injected
        // domain/Boolean assumptions above were individually certified. The
        // exact checker recognizes its load-bearing literal only when it is the
        // complete K6 pairwise-distinct negation over the five-value RM domain.
        // Re-run the same producer/checker predicate here, after every surgery;
        // malformed, partial, or wrong-sort conflicts remain Generic and fail
        // strict validation.
        Self::promote_fp_rounding_mode_domain_axioms(&self.ctx.terms, &mut proof);

        // Final str.len length-axiom boundary (#selfcert-strlen): mirror the RM
        // boundary above — a late collapse/rebuild pass can re-materialize an
        // injected length axiom as an `assume` leaf, so re-run the promotion here,
        // after every surgery and immediately before proof validation, so no
        // certified length theorem is left as a foreign assume.
        Self::promote_string_length_lemma_axioms(&self.ctx.terms, &mut proof);

        // Generic BV conflicts are promoted only after the strict checker's
        // own semantic recognizer produces and replays a bit-blast/LRAT
        // refutation of the exact clause. This covers both the small exhaustive
        // lane and scalable width-32 identities while leaving SAT, unsupported,
        // or unsurfaceable clauses Generic (and therefore fail-closed).
        Self::promote_semantically_checked_bv_lemmas(&self.ctx.terms, &mut proof);

        // Exact authored `false` premise (#verification-consumer-proof-assert-authority).
        //
        // A native consumer can legitimately assert the Boolean constant
        // `false` after independently simplifying an obligation.  SAT proof
        // reconstruction used to keep exploring unrelated theory conflicts in
        // that case, leaving Generic/trust leaves on the terminal path even
        // though the problem itself already contains the empty contradiction.
        // Replace that defective detour with the smallest strict proof, but
        // ONLY when the exact canonical `false` TermId is present in the
        // independently assembled authored premise scope.  The replacement is
        // committed only after the strict checker validates every step and the
        // premise authorization against that same scope.
        self.replace_with_exact_authored_false_refutation(&mut proof);
        self.run_authored_replacement_cascade(&mut proof);

        self.run_arithmetic_reconstruction_fallbacks(&mut proof);

        // Some native certificate kinds are intentionally not surfaceable on
        // the pinned Alethe wire (for example `BvLiaTautology`). They are
        // valid internal certificates, but must not suppress an authored-root
        // reconstruction that can produce a fully checkable document. Give
        // the conjunction planner one final opportunity after the internal
        // fallback; its atomic commit gate still requires a complete strict
        // proof over the exact authored scope.
        if self.proof_has_known_wire_gap(&proof) {
            self.replace_with_exact_authored_conjunct_refutation(&mut proof, RepairEntry::Check);
        }
        false_source::demote_unattributed_assumed_false(self, &mut proof);
        self.demote_unrenderable_eq_transitive_lemmas(&mut proof);
        // Proof validation (#4393): validates all non-Hole steps via partial
        // checker. Replaces the old check_proof + Hole-skip pattern that skipped
        // entire proofs when ANY Hole step was present.
        #[cfg(feature = "proof-checker")]
        self.run_internal_proof_check(&proof);
        #[cfg(not(feature = "proof-checker"))]
        {
            if self.strict_proofs_enabled() {
                // Strict mode without proof-checker feature: use the strict
                // checker with datatype-distinctness validation (#8419).
                match self.check_proof_strict_with_datatypes(&proof) {
                    Ok(_quality) => {
                        let total = proof.steps.len() as u32;
                        self.proof_check_result = Some(PartialProofCheck {
                            checked_steps: total,
                            skipped_hole_steps: 0,
                            total_steps: total,
                        });
                    }
                    Err(e) => {
                        let total = proof.steps.len() as u32;
                        self.proof_check_result = Some(PartialProofCheck {
                            checked_steps: total,
                            skipped_hole_steps: 0,
                            total_steps: total,
                        });
                        tracing::error!(
                            error = %e,
                            total_steps = total,
                            "strict proof checker rejected UNSAT proof"
                        );
                    }
                }
            } else {
                let (partial, error) = check_proof_partial(&proof, &self.ctx.terms);
                self.proof_check_result = Some(partial.clone());
                if let Some(ref e) = error {
                    tracing::error!(
                        error = %e,
                        result = %partial,
                        "internal proof checker rejected UNSAT proof"
                    );
                }
            }
        }

        // Proof quality metrics (#4176, #4420).
        let quality = self.validate_and_measure_proof(&proof);
        if let Some(ref q) = quality {
            self.populate_proof_quality_stats(q);
        }
        self.last_proof_quality = quality;

        // Postcondition contracts (#4642): proof built successfully.
        debug_assert!(
            !proof.steps.is_empty(),
            "BUG: build_unsat_proof produced an empty proof"
        );
        debug_assert!(
            Self::proof_derives_empty_clause(&proof),
            "BUG: build_unsat_proof produced a proof that does not derive the empty clause"
        );
        #[cfg(feature = "proof-checker")]
        debug_assert!(
            self.proof_check_result.is_some(),
            "BUG: build_unsat_proof did not run internal proof checker"
        );

        self.promote_final_collection_axioms(&mut proof);

        self.last_proof = Some(proof);
    }

    /// Replace an arbitrary UNSAT derivation with the canonical proof from an
    /// exact authored `false` premise.
    ///
    /// This is deliberately an identity test against the strict checker's
    /// authored problem scope.  A normalized term that happens to fold to
    /// `false`, a solver-injected `false`, or any non-Boolean lookalike cannot
    /// authorize the rewrite.  The candidate is checked atomically before it
    /// replaces the original proof, so a checker/printer rule mismatch fails
    /// closed and leaves the original (possibly trust-bearing) proof visible.
    fn replace_with_exact_authored_false_refutation(&mut self, proof: &mut Proof) {
        let false_term = self.ctx.terms.false_term();
        // A canonical `false` TermId is not enough: elaboration also maps any
        // authored contradiction (for example `x - x <= -1`) to that same
        // identifier. The shared premise-authority gate admits only exact
        // literal-false assertion or assumption provenance.
        if !self.boolean_constant_premises_authored().1
            || !matches!(
                self.ctx.terms.get(false_term),
                TermData::Const(Constant::Bool(false))
            )
        {
            return;
        }

        // Alethe's `false` rule proves `(not false)`.  Resolve that tautology
        // against the exact authored `false` assumption to obtain the empty
        // clause.  No trust/hole/theory shortcut participates.
        let not_false = self.ctx.terms.mk_not_raw(false_term);
        let mut candidate = Proof::new();
        let premise = candidate.add_assume(false_term, Some("exact_authored_false".to_string()));
        let tautology =
            candidate.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
        candidate.add_resolution(Vec::new(), false_term, premise, tautology);

        if self.check_proof_strict_with_datatypes(&candidate).is_ok() {
            *proof = candidate;
        }
    }

    /// Rebuild a trust-bearing refutation directly from one exact authored
    /// conjunction.
    ///
    /// Native API consumers commonly submit a theorem as one negated
    /// implication. Canonical Boolean elaboration turns
    /// `not (A -> C)` into an `and` whose leaves are the antecedent facts and
    /// `not C`; solver preprocessing then reasons over those leaves.  A leaf is
    /// not itself an authored assertion, so retaining it as an `Assume` or
    /// relabelling it as `trust` is invalid.  This reconstruction instead:
    ///
    /// 1. assumes only the immutable authored root;
    /// 2. derives every leaf with checked `and_pos` + resolution steps; and
    /// 3. proves the contradiction with reconstructed Farkas, an exportable
    ///    congruence/linear-identity chain, or strict EUF transitivity.
    ///
    /// Every candidate is atomically replayed by the strict checker and its
    /// sole assumption is independently checked against the exact source scope.
    fn replace_with_exact_authored_conjunct_refutation(
        &mut self,
        proof: &mut Proof,
        entry: RepairEntry,
    ) {
        if entry == RepairEntry::Check && self.authored_cascade_publishable(proof) {
            return;
        }
        fn collect_leaves(
            terms: &TermStore,
            term: TermId,
            path: &mut Vec<u32>,
            leaves: &mut Vec<(TermId, Vec<u32>)>,
            include_root: bool,
        ) {
            if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
                if name == "and" {
                    for (position, &child) in args.iter().enumerate() {
                        path.push(position as u32);
                        collect_leaves(terms, child, path, leaves, true);
                        path.pop();
                    }
                    return;
                }
            }
            if include_root || !path.is_empty() {
                leaves.push((term, path.clone()));
            }
        }
        // Route tags cannot collide with an `and` operand index: the source
        // audit bounds every authored connective far below `u32::MAX`.
        const NEGATED_IMPLIES_ANTECEDENT: u32 = u32::MAX;
        const NEGATED_IMPLIES_CONSEQUENT: u32 = u32::MAX - 1;

        fn derive_leaf(
            terms: &mut TermStore,
            proof: &mut Proof,
            root_assume: ProofId,
            root: TermId,
            path: &[u32],
        ) -> Option<ProofId> {
            let mut current_id = root_assume;
            let mut current_term = root;
            let mut positions = path;

            // Stable authored provenance now preserves the exact
            // `not (=> A B)` root instead of authorizing its elaborated
            // `(and A (not B))` surrogate. Derive the two components with the
            // native Alethe implication rules, then continue ordinary
            // `and_pos` projection inside A. No generated surrogate is ever
            // assumed.
            if let Some((&route, rest)) = positions.split_first() {
                if matches!(
                    route,
                    NEGATED_IMPLIES_ANTECEDENT | NEGATED_IMPLIES_CONSEQUENT
                ) {
                    let TermData::Not(implication) = terms.get(root).clone() else {
                        return None;
                    };
                    let TermData::App(Symbol::Named(operator), args) =
                        terms.get(implication).clone()
                    else {
                        return None;
                    };
                    if operator != "=>" || args.len() != 2 {
                        return None;
                    }
                    let component = if route == NEGATED_IMPLIES_ANTECEDENT {
                        args[0]
                    } else {
                        terms.mk_not_raw(args[1])
                    };
                    let rule = if route == NEGATED_IMPLIES_ANTECEDENT {
                        AletheRule::ImpliesNeg1
                    } else {
                        AletheRule::ImpliesNeg2
                    };
                    let projection = proof.add_rule_step(
                        rule,
                        vec![implication, component],
                        Vec::new(),
                        Vec::new(),
                    );
                    current_id =
                        proof.add_resolution(vec![component], implication, projection, root_assume);
                    current_term = component;
                    positions = rest;
                    if route == NEGATED_IMPLIES_CONSEQUENT && !positions.is_empty() {
                        return None;
                    }
                }
            }

            for &position in positions {
                let TermData::App(Symbol::Named(name), args) = terms.get(current_term) else {
                    return None;
                };
                if name != "and" {
                    return None;
                }
                let child = *args.get(position as usize)?;
                let not_parent = terms.mk_not_raw(current_term);
                let projection = proof.add_rule_step(
                    AletheRule::AndPos(position),
                    vec![not_parent, child],
                    Vec::new(),
                    vec![current_term],
                );
                current_id =
                    proof.add_resolution(vec![child], current_term, projection, current_id);
                current_term = child;
            }
            Some(current_id)
        }

        /// Build the exportable affine-equality proof used by concrete
        /// arithmetic goals such as `x=2 ∧ y=3 ∧ x+y≠5`.
        ///
        /// A single internal Farkas certificate can validate this conflict by
        /// case-splitting the disequality.  Alethe `la_generic`, however, has
        /// only one signed linear combination and cannot encode both branches.
        /// Keep internal and exported proof authority aligned by composing
        /// ordinary checkable rules instead:
        ///
        /// * `eq_congruent` transports the authored argument equalities through
        ///   the arithmetic application;
        /// * `LinearIdentity` evaluates the resulting constant affine term;
        /// * `eq_transitive` connects those equalities to the authored goal.
        ///
        /// Recognition is deliberately narrow.  Every application argument
        /// must have its own positive equality leaf, and the constant bridge
        /// must pass the checker's exact linear-identity recognizer.
        fn build_affine_equality_refutation(
            terms: &mut TermStore,
            root: TermId,
            leaves: &[(TermId, Vec<u32>)],
        ) -> Option<Proof> {
            for (goal_index, &(goal_leaf, ref goal_path)) in leaves.iter().enumerate() {
                let TermData::Not(goal_eq) = terms.get(goal_leaf) else {
                    continue;
                };
                let goal_eq = *goal_eq;
                let Some((goal_lhs, goal_rhs)) = decode_eq_local(terms, goal_eq) else {
                    continue;
                };

                for (source_app, target) in [(goal_lhs, goal_rhs), (goal_rhs, goal_lhs)] {
                    if !matches!(terms.sort(source_app), Sort::Int)
                        || !matches!(terms.sort(target), Sort::Int)
                    {
                        continue;
                    }
                    let TermData::App(source_symbol, source_args) = terms.get(source_app).clone()
                    else {
                        continue;
                    };
                    if source_args.is_empty() {
                        continue;
                    }

                    let mut premise_indices = Vec::with_capacity(source_args.len());
                    let mut premise_equalities = Vec::with_capacity(source_args.len());
                    let mut replacement_args = Vec::with_capacity(source_args.len());
                    let mut complete = true;
                    for source_arg in source_args {
                        let matched =
                            leaves
                                .iter()
                                .enumerate()
                                .find_map(|(leaf_index, &(leaf, _))| {
                                    if leaf_index == goal_index
                                        || premise_indices.contains(&leaf_index)
                                        || matches!(terms.get(leaf), TermData::Not(_))
                                    {
                                        return None;
                                    }
                                    let (lhs, rhs) = decode_eq_local(terms, leaf)?;
                                    if lhs == source_arg
                                        && terms.sort(rhs) == terms.sort(source_arg)
                                    {
                                        Some((leaf_index, leaf, rhs))
                                    } else if rhs == source_arg
                                        && terms.sort(lhs) == terms.sort(source_arg)
                                    {
                                        Some((leaf_index, leaf, lhs))
                                    } else {
                                        None
                                    }
                                });
                        let Some((leaf_index, equality, replacement)) = matched else {
                            complete = false;
                            break;
                        };
                        premise_indices.push(leaf_index);
                        premise_equalities.push(equality);
                        replacement_args.push(replacement);
                    }
                    if !complete {
                        continue;
                    }

                    let app_sort = terms.sort(source_app).clone();
                    let replacement_app =
                        terms.mk_app(source_symbol.clone(), replacement_args, app_sort);
                    if replacement_app == source_app {
                        continue;
                    }
                    let congruence_eq = terms.mk_app(
                        Symbol::named("="),
                        [source_app, replacement_app],
                        Sort::Bool,
                    );
                    let identity_eq =
                        terms.mk_app(Symbol::named("="), [replacement_app, target], Sort::Bool);
                    if !ay_core::proof_validation::recognize_lia_linear_identity(
                        terms,
                        &[identity_eq],
                    ) {
                        continue;
                    }

                    let mut candidate = Proof::new();
                    let root_assume = candidate.add_assume(root, None);
                    let mut premise_units = Vec::with_capacity(premise_indices.len());
                    for &leaf_index in &premise_indices {
                        let unit = derive_leaf(
                            terms,
                            &mut candidate,
                            root_assume,
                            root,
                            &leaves[leaf_index].1,
                        )?;
                        premise_units.push(unit);
                    }
                    let goal_unit =
                        derive_leaf(terms, &mut candidate, root_assume, root, goal_path)?;

                    let mut congruence_clause = Vec::with_capacity(premise_equalities.len() + 1);
                    for &equality in &premise_equalities {
                        congruence_clause.push(terms.mk_not_raw(equality));
                    }
                    congruence_clause.push(congruence_eq);
                    let mut congruence_unit = candidate.add_rule_step(
                        AletheRule::EqCongruent,
                        congruence_clause.clone(),
                        Vec::new(),
                        Vec::new(),
                    );
                    let mut residual = congruence_clause;
                    for (&equality, &unit) in premise_equalities.iter().zip(premise_units.iter()) {
                        let negated = terms.mk_not_raw(equality);
                        let position = residual.iter().position(|&lit| lit == negated)?;
                        let _ = residual.remove(position);
                        congruence_unit = candidate.add_resolution(
                            residual.clone(),
                            equality,
                            congruence_unit,
                            unit,
                        );
                    }
                    if residual != [congruence_eq] {
                        continue;
                    }

                    let identity = candidate.add_step(ProofStep::TheoryLemma {
                        theory: "LIA".to_string(),
                        clause: vec![identity_eq],
                        farkas: Some(FarkasAnnotation::new(vec![num_rational::Rational64::from(
                            1,
                        )])),
                        kind: TheoryLemmaKind::LiaGeneric,
                        lia: Some(ay_core::LiaAnnotation::LinearIdentity),
                    });
                    let not_congruence = terms.mk_not_raw(congruence_eq);
                    let not_identity = terms.mk_not_raw(identity_eq);
                    let transitivity = candidate.add_rule_step(
                        AletheRule::EqTransitive,
                        vec![not_congruence, not_identity, goal_eq],
                        Vec::new(),
                        Vec::new(),
                    );
                    let goal_from_congruence = candidate.add_resolution(
                        vec![not_identity, goal_eq],
                        congruence_eq,
                        transitivity,
                        congruence_unit,
                    );
                    let goal = candidate.add_resolution(
                        vec![goal_eq],
                        identity_eq,
                        goal_from_congruence,
                        identity,
                    );
                    candidate.add_resolution(Vec::new(), goal_eq, goal, goal_unit);
                    return Some(candidate);
                }
            }
            None
        }

        const MAX_AUTHORED_CONJUNCTS: usize = 64;
        let authored = self.exact_concrete_authored_scope();
        let parsed_assertions = self.ctx.assertions_parsed().to_vec();
        let original_assertions = self.proof_original_problem_assertions();
        for &root in &authored {
            let mut leaves = Vec::new();
            let root_shape = self.ctx.terms.get(root).clone();
            if let TermData::Not(implication) = root_shape {
                if let TermData::App(Symbol::Named(operator), args) =
                    self.ctx.terms.get(implication).clone()
                {
                    if operator == "=>" && args.len() == 2 {
                        let mut antecedent_leaves = Vec::new();
                        collect_leaves(
                            &self.ctx.terms,
                            args[0],
                            &mut Vec::new(),
                            &mut antecedent_leaves,
                            true,
                        );
                        for (leaf, mut path) in antecedent_leaves {
                            path.insert(0, NEGATED_IMPLIES_ANTECEDENT);
                            leaves.push((leaf, path));
                        }
                        let not_consequent = self.ctx.terms.mk_not_raw(args[1]);
                        leaves.push((not_consequent, vec![NEGATED_IMPLIES_CONSEQUENT]));
                    }
                }
            }
            if leaves.is_empty() {
                collect_leaves(&self.ctx.terms, root, &mut Vec::new(), &mut leaves, false);
            }
            if leaves.len() < 2 || leaves.len() > MAX_AUTHORED_CONJUNCTS {
                continue;
            }

            let mut blocking_clause = Vec::with_capacity(leaves.len());
            let mut pivots = Vec::with_capacity(leaves.len());
            for &(leaf, _) in &leaves {
                match self.ctx.terms.get(leaf).clone() {
                    TermData::Not(inner) => {
                        blocking_clause.push(inner);
                        pivots.push(inner);
                    }
                    _ => {
                        blocking_clause.push(self.ctx.terms.mk_not_raw(leaf));
                        pivots.push(leaf);
                    }
                }
            }

            if let Some(candidate) =
                build_affine_equality_refutation(&mut self.ctx.terms, root, &leaves)
            {
                if self.commit_if_strictly_checked(proof, candidate, &authored) {
                    self.restore_authored_root_surface_after_conjunct_rebuild(
                        root,
                        &original_assertions,
                        &parsed_assertions,
                    );
                    return;
                }
            }

            let mut theory_candidates = Vec::new();
            let mut farkas = None;
            let mut kind = TheoryLemmaKind::Generic;
            if super::proof_farkas::try_lra_farkas_reconstruction(
                &self.ctx.terms,
                &blocking_clause,
                &mut farkas,
                &mut kind,
            ) && !kind.is_trust()
            {
                // A rational Farkas contradiction is valid for both Real and
                // Int domains. Use the strict Farkas rule directly; the LIA
                // annotations describe integer-only arguments and are neither
                // needed nor appropriate for this rational certificate.
                theory_candidates.push((TheoryLemmaKind::LraFarkas, farkas, None));
            }
            // EUF equality transitivity is an Alethe rule rather than a
            // TheoryLemma kind. The strict checker decides whether this exact
            // blocking clause is a valid chain; non-EUF lookalikes fail closed.
            theory_candidates.push((
                TheoryLemmaKind::Generic,
                None,
                Some(AletheRule::EqTransitive),
            ));

            for (kind, farkas, boolean_rule) in theory_candidates {
                let mut candidate = Proof::new();
                let root_assume = candidate.add_assume(root, None);
                let mut leaf_units = Vec::with_capacity(leaves.len());
                let mut derivation_failed = false;
                for (_, path) in &leaves {
                    let Some(unit) =
                        derive_leaf(&mut self.ctx.terms, &mut candidate, root_assume, root, path)
                    else {
                        derivation_failed = true;
                        break;
                    };
                    leaf_units.push(unit);
                }
                if derivation_failed {
                    continue;
                }

                let mut current = if let Some(rule) = boolean_rule {
                    candidate.add_rule_step(rule, blocking_clause.clone(), Vec::new(), Vec::new())
                } else {
                    candidate.add_step(ProofStep::TheoryLemma {
                        theory: "LIA".to_string(),
                        clause: blocking_clause.clone(),
                        farkas,
                        kind,
                        lia: None,
                    })
                };
                let mut residual = blocking_clause.clone();
                for ((&pivot, &(leaf, _)), &leaf_unit) in
                    pivots.iter().zip(leaves.iter()).zip(leaf_units.iter())
                {
                    let complement = if matches!(self.ctx.terms.get(leaf), TermData::Not(_)) {
                        pivot
                    } else {
                        self.ctx.terms.mk_not_raw(leaf)
                    };
                    let Some(position) = residual.iter().position(|&lit| lit == complement) else {
                        derivation_failed = true;
                        break;
                    };
                    let _ = residual.remove(position);
                    current = candidate.add_resolution(residual.clone(), pivot, current, leaf_unit);
                }
                if derivation_failed || !residual.is_empty() {
                    continue;
                }
                if self.commit_if_strictly_checked(proof, candidate, &authored) {
                    self.restore_authored_root_surface_after_conjunct_rebuild(
                        root,
                        &original_assertions,
                        &parsed_assertions,
                    );
                    return;
                }
            }
        }
    }

    /// Restore only the exact authored spelling of the assumed root after the
    /// canonical conjunction reconstruction has passed its strict commit
    /// gate. Derived operands keep their checker-validated canonical spelling;
    /// the root override affects the `assume` line and the negative gate in
    /// `and_pos`, which the Alethe printer validates as exact complements.
    fn restore_authored_root_surface_after_conjunct_rebuild(
        &mut self,
        root: TermId,
        originals: &[TermId],
        parsed: &[FrontendTerm],
    ) {
        if !super::proof_surface_syntax::surface_override_roots_have_bounded_work(
            &self.ctx.terms,
            [root],
        ) {
            return;
        }
        let Some(index) = originals.iter().position(|&term| term == root) else {
            return;
        };
        let Some(source) = parsed.get(index) else {
            return;
        };
        let mut overrides = self.last_proof_term_overrides.clone().unwrap_or_default();
        if !super::proof_surface_syntax::surface_override_map_is_bounded(&overrides) {
            return;
        }
        super::proof_surface_syntax::collect_root_surface_term_override(
            &mut self.ctx,
            root,
            source,
            &mut overrides,
        );
        if !super::proof_surface_syntax::surface_override_map_is_bounded(&overrides) {
            return;
        }
        self.last_proof_term_overrides = Some(overrides);
    }

    /// Rebuild the exact mixed LIA/EUF value-conflict lane from authored
    /// premises.
    ///
    /// A common UFLIA refutation is lost when arithmetic preprocessing derives
    /// an argument equality before EUF closes a value conflict:
    ///
    /// `a + b = c, b = 0, f(a) = v, f(c) != v`.
    ///
    /// Reconstruct it as a checked composition: Farkas derives each needed
    /// argument equality, `eq_congruent` transports the application, and
    /// `eq_transitive` transports the known value. Only exact immutable roots
    /// are assumed, and the whole candidate is replayed strictly before use.
    fn replace_with_exact_authored_affine_euf_refutation(&mut self, proof: &mut Proof) {
        const MAX_AUTHORED_ROOTS: usize = 64;
        const MAX_ARITH_ROOTS: usize = 12;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }

        fn is_pure_linear_term(terms: &TermStore, term: TermId) -> bool {
            if !matches!(terms.sort(term), Sort::Int | Sort::Real) {
                return false;
            }
            match terms.get(term) {
                TermData::Const(_) | TermData::Var(..) => true,
                TermData::App(Symbol::Named(operator), args) => match operator.as_str() {
                    "+" | "-" | "*" => args.iter().all(|&arg| is_pure_linear_term(terms, arg)),
                    _ => args.is_empty(),
                },
                _ => false,
            }
        }

        fn is_pure_linear_literal(terms: &TermStore, literal: TermId) -> bool {
            let atom = match terms.get(literal) {
                TermData::Not(inner) => *inner,
                _ => literal,
            };
            let TermData::App(Symbol::Named(operator), args) = terms.get(atom) else {
                return false;
            };
            args.len() == 2
                && matches!(operator.as_str(), "=" | "<" | "<=" | ">" | ">=")
                && terms.sort(args[0]) == terms.sort(args[1])
                && is_pure_linear_term(terms, args[0])
                && is_pure_linear_term(terms, args[1])
        }

        fn assume_exact(
            candidate: &mut Proof,
            assumptions: &mut Vec<(TermId, ProofId)>,
            term: TermId,
        ) -> ProofId {
            if let Some((_, id)) = assumptions.iter().find(|(existing, _)| *existing == term) {
                return *id;
            }
            let id = candidate.add_assume(term, None);
            assumptions.push((term, id));
            id
        }

        fn derive_affine_literal(
            terms: &mut TermStore,
            candidate: &mut Proof,
            assumptions: &mut Vec<(TermId, ProofId)>,
            arithmetic_roots: &[TermId],
            conclusion: TermId,
        ) -> Option<ProofId> {
            if arithmetic_roots.is_empty() || arithmetic_roots.len() > MAX_ARITH_ROOTS {
                return None;
            }
            // Prefer smaller premise sets. Besides producing compact proofs,
            // this avoids zero-coefficient baggage that external la_generic
            // checkers disagree about.
            for cardinality in 1..=arithmetic_roots.len() {
                let limit = 1_u64.checked_shl(arithmetic_roots.len() as u32)?;
                for mask in 1_u64..limit {
                    if mask.count_ones() as usize != cardinality {
                        continue;
                    }
                    let selected: Vec<TermId> = arithmetic_roots
                        .iter()
                        .enumerate()
                        .filter_map(|(index, &root)| {
                            ((mask & (1_u64 << index)) != 0).then_some(root)
                        })
                        .collect();
                    let mut clause: Vec<TermId> = selected
                        .iter()
                        .map(|&root| terms.mk_not_raw(root))
                        .collect();
                    clause.push(conclusion);
                    let mut farkas = None;
                    let mut inferred = TheoryLemmaKind::Generic;
                    if !super::proof_farkas::try_lra_farkas_reconstruction(
                        terms,
                        &clause,
                        &mut farkas,
                        &mut inferred,
                    ) {
                        continue;
                    }
                    let farkas = farkas?;
                    let mut current = candidate.add_step(ProofStep::TheoryLemma {
                        theory: "LRA".to_string(),
                        clause: clause.clone(),
                        farkas: Some(farkas),
                        kind: TheoryLemmaKind::LraFarkas,
                        lia: None,
                    });
                    let mut residual = clause;
                    for root in selected {
                        let negated = terms.mk_not_raw(root);
                        let position = residual.iter().position(|&term| term == negated)?;
                        let _ = residual.remove(position);
                        let premise = assume_exact(candidate, assumptions, root);
                        current =
                            candidate.add_resolution(residual.clone(), root, current, premise);
                    }
                    if residual == [conclusion] {
                        return Some(current);
                    }
                    return None;
                }
            }
            None
        }

        let arithmetic_roots: Vec<TermId> = authored
            .iter()
            .copied()
            .filter(|&root| is_pure_linear_literal(&self.ctx.terms, root))
            .collect();
        if arithmetic_roots.is_empty() || arithmetic_roots.len() > MAX_ARITH_ROOTS {
            return;
        }

        for &negative_root in &authored {
            let TermData::Not(goal_equality) = self.ctx.terms.get(negative_root) else {
                continue;
            };
            let goal_equality = *goal_equality;
            let Some((goal_lhs, goal_rhs)) = decode_eq_local(&self.ctx.terms, goal_equality) else {
                continue;
            };
            for (goal_app, value) in [(goal_lhs, goal_rhs), (goal_rhs, goal_lhs)] {
                let TermData::App(goal_symbol, goal_args) = self.ctx.terms.get(goal_app).clone()
                else {
                    continue;
                };
                // This reconstruction is specifically for EUF transport.
                // Interpreted applications such as `count + 1` are not function
                // symbols to pair by congruence here; admitting them sends pure
                // incremental LIA proofs through an exponential subset search.
                if goal_args.is_empty()
                    || is_pure_linear_term(&self.ctx.terms, goal_app)
                    || ay_frontend::is_reserved_symbol(goal_symbol.name())
                {
                    continue;
                }
                for &value_root in &authored {
                    if value_root == negative_root || arithmetic_roots.contains(&value_root) {
                        continue;
                    }
                    let Some((value_lhs, value_rhs)) = decode_eq_local(&self.ctx.terms, value_root)
                    else {
                        continue;
                    };
                    for (source_app, source_value) in
                        [(value_lhs, value_rhs), (value_rhs, value_lhs)]
                    {
                        if source_value != value {
                            continue;
                        }
                        let TermData::App(source_symbol, source_args) =
                            self.ctx.terms.get(source_app).clone()
                        else {
                            continue;
                        };
                        if source_symbol != goal_symbol
                            || source_args.len() != goal_args.len()
                            || source_args.is_empty()
                        {
                            continue;
                        }

                        let mut candidate = Proof::new();
                        let mut assumptions = Vec::new();
                        let mut argument_equalities = Vec::with_capacity(source_args.len());
                        let mut argument_units = Vec::with_capacity(source_args.len());
                        let mut failed = false;
                        for (&source_arg, &goal_arg) in source_args.iter().zip(goal_args.iter()) {
                            let argument_equality = self.ctx.terms.mk_app(
                                Symbol::named("="),
                                [source_arg, goal_arg],
                                Sort::Bool,
                            );
                            let unit = if source_arg == goal_arg {
                                candidate.add_rule_step(
                                    AletheRule::EqReflexive,
                                    vec![argument_equality],
                                    Vec::new(),
                                    Vec::new(),
                                )
                            } else {
                                let forward = self.ctx.terms.mk_app(
                                    Symbol::named("<="),
                                    [source_arg, goal_arg],
                                    Sort::Bool,
                                );
                                let reverse = self.ctx.terms.mk_app(
                                    Symbol::named("<="),
                                    [goal_arg, source_arg],
                                    Sort::Bool,
                                );
                                let Some(forward_unit) = derive_affine_literal(
                                    &mut self.ctx.terms,
                                    &mut candidate,
                                    &mut assumptions,
                                    &arithmetic_roots,
                                    forward,
                                ) else {
                                    failed = true;
                                    break;
                                };
                                let Some(reverse_unit) = derive_affine_literal(
                                    &mut self.ctx.terms,
                                    &mut candidate,
                                    &mut assumptions,
                                    &arithmetic_roots,
                                    reverse,
                                ) else {
                                    failed = true;
                                    break;
                                };
                                let not_forward = self.ctx.terms.mk_not_raw(forward);
                                let not_reverse = self.ctx.terms.mk_not_raw(reverse);
                                let split = self.ctx.terms.mk_app(
                                    Symbol::named("or"),
                                    [argument_equality, not_forward, not_reverse],
                                    Sort::Bool,
                                );
                                let split_unit = candidate.add_rule_step(
                                    AletheRule::LaDisequality,
                                    vec![split],
                                    Vec::new(),
                                    Vec::new(),
                                );
                                let split_clause = candidate.add_rule_step(
                                    AletheRule::Or,
                                    vec![argument_equality, not_forward, not_reverse],
                                    vec![split_unit],
                                    Vec::new(),
                                );
                                let forward_resolved = candidate.add_resolution(
                                    vec![argument_equality, not_reverse],
                                    forward,
                                    split_clause,
                                    forward_unit,
                                );
                                candidate.add_resolution(
                                    vec![argument_equality],
                                    reverse,
                                    forward_resolved,
                                    reverse_unit,
                                )
                            };
                            argument_equalities.push(argument_equality);
                            argument_units.push(unit);
                        }
                        if failed {
                            continue;
                        }

                        let congruence_equality = self.ctx.terms.mk_app(
                            Symbol::named("="),
                            [source_app, goal_app],
                            Sort::Bool,
                        );
                        let mut congruence_clause: Vec<TermId> = argument_equalities
                            .iter()
                            .map(|&equality| self.ctx.terms.mk_not_raw(equality))
                            .collect();
                        congruence_clause.push(congruence_equality);
                        let mut congruence_unit = candidate.add_rule_step(
                            AletheRule::EqCongruent,
                            congruence_clause.clone(),
                            Vec::new(),
                            Vec::new(),
                        );
                        let mut residual = congruence_clause;
                        for (&argument_equality, &argument_unit) in
                            argument_equalities.iter().zip(argument_units.iter())
                        {
                            let negated = self.ctx.terms.mk_not_raw(argument_equality);
                            let Some(position) = residual.iter().position(|&term| term == negated)
                            else {
                                failed = true;
                                break;
                            };
                            let _ = residual.remove(position);
                            congruence_unit = candidate.add_resolution(
                                residual.clone(),
                                argument_equality,
                                congruence_unit,
                                argument_unit,
                            );
                        }
                        if failed || residual != [congruence_equality] {
                            continue;
                        }

                        let not_congruence = self.ctx.terms.mk_not_raw(congruence_equality);
                        let not_value_root = self.ctx.terms.mk_not_raw(value_root);
                        let transitivity = candidate.add_rule_step(
                            AletheRule::EqTransitive,
                            vec![not_congruence, not_value_root, goal_equality],
                            Vec::new(),
                            Vec::new(),
                        );
                        let from_congruence = candidate.add_resolution(
                            vec![not_value_root, goal_equality],
                            congruence_equality,
                            transitivity,
                            congruence_unit,
                        );
                        let value_assume =
                            assume_exact(&mut candidate, &mut assumptions, value_root);
                        let goal_unit = candidate.add_resolution(
                            vec![goal_equality],
                            value_root,
                            from_congruence,
                            value_assume,
                        );
                        let negative_assume =
                            assume_exact(&mut candidate, &mut assumptions, negative_root);
                        candidate.add_resolution(
                            Vec::new(),
                            goal_equality,
                            goal_unit,
                            negative_assume,
                        );

                        if ay_proof::validate_reachable_assumes_in_problem_scope(
                            &candidate, &authored,
                        )
                        .is_ok()
                            && Self::proof_derives_empty_clause(&candidate)
                            && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                        {
                            *proof = candidate;
                            return;
                        }
                    }
                }
            }
        }

        // The same mixed-theory conflict can be authored without an explicit
        // UF disequality: `f(x) = v1`, `f(y) = v2`, arithmetic entails `x = y`,
        // and `v1 != v2` is itself an unconditional linear theorem (the smoke
        // corpus uses the distinct constants 10 and 20).  Compose that case
        // explicitly as argument equality -> congruence -> value transitivity
        // -> an independently reconstructed Farkas disequality.
        let mut app_value_roots = Vec::new();
        for &root in &authored {
            let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, root) else {
                continue;
            };
            for (app, value) in [(lhs, rhs), (rhs, lhs)] {
                let TermData::App(symbol, args) = self.ctx.terms.get(app).clone() else {
                    continue;
                };
                if args.is_empty()
                    || is_pure_linear_term(&self.ctx.terms, app)
                    || ay_frontend::is_reserved_symbol(symbol.name())
                    || !matches!(self.ctx.terms.sort(value), Sort::Int | Sort::Real)
                    || self.ctx.terms.sort(app) != self.ctx.terms.sort(value)
                {
                    continue;
                }
                app_value_roots.push((root, app, value, symbol, args));
            }
        }

        for source_index in 0..app_value_roots.len() {
            for goal_index in (source_index + 1)..app_value_roots.len() {
                let (source_root, source_app, source_value, source_symbol, source_args) =
                    app_value_roots[source_index].clone();
                let (goal_root, goal_app, goal_value, goal_symbol, goal_args) =
                    app_value_roots[goal_index].clone();
                if source_root == goal_root
                    || source_symbol != goal_symbol
                    || source_args.len() != goal_args.len()
                    || source_args.is_empty()
                    || self.ctx.terms.sort(source_value) != self.ctx.terms.sort(goal_value)
                {
                    continue;
                }

                let value_equality = self.ctx.terms.mk_app(
                    Symbol::named("="),
                    [source_value, goal_value],
                    Sort::Bool,
                );
                let value_disequality = self.ctx.terms.mk_not_raw(value_equality);
                let mut value_farkas = None;
                let mut value_kind = TheoryLemmaKind::Generic;
                let reconstructed_value_disequality =
                    super::proof_farkas::try_lra_farkas_reconstruction(
                        &self.ctx.terms,
                        &[value_disequality],
                        &mut value_farkas,
                        &mut value_kind,
                    );
                if !reconstructed_value_disequality {
                    // The LRA solver constant-folds a ground false equality
                    // before it can return a conflict annotation.  The exact
                    // one-row equality certificate is canonical; the strict
                    // checker below still independently validates it before
                    // this candidate can replace the original proof.
                    value_farkas = Some(FarkasAnnotation::from_ints(&[1]));
                }
                let Some(value_farkas) = value_farkas else {
                    continue;
                };

                let mut candidate = Proof::new();
                let mut assumptions = Vec::new();
                let mut argument_equalities = Vec::with_capacity(source_args.len());
                let mut argument_units = Vec::with_capacity(source_args.len());
                let mut failed = false;
                for (&source_arg, &goal_arg) in source_args.iter().zip(goal_args.iter()) {
                    let argument_equality = self.ctx.terms.mk_app(
                        Symbol::named("="),
                        [source_arg, goal_arg],
                        Sort::Bool,
                    );
                    let unit = if source_arg == goal_arg {
                        candidate.add_rule_step(
                            AletheRule::EqReflexive,
                            vec![argument_equality],
                            Vec::new(),
                            Vec::new(),
                        )
                    } else {
                        let forward = self.ctx.terms.mk_app(
                            Symbol::named("<="),
                            [source_arg, goal_arg],
                            Sort::Bool,
                        );
                        let reverse = self.ctx.terms.mk_app(
                            Symbol::named("<="),
                            [goal_arg, source_arg],
                            Sort::Bool,
                        );
                        let Some(forward_unit) = derive_affine_literal(
                            &mut self.ctx.terms,
                            &mut candidate,
                            &mut assumptions,
                            &arithmetic_roots,
                            forward,
                        ) else {
                            failed = true;
                            break;
                        };
                        let Some(reverse_unit) = derive_affine_literal(
                            &mut self.ctx.terms,
                            &mut candidate,
                            &mut assumptions,
                            &arithmetic_roots,
                            reverse,
                        ) else {
                            failed = true;
                            break;
                        };
                        let not_forward = self.ctx.terms.mk_not_raw(forward);
                        let not_reverse = self.ctx.terms.mk_not_raw(reverse);
                        let split = self.ctx.terms.mk_app(
                            Symbol::named("or"),
                            [argument_equality, not_forward, not_reverse],
                            Sort::Bool,
                        );
                        let split_unit = candidate.add_rule_step(
                            AletheRule::LaDisequality,
                            vec![split],
                            Vec::new(),
                            Vec::new(),
                        );
                        let split_clause = candidate.add_rule_step(
                            AletheRule::Or,
                            vec![argument_equality, not_forward, not_reverse],
                            vec![split_unit],
                            Vec::new(),
                        );
                        let forward_resolved = candidate.add_resolution(
                            vec![argument_equality, not_reverse],
                            forward,
                            split_clause,
                            forward_unit,
                        );
                        candidate.add_resolution(
                            vec![argument_equality],
                            reverse,
                            forward_resolved,
                            reverse_unit,
                        )
                    };
                    argument_equalities.push(argument_equality);
                    argument_units.push(unit);
                }
                if failed {
                    continue;
                }

                let mut congruence = None;
                if source_app != goal_app {
                    let congruence_equality = self.ctx.terms.mk_app(
                        Symbol::named("="),
                        [source_app, goal_app],
                        Sort::Bool,
                    );
                    let mut congruence_clause: Vec<TermId> = argument_equalities
                        .iter()
                        .map(|&equality| self.ctx.terms.mk_not_raw(equality))
                        .collect();
                    congruence_clause.push(congruence_equality);
                    let mut congruence_unit = candidate.add_rule_step(
                        AletheRule::EqCongruent,
                        congruence_clause.clone(),
                        Vec::new(),
                        Vec::new(),
                    );
                    let mut residual = congruence_clause;
                    for (&argument_equality, &argument_unit) in
                        argument_equalities.iter().zip(argument_units.iter())
                    {
                        let negated = self.ctx.terms.mk_not_raw(argument_equality);
                        let Some(position) = residual.iter().position(|&term| term == negated)
                        else {
                            failed = true;
                            break;
                        };
                        let _ = residual.remove(position);
                        congruence_unit = candidate.add_resolution(
                            residual.clone(),
                            argument_equality,
                            congruence_unit,
                            argument_unit,
                        );
                    }
                    if failed || residual != [congruence_equality] {
                        continue;
                    }
                    congruence = Some((congruence_equality, congruence_unit));
                }

                let source_assume = assume_exact(&mut candidate, &mut assumptions, source_root);
                let goal_assume = assume_exact(&mut candidate, &mut assumptions, goal_root);
                let mut chain_clause = vec![self.ctx.terms.mk_not_raw(source_root)];
                if let Some((congruence_equality, _)) = congruence {
                    chain_clause.push(self.ctx.terms.mk_not_raw(congruence_equality));
                }
                chain_clause.push(self.ctx.terms.mk_not_raw(goal_root));
                chain_clause.push(value_equality);
                let mut value_unit = candidate.add_rule_step(
                    AletheRule::EqTransitive,
                    chain_clause.clone(),
                    Vec::new(),
                    Vec::new(),
                );
                let mut residual = chain_clause;
                for (pivot, unit) in std::iter::once((source_root, source_assume))
                    .chain(congruence)
                    .chain(std::iter::once((goal_root, goal_assume)))
                {
                    let negated = self.ctx.terms.mk_not_raw(pivot);
                    let Some(position) = residual.iter().position(|&term| term == negated) else {
                        failed = true;
                        break;
                    };
                    let _ = residual.remove(position);
                    value_unit =
                        candidate.add_resolution(residual.clone(), pivot, value_unit, unit);
                }
                if failed || residual != [value_equality] {
                    continue;
                }

                let disequality_unit = candidate.add_step(ProofStep::TheoryLemma {
                    theory: "LRA".to_string(),
                    clause: vec![value_disequality],
                    farkas: Some(value_farkas),
                    kind: TheoryLemmaKind::LraFarkas,
                    lia: None,
                });
                candidate.add_resolution(Vec::new(), value_equality, value_unit, disequality_unit);

                if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored)
                    .is_ok()
                    && Self::proof_derives_empty_clause(&candidate)
                    && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                {
                    *proof = candidate;
                    return;
                }
            }
        }
    }

    /// Replace a non-strict provisional BV refutation with a complete,
    /// independently replayed Bool/BV refutation of the exact authored roots.
    ///
    /// The checker first proves the clause `¬A1 ∨ ... ∨ ¬An` with its bounded
    /// bit-blast/LRAT producer. Exact `Assume(Ai)` leaves then resolve that
    /// theorem to the empty clause. Unsupported roots, too many roots, SAT
    /// authored conjunctions, resource exhaustion, or any whole-proof replay
    /// failure leave the original trust-bearing proof untouched.
    fn replace_with_exact_authored_bv_refutation(&mut self, proof: &mut Proof) {
        const MAX_AUTHORED_ROOTS: usize = 64;
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }

        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty()
            || authored.len() > MAX_AUTHORED_ROOTS
            || authored
                .iter()
                .any(|&term| !matches!(self.ctx.terms.sort(term), Sort::Bool))
        {
            return;
        }

        let mut exact_roots = Vec::with_capacity(authored.len());
        let mut opposites = Vec::with_capacity(authored.len());
        for &assertion in &authored {
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
        if !ay_proof::recognize_bv_bitblast(&self.ctx.terms, &opposites) {
            return;
        }

        let mut candidate = Proof::new();
        let assumptions: Vec<ProofId> = exact_roots
            .iter()
            .enumerate()
            .map(|(index, &assertion)| {
                candidate.add_assume(assertion, Some(format!("authored_bv_{index}")))
            })
            .collect();
        let mut current = candidate.add_theory_lemma_with_kind(
            "bv",
            opposites.clone(),
            TheoryLemmaKind::BvBitBlast,
        );
        let mut residual = opposites.clone();
        for (&assumption, &opposite) in assumptions.iter().zip(opposites.iter()) {
            residual.retain(|&literal| literal != opposite);
            current = candidate.add_rule_step(
                AletheRule::ThResolution,
                residual.clone(),
                vec![current, assumption],
                Vec::new(),
            );
        }
        if residual.is_empty()
            && ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok()
            && Self::proof_derives_empty_clause(&candidate)
            && self.check_proof_strict_with_datatypes(&candidate).is_ok()
        {
            *proof = candidate;
        }
    }

    fn promote_semantically_checked_bv_lemmas(terms: &TermStore, proof: &mut Proof) {
        let mut proof_producer_attempts = 0_usize;
        for step in &mut proof.steps {
            let ProofStep::TheoryLemma {
                theory,
                clause,
                kind,
                ..
            } = step
            else {
                continue;
            };
            if *kind != TheoryLemmaKind::Generic {
                continue;
            }
            if ay_proof::bv_bitblast_requires_proof_producer(terms, clause) {
                proof_producer_attempts += 1;
                if proof_producer_attempts > ay_proof::MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF {
                    // Leave the lemma Generic: strict checking will reject it.
                    // This bounds total recognizer work before strict replay;
                    // an untrusted proof cannot multiply the per-lemma LRAT
                    // deadline by an arbitrary number of candidates.
                    continue;
                }
            }
            if !ay_proof::recognize_bv_bitblast(terms, clause) {
                continue;
            }
            *theory = "bv".to_string();
            *kind = TheoryLemmaKind::BvBitBlast;
        }
    }

    /// Decompose single Generic/trust theory lemmas for combined real conflicts
    /// into an EUF lemma plus an arithmetic bridge lemma (#6756 Packet 2).
    ///
    /// The recording-phase `record_real_combined_conflict_packet` can only
    /// succeed when the synthetic conclusion equality already exists in the
    /// term store. This pass runs in the proof builder with `&mut TermStore`
    /// access, so it can create the synthetic terms that the recording phase
    /// could not.
    fn decompose_combined_real_conflict_lemmas(terms: &mut TermStore, proof: &mut Proof) {
        use crate::theory_inference::decompose_generic_combined_real_lemma;

        let mut budget = crate::theory_inference::CombinedDecompositionBudget::new();
        let mut decomposed = Vec::new();
        for (idx, step) in proof.steps.iter().enumerate() {
            let ProofStep::TheoryLemma { kind, clause, .. } = step else {
                continue;
            };
            if !kind.is_trust() && !matches!(kind, TheoryLemmaKind::Generic) {
                continue;
            }
            if let Some((euf_kind, euf_clause, bridge_clause, bridge_farkas)) =
                decompose_generic_combined_real_lemma(terms, clause, &mut budget)
            {
                decomposed.push((idx, euf_kind, euf_clause, bridge_clause, bridge_farkas));
            }
        }

        // Apply decompositions in reverse order so indices remain valid.
        for (idx, euf_kind, euf_clause, bridge_clause, bridge_farkas) in
            decomposed.into_iter().rev()
        {
            proof.steps[idx] = ProofStep::TheoryLemma {
                theory: String::from("EUF"),
                kind: euf_kind,
                clause: euf_clause,
                farkas: None,
                lia: None,
            };
            proof.add_step(ProofStep::TheoryLemma {
                theory: String::from("LRA"),
                kind: TheoryLemmaKind::LraFarkas,
                clause: bridge_clause,
                farkas: Some(bridge_farkas),
                lia: None,
            });
        }
    }

    /// Split a `Generic` (trust) EUF congruence-over-equalities lemma into
    /// checker-validated `eq_transitive` / `eq_congruent` / `eq_reflexive` steps
    /// plus their resolution chain (#trust-count→0).
    ///
    /// The EUF congruence closure emits `a=b ∧ b=c ⊢ f(a)=f(c)` (and its n-ary
    /// generalizations) as ONE fused clause
    /// `(cl ¬(=A1 B1) … ¬(=Am Bm) (= (f A) (f B)))` tagged `:rule trust`. That
    /// clause is neither a valid `eq_transitive` (its conclusion is the congruence,
    /// not a chain endpoint) nor a valid `eq_congruent` (its premises are the
    /// equality CHAINS reaching each argument, not the direct per-argument
    /// equalities), so it cannot merely be RECLASSIFIED — it is decomposed. For
    /// each argument position `i`:
    /// ```text
    ///   Aᵢ ≠ Bᵢ via chain → eq_transitive: (cl <chain ¬eqs> (= Aᵢ Bᵢ))
    ///   Aᵢ = Bᵢ           → eq_reflexive : (cl (= Aᵢ Aᵢ))   [raw, see below]
    /// ```
    /// then one `eq_congruent` `(cl ¬(=A1 B1) … ¬(=Am Bm) (= (f A) (f B)))` over
    /// the DIRECT per-argument equalities, and a chain of BINARY `th_resolution`s
    /// resolving the congruence against each position's derivation on the pivot
    /// `(= Aᵢ Bᵢ)`. Every introduced `eq_transitive`/`eq_congruent`/`eq_reflexive`
    /// is independently validated by the strict checker (`ay_proof::checker::euf`,
    /// `ay_proof::checker::boolean_derived`), so the proof has no trust step here.
    /// Covers unary congruence-over-a-chain (`f(a)=f(c)` from `a=b=c`) and n-ary
    /// congruence mixing INDEPENDENT per-argument chains, REFLEXIVE (unchanged)
    /// arguments, and SHARED single-edge chains (`g(a,c)=g(b,d)` from `a=…=b`,
    /// `c=…=d`; `g(a,x)=g(c,x)` from `a=…=c`; `g(a,a)=g(b,b)` from `a=b`).
    /// Reflexive positions use a RAW `(= x x)` built via `mk_app` (`mk_eq` folds
    /// `(= x x)` to `true`); the raw term is resolved away inside the split, so no
    /// non-canonical term escapes into the surrounding proof.
    ///
    /// SOUND + FAIL-SAFE on three levels:
    /// 1. Recognition (`plan_euf_congruence_split`) fires ONLY when the conclusion
    ///    is a positive equality of two applications of the SAME symbol with equal
    ///    arity, every premise is a negated equality, every varying position is
    ///    chain-connected, and the chains together use EVERY premise (no redundant
    ///    premise the resolution chain cannot consume). Positions may share a chain
    ///    (`g(a,a)=g(b,b)`) or be reflexive (consume no premises); the binary
    ///    resolution chain deduplicates shared edges and the gate (level 3) is the
    ///    backstop for any combination the construction gets wrong.
    /// 2. Each replacement step is constructed to exactly match its checker's
    ///    acceptance shape; the final resolvent is computed by explicit set
    ///    resolution and replaces the fused clause's `ProofId`, so downstream
    ///    resolution is unaffected and nothing is logically weakened.
    /// 3. After the rebuild, the whole proof is re-validated with
    ///    [`check_proof`]; if it does not check (e.g. a resolution mismatch from a
    ///    shape this construction got wrong), the ENTIRE rebuild is reverted to the
    ///    original trust proof. Any unrecognized shape is copied through unchanged.
    ///
    /// The proof is rebuilt sequentially with an old→new `ProofId` remap (ids are
    /// positional — `ProofId(i) == steps[i]`); proofs containing subproof
    /// `Anchor`s (whose `end_step` is a forward reference) are skipped wholesale.
    fn split_euf_congruence_lemmas(terms: &mut TermStore, proof: &mut Proof) {
        // Anchors carry forward references the in-order remap cannot resolve.
        if proof
            .steps
            .iter()
            .any(|s| matches!(s, ProofStep::Anchor { .. }))
        {
            return;
        }
        let has_trust = proof
            .steps
            .iter()
            .any(|s| matches!(s, ProofStep::TheoryLemma { kind, .. } if kind.is_trust()));
        if !has_trust {
            return;
        }

        let original = proof.steps.clone();
        let original_named = proof.named_steps.clone();
        let old = std::mem::take(&mut proof.steps);
        let mut remap: Vec<ProofId> = Vec::with_capacity(old.len());
        let mut new_steps: Vec<ProofStep> = Vec::with_capacity(old.len());
        let mut changed = false;

        for step in old {
            // Premises reference only EARLIER steps (already remapped).
            let step = remap_step_premises(step, &remap);

            if let ProofStep::TheoryLemma { kind, clause, .. } = &step {
                if kind.is_trust() {
                    if let Some(plans) = plan_euf_congruence_split(terms, clause) {
                        let conc = clause[clause.len() - 1]; // (= (f A) (f B))
                        let (cur_id, _) =
                            emit_congruence_split_steps(terms, &mut new_steps, &plans, conc, false);
                        remap.push(cur_id);
                        changed = true;
                        continue;
                    }

                    // Cross-theory EUF congruence chain + one arithmetic
                    // COMPARISON literal (class 4), e.g. `x=y ∧ f(x)<f(y) ⊢ ⊥`
                    // or `a=b ∧ b=c ∧ f(a)>f(c) ⊢ ⊥`: the fused clause
                    // `(cl ¬(=A1 B1) … ¬(R (f A) (f B)))`. Derive the
                    // congruence `(= (f A) (f B))` via the SAME
                    // eq_transitive/eq_reflexive/eq_congruent machinery as the
                    // pure split above, refute it against the comparison with a
                    // solver-checked `la_generic` bridge (uninterpreted atoms
                    // are opaque variables to Farkas), and resolve back to the
                    // fused clause.
                    if let Some(rp) = plan_euf_relational_congruence(terms, clause) {
                        let (c_id, c_clause) = emit_congruence_split_steps(
                            terms,
                            &mut new_steps,
                            &rp.plans,
                            rp.cong_eq,
                            true,
                        );

                        // L: (cl ¬(= (f A) (f B)) ¬(R (f A) (f B)))
                        //    :rule la_generic — solver-synthesized Farkas.
                        let l_id = ProofId(new_steps.len() as u32);
                        new_steps.push(ProofStep::TheoryLemma {
                            theory: "LRA".to_string(),
                            clause: rp.la_clause.clone(),
                            farkas: Some(rp.la_farkas),
                            kind: rp.la_kind,
                            lia: None,
                        });

                        // R: resolve the derived congruence (supplies
                        // `(= (f A) (f B))`) against L (supplies its negation)
                        // → the original fused clause.
                        let resolvent =
                            binary_set_resolvent(&rp.la_clause, &c_clause, rp.cong_eq, rp.cong_neg);
                        let r_id = ProofId(new_steps.len() as u32);
                        new_steps.push(ProofStep::Step {
                            rule: AletheRule::ThResolution,
                            clause: resolvent,
                            premises: vec![l_id, c_id],
                            args: Vec::new(),
                        });
                        remap.push(r_id);
                        changed = true;
                        continue;
                    }

                    // Congruence-THEN-transitivity to a VALUE, e.g.
                    // `f(a)=v ∧ a=k ⊢ f(k)=v` (the fused clause
                    // `(cl ¬(=(f a) v) ¬(=a k) (= (f k) v))`, common in real
                    // proofs that substitute a known value into a function). The
                    // conclusion is NOT a congruence (its rhs is a value, not a
                    // matching application), so the pure-congruence handler above
                    // declines. Reconstruct: introduce the congruence
                    // `(= (f a) (f k))` (G_cong) from the substitution premise,
                    // then an eq_transitive chain `(f k) = (f a) = … = v`, then
                    // resolve them — reproducing the fused clause.
                    if let Some(vp) = plan_euf_value_congruence(terms, clause) {
                        // G_cong: (cl ¬(=A1 B1) … ¬(=Am Bm) (= (g A) (g B)))
                        //   :rule eq_congruent
                        let mut g_clause = vp.cong_premises.clone();
                        g_clause.push(vp.cong_eq);
                        let g_id = ProofId(new_steps.len() as u32);
                        new_steps.push(ProofStep::Step {
                            rule: AletheRule::EqCongruent,
                            clause: g_clause.clone(),
                            premises: Vec::new(),
                            args: Vec::new(),
                        });

                        // T: (cl ¬(=(g A)(g B)) <chain ¬eqs> (= (g B) v))
                        //    :rule eq_transitive  (chain (g B) = (g A) = … = v)
                        let mut t_clause = vec![vp.cong_neg];
                        t_clause.extend(vp.chain_to_value.iter().copied());
                        t_clause.push(vp.conc);
                        let t_id = ProofId(new_steps.len() as u32);
                        new_steps.push(ProofStep::Step {
                            rule: AletheRule::EqTransitive,
                            clause: t_clause.clone(),
                            premises: Vec::new(),
                            args: Vec::new(),
                        });

                        // R: resolve T (supplies ¬(=(f a)(f k))) against G_cong
                        // (supplies (=(f a)(f k))) → the original fused clause.
                        let resolvent =
                            binary_set_resolvent(&t_clause, &g_clause, vp.cong_eq, vp.cong_neg);
                        let r_id = ProofId(new_steps.len() as u32);
                        new_steps.push(ProofStep::Step {
                            rule: AletheRule::ThResolution,
                            clause: resolvent,
                            premises: vec![t_id, g_id],
                            args: Vec::new(),
                        });
                        remap.push(r_id);
                        changed = true;
                        continue;
                    }

                    // Cross-theory EUF congruence + LIA conflict, e.g.
                    // `f(a)=5 ∧ a=b ∧ f(b)>5 ⊢ ⊥`. Derive `f(b)=5` via
                    // eq_congruent + eq_transitive, then refute `f(b)=5 ∧ f(b)>5`
                    // with a solver-checked `la_generic`, then resolve back to the
                    // fused clause.
                    if let Some(lp) = plan_euf_lia_value_conflict(terms, clause) {
                        // G_cong: (cl ¬(=a b) (= (f a)(f b))) :rule eq_congruent
                        let g_clause = vec![lp.sub_lit, lp.cong_eq];
                        let g_id = ProofId(new_steps.len() as u32);
                        new_steps.push(ProofStep::Step {
                            rule: AletheRule::EqCongruent,
                            clause: g_clause.clone(),
                            premises: Vec::new(),
                            args: Vec::new(),
                        });

                        // T: (cl ¬(=(f a)(f b)) ¬(=(f a) v) (= (f b) v))
                        //    :rule eq_transitive  (chain (f b) = (f a) = v)
                        let t_clause = vec![lp.cong_neg, lp.val_lit, lp.derived_eq];
                        let t_id = ProofId(new_steps.len() as u32);
                        new_steps.push(ProofStep::Step {
                            rule: AletheRule::EqTransitive,
                            clause: t_clause.clone(),
                            premises: Vec::new(),
                            args: Vec::new(),
                        });

                        // L: (cl ¬(=(f b) v) ¬arith) :rule la_generic — the LIA
                        // conflict, with the solver-synthesized Farkas certificate.
                        let l_id = ProofId(new_steps.len() as u32);
                        new_steps.push(ProofStep::TheoryLemma {
                            theory: "LIA".to_string(),
                            clause: lp.la_clause.clone(),
                            farkas: Some(lp.la_farkas),
                            kind: TheoryLemmaKind::LiaGeneric,
                            lia: None,
                        });

                        // R1: resolve L (supplies ¬(=(f b) v)) against T (supplies
                        // (= (f b) v)) → drops the derived equality.
                        let r1 = binary_set_resolvent(
                            &lp.la_clause,
                            &t_clause,
                            lp.derived_eq,
                            lp.derived_neg,
                        );
                        let r1_id = ProofId(new_steps.len() as u32);
                        new_steps.push(ProofStep::Step {
                            rule: AletheRule::ThResolution,
                            clause: r1.clone(),
                            premises: vec![l_id, t_id],
                            args: Vec::new(),
                        });

                        // R2: resolve R1 (supplies ¬(=(f a)(f b))) against G_cong
                        // (supplies (= (f a)(f b))) → the original fused clause.
                        let r2 = binary_set_resolvent(&r1, &g_clause, lp.cong_eq, lp.cong_neg);
                        let r2_id = ProofId(new_steps.len() as u32);
                        new_steps.push(ProofStep::Step {
                            rule: AletheRule::ThResolution,
                            clause: r2,
                            premises: vec![r1_id, g_id],
                            args: Vec::new(),
                        });
                        remap.push(r2_id);
                        changed = true;
                        continue;
                    }
                }
            }

            let id = ProofId(new_steps.len() as u32);
            new_steps.push(step);
            remap.push(id);
        }

        if !changed {
            proof.steps = original;
            return;
        }

        let mut remapped_named = original_named.clone();
        remapped_named.retain(|_, id| {
            let old_index = id.0 as usize;
            if !matches!(original.get(old_index), Some(ProofStep::Assume(_))) {
                return false;
            }
            let Some(new_id) = remap.get(old_index) else {
                return false;
            };
            *id = *new_id;
            true
        });
        proof.steps = new_steps;
        proof.named_steps = remapped_named;

        // (3) Whole-proof revert gate: if the rebuilt proof fails to check (a
        // resolution the construction got wrong for some shape), discard ALL
        // splits and keep the original trust proof — never ship an invalid proof.
        if ay_proof::check_proof(proof, terms).is_err() {
            proof.steps = original;
            proof.named_steps = original_named;
        }
    }

    /// Expand exact shadowed two-store equality lemmas into standard Alethe
    /// primitives.
    ///
    /// The compact solve-path clause avoids manufacturing select-over-store
    /// ITEs for one fixed witness read. Proof export must still justify that
    /// consequence rather than mislabel it as ROW2.  For
    ///
    /// ```text
    /// E := store(store(a,i,v),j,x) = store(store(a,i,w),j,x)
    /// C := not E OR i=j OR v=w
    /// ```
    ///
    /// this rebuild emits raw witness reads, two ROW1 units, two ROW2 clauses,
    /// `E`-guarded select congruence (including a checked reflexive proof for
    /// the unchanged select index), one equality-transitivity clause, and the
    /// resolution chain whose exact result is `C`.  A packed unit `(or ...)`
    /// is reconstructed from the flat clause with standard `or_neg` steps.
    ///
    /// Fail-safe: exact schema recognition and a whole-proof datatype-aware
    /// strict check are required; any failure reverts every replacement.
    fn split_shadowed_store_equality_lemmas(&mut self, proof: &mut Proof) {
        // Anchors carry forward references the in-order remap cannot resolve.
        if proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Anchor { .. }))
        {
            return;
        }
        if !proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust()))
        {
            return;
        }

        let original = proof.steps.clone();
        let original_named = proof.named_steps.clone();
        let old = std::mem::take(&mut proof.steps);
        let mut remap = Vec::with_capacity(old.len());
        let mut new_steps = Vec::with_capacity(old.len());
        let mut changed = false;

        for step in old {
            let step = remap_step_premises(step, &remap);
            let plan = match &step {
                ProofStep::TheoryLemma { kind, clause, .. } if kind.is_trust() => {
                    plan_shadowed_store_equality_proof(&self.ctx.terms, clause)
                }
                _ => None,
            };
            if let Some(plan) = plan {
                let mark = new_steps.len();
                if let Some(replacement) =
                    emit_shadowed_store_equality_proof(&mut self.ctx.terms, &mut new_steps, &plan)
                {
                    remap.push(replacement);
                    changed = true;
                    continue;
                }
                new_steps.truncate(mark);
            }

            let id = ProofId(new_steps.len() as u32);
            new_steps.push(step);
            remap.push(id);
        }

        if !changed {
            proof.steps = original;
            return;
        }

        let mut remapped_named = original_named.clone();
        remapped_named.retain(|_, id| {
            let old_index = id.0 as usize;
            if !matches!(original.get(old_index), Some(ProofStep::Assume(_))) {
                return false;
            }
            let Some(new_id) = remap.get(old_index) else {
                return false;
            };
            *id = *new_id;
            true
        });
        proof.steps = new_steps;
        proof.named_steps = remapped_named;
        let mut validation = proof.clone();
        self.promote_array_extensionality_axioms(&mut validation);
        let valid = self
            .check_proof_strict_derivation_with_datatypes(&validation)
            .is_ok();
        if !valid {
            proof.steps = original;
            proof.named_steps = original_named;
        }
    }

    /// Finalize-time promotion of `Generic` datatype constructor-distinctness
    /// lemmas to the strict-checkable `DatatypeDistinct` kind (#8419).
    ///
    /// The live conflict classifier (`theory_inference`) cannot label these: it
    /// receives only the `TermStore`, while datatype constructor membership
    /// lives in the elaboration context (runtime datatype terms carry
    /// `Sort::Uninterpreted`). Here the executor has both, so it confirms each
    /// candidate `(not (= C1(..) C2(..)))` / binary-exclusion lemma against the
    /// `declare-datatype` registry via the checker's own recognizer and promotes
    /// only those — keeping the classifier and strict checker in lock-step.
    ///
    /// SOUND: a lemma is promoted only when `recognize_datatype_distinct`
    /// accepts it (distinct constructors of the same datatype — a tautology of
    /// datatype theory, machine-checked in `AySoundness/Datatype.lean`), and the
    /// strict checker independently re-validates every `DatatypeDistinct` step
    /// against the same registry. Non-distinctness lemmas stay `Generic` and are
    /// reported as trust as before — no soundness change, no verdict regression.
    fn promote_datatype_distinct_lemmas(&self, proof: &mut Proof) {
        let decls: Vec<(String, Vec<String>)> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect();
        if decls.is_empty() {
            return;
        }
        for step in &mut proof.steps {
            if let ProofStep::TheoryLemma { kind, clause, .. } = step {
                if *kind == TheoryLemmaKind::Generic
                    && ay_proof::recognize_datatype_distinct(&self.ctx.terms, clause, &decls)
                {
                    *kind = TheoryLemmaKind::DatatypeDistinct;
                }
            }
        }
    }

    /// Preserve the pre-existing reconstruction for ordinary bounded source
    /// surfaces. The sealed early path is only an exception to oversized-source
    /// poisoning; a decline here leaves the original proof unchanged.
    fn rebuild_finite_enum_pigeonhole_refutation(&mut self, proof: &mut Proof) {
        let Some(witness) = self.last_finite_enum_pigeonhole.as_ref() else {
            return;
        };
        if Some(witness.members.len()) != witness.k.checked_add(1) {
            return;
        }
        let member_set: ay_core::kani_compat::DetHashSet<TermId> =
            witness.members.iter().copied().collect();
        if member_set.len() != witness.members.len() {
            return;
        }
        let Some(pair_count) = witness
            .members
            .len()
            .checked_mul(witness.members.len().saturating_sub(1))
            .map(|pairs| pairs / 2)
        else {
            return;
        };
        let legitimate = self.proof_legit_assume_set();

        // Collect the authored disequality for every member pair, and the
        // matching equality literal for the lemma clause.
        let mut assumptions: Vec<TermId> = Vec::new();
        let mut equalities: Vec<TermId> = Vec::new();
        for (i, &a) in witness.members.iter().enumerate() {
            for &b in &witness.members[i + 1..] {
                let key = if a.0 < b.0 { (a, b) } else { (b, a) };
                let Some(&source) = witness.edge_sources.get(&key) else {
                    return;
                };
                if !legitimate.contains(&source) {
                    return;
                }
                // The source must be exactly `(not (= a b))`; anything else is
                // evidence we cannot cite verbatim.
                let TermData::Not(inner) = self.ctx.terms.get(source) else {
                    return;
                };
                let inner = *inner;
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(inner) else {
                    return;
                };
                if name != "=" || args.len() != 2 {
                    return;
                }
                let (lhs, rhs) = (args[0], args[1]);
                let matches_pair = (lhs == a && rhs == b) || (lhs == b && rhs == a);
                if !matches_pair {
                    return;
                }
                assumptions.push(source);
                equalities.push(inner);
            }
        }
        if assumptions.is_empty() {
            return;
        }
        if assumptions.len() != pair_count || equalities.len() != pair_count {
            return;
        }

        // A detector witness is not permission to replace an independently
        // owned proof. At this point every witness edge has already been bound
        // to a distinct, exact authored `(not (= a b))` source, so the expected
        // equality graph is bounded by the ordinary proof-source cap. Rebuild
        // only when the current dependency cone contains either the exact
        // trust-family `[false]` stub emitted by this finite-enum conflict path
        // or its normalized form: precisely the complete graph of complements
        // of those disequalities, with no duplicate or missing edge.
        // Surrounding SAT reconstruction steps are permitted.
        //
        // `ensure_empty_clause_derivation` can normalize the injected `false`
        // through the authored disequality origins before this pass runs. For
        // four members that produces the six-literal pigeonhole clause rather
        // than retaining `[false]`. Input-syntax rewriting can re-intern an
        // equality in an authored orientation, and raw resolution parity can
        // retain a complement as `(not (not (= a b)))` instead of simplifying
        // it to `(= a b)`. Match exactly those two structural forms by unordered
        // member pair rather than requiring the pre-rewrite equality `TermId`.
        // The exact source terms were independently authenticated above.
        let false_term = self.ctx.terms.false_term();
        let is_pigeonhole_stub = proof.steps.iter().any(|step| match step {
            ProofStep::TheoryLemma { kind, clause, .. } if kind.is_trust() => {
                if clause.as_slice() == [false_term] {
                    return true;
                }
                if clause.len() != pair_count {
                    return false;
                }
                let mut seen_pairs = ay_core::kani_compat::DetHashSet::default();
                clause.iter().all(|&literal| {
                    let equality = match self.ctx.terms.get(literal) {
                        TermData::App(Symbol::Named(name), _) if name == "=" => literal,
                        TermData::Not(negated) => match self.ctx.terms.get(*negated) {
                            TermData::Not(equality) => *equality,
                            _ => return false,
                        },
                        _ => return false,
                    };
                    let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(equality)
                    else {
                        return false;
                    };
                    let [left, right] = args.as_slice() else {
                        return false;
                    };
                    if name != "="
                        || left == right
                        || !member_set.contains(left)
                        || !member_set.contains(right)
                    {
                        return false;
                    }
                    let pair = if left.0 < right.0 {
                        (*left, *right)
                    } else {
                        (*right, *left)
                    };
                    seen_pairs.insert(pair)
                }) && seen_pairs.len() == pair_count
            }
            _ => false,
        });
        if !is_pigeonhole_stub {
            return;
        }

        let mut rebuilt = Proof::new();
        let mut premises: Vec<ProofId> = Vec::with_capacity(assumptions.len() + 1);
        let lemma_id = rebuilt.add_theory_lemma_with_kind(
            "DT",
            equalities,
            TheoryLemmaKind::DatatypeEnumPigeonhole,
        );
        premises.push(lemma_id);
        for &assumption in &assumptions {
            premises.push(rebuilt.add_assume(assumption, None));
        }
        rebuilt.add_rule_step(AletheRule::Resolution, Vec::new(), premises, Vec::new());
        *proof = rebuilt;
    }

    fn rebuild_rounding_mode_pigeonhole_refutation(&mut self, proof: &mut Proof) {
        let legitimate = self.proof_legit_assume_set();
        let candidates: Vec<_> = proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Assume(term) if legitimate.contains(term) => Some(*term),
                _ => None,
            })
            .collect();

        let mut certificate = None;
        for assumption in candidates {
            let negated = self.ctx.terms.mk_not_raw(assumption);
            if ay_proof::recognize_rounding_mode_domain(&self.ctx.terms, &[negated]) {
                certificate = Some((assumption, negated));
                break;
            }
        }
        let Some((assumption, negated)) = certificate else {
            return;
        };

        // The independently checked theorem says that more than five values of
        // the fixed five-element sort cannot be pairwise distinct. Rebuild the
        // noisy SAT/Tseitin chain as the direct two-premise refutation, retaining
        // only the caller-authored assumption as proof authority.
        let mut rebuilt = Proof::new();
        let assume_id = rebuilt.add_assume(assumption, None);
        let lemma_id = rebuilt.add_theory_lemma_with_kind(
            "FP",
            vec![negated],
            TheoryLemmaKind::RoundingModeDomain,
        );
        rebuilt.add_resolution(Vec::new(), assumption, assume_id, lemma_id);
        *proof = rebuilt;
    }

    /// Promote exact SMT-LIB `RoundingMode` domain axioms to their
    /// strict-checkable theory kind.
    fn promote_rounding_mode_domain_lemmas(terms: &TermStore, proof: &mut Proof) {
        for step in &mut proof.steps {
            let trust_clause = match step {
                ProofStep::TheoryLemma { kind, clause, .. } if kind.is_trust() => {
                    if ay_proof::recognize_rounding_mode_domain(terms, clause) {
                        *kind = TheoryLemmaKind::RoundingModeDomain;
                    }
                    None
                }
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    args,
                } if premises.is_empty()
                    && args.is_empty()
                    && ay_proof::recognize_rounding_mode_domain(terms, clause) =>
                {
                    Some(clause.clone())
                }
                _ => None,
            };
            if let Some(clause) = trust_clause {
                *step = ProofStep::TheoryLemma {
                    theory: "FP".to_string(),
                    clause,
                    farkas: None,
                    kind: TheoryLemmaKind::RoundingModeDomain,
                    lia: None,
                };
            }
        }
    }

    /// Finalize-time promotion of `Generic` integer-divisibility conflicts to the
    /// strict-checkable `LiaGeneric` + [`ay_core::LiaAnnotation::Divisibility`]
    /// (#trust-count→0).
    ///
    /// A conflict like `2y = 7` is rationally satisfiable (`y = 3.5`), so the
    /// Farkas (LRA) reconstruction misses it; in a nonlinear (QF_NIA) context the
    /// live classifier likewise emits the linear conflict as `Generic`/trust. Here
    /// the executor promotes each single-literal `(not (= A B))` lemma that
    /// `recognize_lia_divisibility` confirms to be integer-infeasible
    /// (`gcd(variable coefficients) ∤ constant`, all variables integer-sorted).
    ///
    /// SOUND: the recognizer delegates to the SAME `validate_divisibility` the
    /// strict checker runs, so every promoted `Divisibility` step is independently
    /// re-validated; a lemma that is not a genuine integer tautology is never
    /// promoted and stays trust (fail-closed). The verdict is unchanged — the
    /// lemma is already a valid tautology of integer arithmetic.
    /// FP classification promotion (#trust-count→0): the FP solver emits a
    /// classification / sign / structural-equality / comparison identity conflict
    /// lemma — e.g. `(= (fp.abs (fp.abs x)) (fp.abs x))`,
    /// `(not (and (fp.isNaN x) (fp.isNormal x)))` — as a `Generic`/trust theory
    /// lemma. Promote each such lemma the strict checker's OWN recognizer confirms
    /// to the strict-checkable `FpClassification` kind, so the residual trust step
    /// becomes a validated `fp_classification` (exhaustive bounded EXACT-IEEE
    /// evaluation). SOUND: `recognize_fp_classification_op` IS the strict checker's
    /// `validate_fp_classification`, so a promoted step is independently
    /// re-validated and a non-FP-tautology lemma stays trust (the recognizer
    /// returns `None`). The lemma term already carries the real FP structure, so
    /// no reconstruction or term rebuild is needed.
    fn promote_fp_classification_lemmas(terms: &TermStore, proof: &mut Proof) {
        for step in &mut proof.steps {
            if let ProofStep::TheoryLemma { kind, clause, .. } = step {
                if matches!(*kind, TheoryLemmaKind::Generic) {
                    if let Some(op) = ay_proof::recognize_fp_classification_op(terms, clause) {
                        *kind = TheoryLemmaKind::FpClassification { operation: op };
                    }
                }
            }
        }
    }

    /// Promote exact fixed-domain `RoundingMode` axioms from generic/injected
    /// proof leaves to an independently checked FP theory rule.
    fn promote_fp_rounding_mode_domain_axioms(terms: &TermStore, proof: &mut Proof) {
        for step in &mut proof.steps {
            match step {
                ProofStep::TheoryLemma { kind, clause, .. }
                    if kind.is_trust()
                        && ay_proof::recognize_fp_rounding_mode_domain(terms, clause) =>
                {
                    *kind = TheoryLemmaKind::FpRoundingModeDomain;
                }
                ProofStep::Assume(term)
                    if ay_proof::recognize_fp_rounding_mode_domain(terms, &[*term]) =>
                {
                    let term = *term;
                    *step = ProofStep::TheoryLemma {
                        theory: "FP".to_string(),
                        clause: vec![term],
                        farkas: None,
                        kind: TheoryLemmaKind::FpRoundingModeDomain,
                        lia: None,
                    };
                }
                _ => {}
            }
        }
        proof
            .named_steps
            .retain(|_, id| matches!(proof.steps.get(id.0 as usize), Some(ProofStep::Assume(_))));
    }

    /// Promote solver-generated packed Boolean tautology leaves to the strict
    /// checker's independently revalidated `BoolTautology` rule.
    fn promote_bool_tautology_leaves(terms: &TermStore, proof: &mut Proof) {
        for step in &mut proof.steps {
            match step {
                ProofStep::TheoryLemma { kind, clause, .. }
                    if kind.is_trust() && ay_proof::recognize_bool_tautology(terms, clause) =>
                {
                    *kind = TheoryLemmaKind::BoolTautology;
                }
                ProofStep::Assume(term) if ay_proof::recognize_bool_tautology(terms, &[*term]) => {
                    let term = *term;
                    *step = ProofStep::TheoryLemma {
                        theory: "Bool".to_string(),
                        clause: vec![term],
                        farkas: None,
                        kind: TheoryLemmaKind::BoolTautology,
                        lia: None,
                    };
                }
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    args,
                } if premises.is_empty()
                    && args.is_empty()
                    && ay_proof::recognize_bool_tautology(terms, clause) =>
                {
                    let clause = clause.clone();
                    *step = ProofStep::TheoryLemma {
                        theory: "Bool".to_string(),
                        clause,
                        farkas: None,
                        kind: TheoryLemmaKind::BoolTautology,
                        lia: None,
                    };
                }
                _ => {}
            }
        }
        proof
            .named_steps
            .retain(|_, id| matches!(proof.steps.get(id.0 as usize), Some(ProofStep::Assume(_))));
    }

    /// Promote the solver's injected `str.len` length axioms
    /// (`collect_str_len_axioms_from_roots`) from foreign `assume` leaves to the
    /// strict checker's independently re-derived `StringLengthLemma` rule.
    ///
    /// These facts — concat-length sum, empty↔zero-length, non-negativity,
    /// constant length, equal-length congruence, and containment length bounds —
    /// are UNIVERSALLY VALID `str.len` theorems, not authored premises, so being
    /// `assume`d they were rejected by the #8821 provenance gate and the whole
    /// (correct) UNSAT degraded to `unknown` under `--self-check` /
    /// `--strict-proofs`. Each is a theory tautology, so re-tagging the leaf as a
    /// unit `TheoryLemma` with the SAME clause `[t]` keeps every downstream
    /// resolution/DRUP linkage intact while giving the leaf a checkable rule.
    /// `ay_proof::recognize_string_length_lemma` is the EXACT precondition of the
    /// strict validator (structural, fail-closed on any near-miss), so a leaf
    /// that is not a genuine length theorem is left an `assume` and still fails
    /// closed. SOUND: an accepted clause is valid under every model
    /// (#selfcert-strlen).
    fn promote_string_length_lemma_axioms(terms: &TermStore, proof: &mut Proof) {
        for step in &mut proof.steps {
            match step {
                ProofStep::TheoryLemma { kind, clause, .. }
                    if kind.is_trust()
                        && ay_proof::recognize_string_length_lemma(terms, clause) =>
                {
                    *kind = TheoryLemmaKind::StringLengthLemma;
                }
                ProofStep::Assume(term)
                    if ay_proof::recognize_string_length_lemma(terms, &[*term]) =>
                {
                    let term = *term;
                    *step = ProofStep::TheoryLemma {
                        theory: "STRINGS".to_string(),
                        clause: vec![term],
                        farkas: None,
                        kind: TheoryLemmaKind::StringLengthLemma,
                        lia: None,
                    };
                }
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    args,
                } if premises.is_empty()
                    && args.is_empty()
                    && ay_proof::recognize_string_length_lemma(terms, clause) =>
                {
                    let clause = clause.clone();
                    *step = ProofStep::TheoryLemma {
                        theory: "STRINGS".to_string(),
                        clause,
                        farkas: None,
                        kind: TheoryLemmaKind::StringLengthLemma,
                        lia: None,
                    };
                }
                _ => {}
            }
        }
        proof
            .named_steps
            .retain(|_, id| matches!(proof.steps.get(id.0 as usize), Some(ProofStep::Assume(_))));
    }

    /// FP forward-error promotion (#trust-count→0): the forward-error tactic
    /// (`theories/fp/forward_error.rs`) detects its UNSAT outside the SAT
    /// loop, so the proof closes via `derive_empty_via_trust_lemma` — ONE
    /// `Generic`/trust theory lemma whose clause is the negation of all
    /// resolvable assumptions (the `fp.isNormal` + magnitude-bound input
    /// facts and the refuted rounding-error goal), resolved by genuine
    /// `th_resolution` to the empty clause. Promote that lemma to the
    /// strict-checkable `FpForwardError` kind iff the strict checker's OWN
    /// recognizer confirms it: `recognize_fp_forward_error` IS
    /// `validate_fp_forward_error`, which independently re-derives the whole
    /// refutation from the clause (fact mining, RNE + no-overflow side
    /// conditions, exact-rational half-ulp enclosure propagation, exact
    /// mirror-polynomial identity, strict claim contradiction). SOUND +
    /// fail-closed: a promoted step is independently re-validated in strict
    /// mode, and any clause the analytic checker cannot certify stays
    /// `Generic`/trust — no verdict change either way.
    fn promote_fp_forward_error_lemmas(terms: &TermStore, proof: &mut Proof) {
        for step in &mut proof.steps {
            if let ProofStep::TheoryLemma { kind, clause, .. } = step {
                if matches!(*kind, TheoryLemmaKind::Generic)
                    && ay_proof::recognize_fp_forward_error(terms, clause)
                {
                    *kind = TheoryLemmaKind::FpForwardError;
                }
            }
        }
    }

    /// Whether `clause` is a single negated GROUND arithmetic equality
    /// `(cl (not (= c1 c2)))` — both sides numeral-only (`+`/`-`/`*` over
    /// constants, no variables or theory atoms).
    fn clause_is_ground_equality_refutation(terms: &TermStore, clause: &[TermId]) -> bool {
        fn ground_numeral(terms: &TermStore, t: TermId) -> bool {
            match terms.get(t) {
                TermData::Const(_) => true,
                TermData::App(Symbol::Named(op), args) => {
                    matches!(op.as_str(), "+" | "-" | "*")
                        && args.iter().all(|&a| ground_numeral(terms, a))
                }
                _ => false,
            }
        }
        let [lit] = clause else {
            return false;
        };
        let TermData::Not(inner) = terms.get(*lit) else {
            return false;
        };
        let TermData::App(Symbol::Named(op), args) = terms.get(*inner) else {
            return false;
        };
        op == "=" && args.len() == 2 && args.iter().all(|&a| ground_numeral(terms, a))
    }

    fn promote_lia_divisibility_lemmas(terms: &TermStore, proof: &mut Proof) {
        for step in &mut proof.steps {
            if let ProofStep::TheoryLemma {
                kind,
                clause,
                farkas,
                lia,
                ..
            } = step
            {
                // Catch `Generic`/trust (nonlinear context), a `LiaGeneric` the LIA
                // solver emitted WITHOUT an integer annotation, AND an `LraFarkas`
                // whose RATIONAL certificate cannot eliminate the variables (a
                // divisibility/integer-CUT conflict, e.g. QF_LIA `2y = 7` or
                // `3x ∈ [1,2]`): each has `trust_count == 0` yet FAILS the strict
                // checker. The recognizer accepts ONLY genuine integer tautologies
                // (gcd ∤ const, or no multiple of gcd in a non-empty bounded range —
                // which rational Farkas provably cannot show), so attaching
                // `Divisibility` makes them genuinely strict-checkable without
                // disturbing any rationally-certified lemma.
                if matches!(
                    *kind,
                    TheoryLemmaKind::Generic
                        | TheoryLemmaKind::LiaGeneric
                        | TheoryLemmaKind::LraFarkas
                ) && lia.is_none()
                    && ay_core::proof_validation::recognize_lia_divisibility(terms, clause)
                {
                    // The fold-to-`false` collapse's GROUND refutation (a
                    // single `(cl (not (= c1 c2)))` over numeral-only sides,
                    // e.g. `(= 1 2)`: `0 = -1` trips the gcd recognizer but
                    // IS rationally refutable) already carries a verified
                    // rational certificate and checks externally as
                    // `la_generic`; re-kinding it to `lia_generic` would
                    // demote it to an external checker hole. Leave it
                    // untouched. Scoped to GROUND single-literal lemmas so
                    // genuine variable-carrying divisibility conflicts (which
                    // `la_generic` cannot express) keep the promotion.
                    if matches!(*kind, TheoryLemmaKind::LraFarkas)
                        && farkas.is_some()
                        && Self::clause_is_ground_equality_refutation(terms, clause)
                    {
                        continue;
                    }
                    *kind = TheoryLemmaKind::LiaGeneric;
                    // The `Divisibility` annotation drives strict VALIDATION (the
                    // gcd check). The Alethe printer renders `lia_generic` from the
                    // Farkas combination coefficient, so attach the trivial `[1]`
                    // (one literal) purely for rendering — validation uses the
                    // LiaAnnotation, not these coefficients.
                    *lia = Some(ay_core::LiaAnnotation::Divisibility);
                    if farkas.is_none() {
                        *farkas =
                            Some(FarkasAnnotation::new(vec![num_rational::Rational64::from(
                                1,
                            )]));
                    }
                }
            }
        }
    }

    /// Rebuild a STRING-LENGTH ARITHMETIC refutation directly from exact
    /// authored roots (#trust-count→0, the QF_S/QF_SLIA length-coherence
    /// family).
    ///
    /// The problem constrains a string term through `str.++` / `str.contains` /
    /// `str.prefixof` / `str.suffixof` and pins `str.len` values that cannot be
    /// reconciled — for example `(= (str.++ x y) "abc")` with
    /// `(= (str.len x) 2)` and `(= (str.len y) 2)`, where the concatenation is
    /// three characters long but its operands are pinned to four between them.
    /// z3 5.0.0 answers `unsat` and AY computes that verdict every time, but the
    /// CEGAR string lane closes the search outside the SAT trace, so no
    /// clause-level conflict reaches the proof, the reconstruction falls through
    /// to the whole-problem `trust` closer, and the mandatory certification gate
    /// correctly degrades a correct `unsat` to `unknown`.
    ///
    /// THE FIX IS A DERIVATION, NOT A RELAXATION. Every fact this pass needs is
    /// already a rule `ay-proof` validates independently:
    ///
    /// * [`TheoryLemmaKind::StringLengthLemma`], whose validator
    ///   (`validate_string_length_lemma`) re-derives the exact algebraic
    ///   identity from the clause alone — the concat-length sum with
    ///   multiset-matched operands, the constant length, the equal-length
    ///   congruence `(or (not (= s t)) LENEQ)`, the containment length bound
    ///   `(or (not PRED) (<= (str.len contained) (str.len container)))`, and
    ///   `str.len` non-negativity. Nothing is taken on the producer's word.
    /// * [`AletheRule::Or`], to turn a unit `(or A B)` lemma into the clause
    ///   `(cl A B)`.
    /// * [`TheoryLemmaKind::LraFarkas`], whose validator re-runs
    ///   `verify_farkas_conflict_lits_full` on the exact clause and certificate.
    ///
    /// The refutation for the example above is
    ///
    /// ```text
    /// (assume h0 (= (str.++ x y) "abc"))
    /// (assume h1 (= (str.len x) 2))
    /// (assume h2 (= (str.len y) 2))
    /// (step t0 (cl (or (not (= (str.++ x y) "abc")) (= (str.len (str.++ x y)) 3)))
    ///          :rule string_length_lemma)
    /// (step t1 (cl (not (= (str.++ x y) "abc")) (= (str.len (str.++ x y)) 3))
    ///          :rule or :premises (t0))
    /// (step t2 (cl (= (str.len (str.++ x y)) 3)) :rule resolution :premises (t1 h0))
    /// (step t3 (cl (= (str.len (str.++ x y)) (+ (str.len x) (str.len y))))
    ///          :rule string_length_lemma)
    /// (step t4 (cl (not (= (str.len x) 2)) (not (= (str.len y) 2))
    ///              (not (= (str.len (str.++ x y)) 3))
    ///              (not (= (str.len (str.++ x y)) (+ (str.len x) (str.len y)))))
    ///          :rule la_generic :args (…))
    /// (step t5 (cl) :rule resolution :premises (t4 h1 h2 t2 t3))
    /// ```
    ///
    /// Fail-closed at every step, mirroring
    /// [`Self::replace_with_exact_authored_store_permutation_refutation`]: it
    /// runs only on a proof the strict checker already rejects; every `assume`
    /// is an exact authored root; every length identity is admitted only when
    /// the CHECKER'S OWN matcher (`ay_proof::recognize_string_length_lemma`)
    /// accepts the clause, so no schema logic is duplicated producer-side; the
    /// arithmetic closure is a real Farkas certificate reconstructed by the LRA
    /// solver and independently re-verified; and the rebuilt proof must derive
    /// the empty clause, keep every reachable assume inside the authored scope,
    /// and pass `check_proof_strict_with_datatypes` before it replaces anything.
    ///
    /// NO FALSE-PROVE RISK: the candidate derives the empty clause from
    /// AUTHORED assertions plus clauses the strict checker independently
    /// re-derives, so it ESTABLISHES the verdict rather than borrowing it. When
    /// the derived facts are not jointly contradictory the Farkas
    /// reconstruction declines and the proof — and the `unknown` — are left
    /// exactly as they were found.
    fn replace_with_exact_authored_string_length_arith_refutation(&mut self, proof: &mut Proof) {
        // Work bounds. This pass runs on every refutation the strict checker
        // rejects, so it must be cheap to DECLINE. Declining leaves today's
        // behaviour exactly as it is (the verdict stays `unknown`), so the
        // bounds can only cost completeness on shapes far larger than any of
        // the length-coherence family.
        const MAX_AUTHORED_ROOTS: usize = 64;
        const MAX_SUBTERM_VISITS: usize = 4096;
        const MAX_DERIVED_FACTS: usize = 48;
        const MAX_FARKAS_LITERALS: usize = 64;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }

        // Cheap pre-filter: no string-sorted term anywhere in the authored
        // scope means this family cannot apply. Keeps the pass off the
        // overwhelming majority of rejected proofs without constructing a
        // single term.
        let Some(subterms) =
            Self::collect_string_relevant_subterms(&self.ctx.terms, &authored, MAX_SUBTERM_VISITS)
        else {
            return;
        };
        if subterms.concats.is_empty()
            && subterms.string_equalities.is_empty()
            && subterms.containments.is_empty()
        {
            return;
        }

        // ── Derive the certified length facts ────────────────────────────
        //
        // Each entry is (fact, provenance). `Provenance::Tautology` is a unit
        // `StringLengthLemma` clause; `Provenance::FromRoot(root, or_term)` is
        // the same lemma over `(or (not root) fact)`, clausified by
        // `AletheRule::Or` and resolved against the authored `root`.
        // Ordered by how load-bearing each family is, because `MAX_DERIVED_FACTS`
        // truncates the tail: the authored roots and the two root-conditioned
        // bridges carry the problem's actual content, the concat sums connect a
        // chain to its operands, and `str.len` non-negativity is the widest and
        // least often needed, so it goes last.
        let mut facts: Vec<(TermId, StringLengthFactProvenance)> = Vec::new();
        let push_fact = |facts: &mut Vec<(TermId, StringLengthFactProvenance)>,
                         fact: TermId,
                         provenance: StringLengthFactProvenance| {
            if facts.len() < MAX_DERIVED_FACTS && !facts.iter().any(|&(f, _)| f == fact) {
                facts.push((fact, provenance));
            }
        };

        // (1) Authored arithmetic roots join the same pool as ordinary assumes.
        for &root in &authored {
            if Self::is_arith_atom_local(&self.ctx.terms, root) {
                push_fact(&mut facts, root, StringLengthFactProvenance::Authored);
            }
        }

        // (2) Equal-length congruence, from every AUTHORED string equality.
        for &(root, left, right) in &subterms.string_equalities {
            if !authored.contains(&root) {
                continue;
            }
            let Some((fact, or_term)) = self.build_equal_length_congruence(root, left, right)
            else {
                continue;
            };
            push_fact(
                &mut facts,
                fact,
                StringLengthFactProvenance::FromRoot { root, or_term },
            );
        }

        // (3) Containment length bounds, from every AUTHORED containment.
        for &(root, contained, container) in &subterms.containments {
            if !authored.contains(&root) {
                continue;
            }
            let Some((fact, or_term)) =
                self.build_containment_length_bound(root, contained, container)
            else {
                continue;
            };
            push_fact(
                &mut facts,
                fact,
                StringLengthFactProvenance::FromRoot { root, or_term },
            );
        }

        // (3b) Regex length lower bounds, from every AUTHORED `str.in_re`. The
        //      bound is the CHECKER's own compositional minimum for the ground
        //      regex, so a membership joins the linear pool the same way a
        //      containment does.
        for &root in &authored {
            let Some(fact) = self.build_regex_length_lower_bound(root) else {
                continue;
            };
            push_fact(
                &mut facts,
                fact,
                StringLengthFactProvenance::FromRootClause {
                    root,
                    kind: TheoryLemmaKind::RegexLengthLowerBound,
                },
            );
        }

        // (4) Concat-length sums, for every `str.++` subterm (nested chains
        //     included, so a nested concat's length is connected to its leaves).
        for &concat in &subterms.concats {
            let Some(fact) = self.build_concat_length_sum(concat) else {
                continue;
            };
            push_fact(&mut facts, fact, StringLengthFactProvenance::Tautology);
        }

        // (5) Constant lengths, for every string-constant subterm.
        for &constant in &subterms.string_constants {
            let Some(fact) = self.build_constant_length(constant) else {
                continue;
            };
            push_fact(&mut facts, fact, StringLengthFactProvenance::Tautology);
        }

        // (6) `str.len` non-negativity, for every string-sorted subject.
        for &subject in &subterms.length_subjects {
            let Some(fact) = self.build_length_non_negativity(subject) else {
                continue;
            };
            push_fact(&mut facts, fact, StringLengthFactProvenance::Tautology);
        }
        if facts.len() < 2 || facts.len() > MAX_FARKAS_LITERALS {
            return;
        }

        // ── Close the arithmetic ─────────────────────────────────────────
        //
        // Rational Farkas first: it decides the whole length-coherence family
        // in one shot. The integer closure below handles what a rational
        // certificate provably cannot — `2·len(x) = 3` is rationally
        // satisfiable and only integrality refutes it.
        if let Some(candidate) = self.build_string_length_farkas_candidate(&facts, &authored) {
            *proof = candidate;
            return;
        }
        if let Some(candidate) = self.build_string_length_divisibility_candidate(&facts, &authored)
        {
            *proof = candidate;
        }
    }

    /// The commit gate shared by both length-arithmetic closures: a candidate
    /// replaces a proof only when every reachable `assume` is an exact authored
    /// root, the derivation reaches the empty clause, and the PLAIN strict
    /// checker accepts it end to end.
    fn string_length_candidate_is_committable(
        &self,
        candidate: &Proof,
        authored: &[TermId],
    ) -> bool {
        ay_proof::validate_reachable_assumes_in_problem_scope(candidate, authored).is_ok()
            && Self::proof_derives_empty_clause(candidate)
            && self.check_proof_strict_with_datatypes(candidate).is_ok()
    }

    /// Close a pool of certified length facts with a RATIONAL Farkas
    /// certificate, or `None` when the pool has no linear contradiction.
    ///
    /// Every fact is asserted TRUE, so the blocking clause is the pointwise
    /// negation. `try_lra_farkas_reconstruction` reconstructs the certificate
    /// with the LRA solver and independently re-verifies it against this exact
    /// clause before returning, and the strict `LraFarkas` validator re-runs
    /// that same verification on the committed step.
    fn build_string_length_farkas_candidate(
        &mut self,
        facts: &[(TermId, StringLengthFactProvenance)],
        authored: &[TermId],
    ) -> Option<Proof> {
        let full_clause: Vec<TermId> = facts
            .iter()
            .map(|&(fact, _)| self.ctx.terms.mk_not_raw(fact))
            .collect();
        let mut farkas = None;
        let mut inferred = TheoryLemmaKind::Generic;
        if !super::proof_farkas::try_lra_farkas_reconstruction(
            &self.ctx.terms,
            &full_clause,
            &mut farkas,
            &mut inferred,
        ) {
            return None;
        }
        let full_farkas = farkas?;

        // Shrink to the facts the certificate actually uses, so the rebuilt
        // proof assumes and derives nothing it does not need. The certificate
        // is RE-RECONSTRUCTED on the smaller clause (not merely truncated), so
        // the committed annotation is one the verifier accepted for exactly
        // the clause it annotates.
        let mut used: Vec<(TermId, StringLengthFactProvenance)> = facts
            .iter()
            .zip(full_farkas.coefficients.iter())
            .filter(|&(_, coefficient)| *coefficient != num_rational::Rational64::from(0))
            .map(|(&entry, _)| entry)
            .collect();
        let mut clause: Vec<TermId> = used
            .iter()
            .map(|&(fact, _)| self.ctx.terms.mk_not_raw(fact))
            .collect();
        let mut shrunk_farkas = None;
        let mut shrunk_kind = TheoryLemmaKind::Generic;
        if used.len() < 2
            || !super::proof_farkas::try_lra_farkas_reconstruction(
                &self.ctx.terms,
                &clause,
                &mut shrunk_farkas,
                &mut shrunk_kind,
            )
        {
            used = facts.to_vec();
            clause = full_clause;
            shrunk_farkas = Some(full_farkas);
        }
        let certificate = shrunk_farkas?;

        let mut candidate = Proof::new();
        let mut fact_units: Vec<ProofId> = Vec::with_capacity(used.len());
        for &(fact, provenance) in &used {
            fact_units.push(self.derive_string_length_fact(&mut candidate, fact, provenance)?);
        }
        // A rational Farkas certificate is strict-checkable for Int and Real
        // roots alike; `str.len` applications enter as opaque Int atoms exactly
        // as `la_generic` consumers treat them.
        let mut current = candidate.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: clause.clone(),
            farkas: Some(certificate),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        let mut residual = clause;
        for (&(fact, _), &unit) in used.iter().zip(fact_units.iter()) {
            let complement = self.ctx.terms.mk_not_raw(fact);
            let position = residual.iter().position(|&literal| literal == complement)?;
            let _ = residual.remove(position);
            current = candidate.add_resolution(residual.clone(), fact, current, unit);
        }
        (residual.is_empty() && self.string_length_candidate_is_committable(&candidate, authored))
            .then_some(candidate)
    }

    /// Close a pool of certified length facts with an INTEGER-divisibility
    /// argument, or `None` when no pair of equalities yields one.
    ///
    /// `(= (str.++ x x) "aba")` pins `2·len(x) = 3`, which has no INTEGER
    /// solution but is perfectly satisfiable over the rationals — no Farkas
    /// certificate exists, and the length-coherence closure above declines. Two
    /// equalities that share an endpoint chain to one equality by
    /// `AletheRule::EqTransitive` (whose validator re-derives the connecting
    /// path itself, in any orientation), and its negation is admitted only when
    /// `ay_core::proof_validation::recognize_lia_divisibility` — the EXACT
    /// precondition of the strict `Divisibility` validator, which re-runs the
    /// `gcd(coefficients) ∤ constant` test over integer-sorted atoms — accepts
    /// it. Nothing here is decided producer-side.
    fn build_string_length_divisibility_candidate(
        &mut self,
        facts: &[(TermId, StringLengthFactProvenance)],
        authored: &[TermId],
    ) -> Option<Proof> {
        // Pair search bound. Quadratic in the equality facts, each pair costing
        // one linear normalization, and this runs only after the Farkas closure
        // declined. Declining an oversized pool leaves the verdict `unknown`,
        // exactly as it is today.
        const MAX_EQUALITY_FACTS: usize = 32;

        let equalities: Vec<(usize, TermId, TermId)> = facts
            .iter()
            .enumerate()
            .filter_map(|(index, &(fact, _))| {
                decode_eq_local(&self.ctx.terms, fact).map(|(left, right)| (index, left, right))
            })
            .take(MAX_EQUALITY_FACTS)
            .collect();

        for (first_position, &(first_index, first_left, first_right)) in
            equalities.iter().enumerate()
        {
            for &(second_index, second_left, second_right) in &equalities[first_position + 1..] {
                // The endpoints the two equalities do NOT share. The premises
                // are stated exactly as authored/derived; `eq_transitive`
                // re-derives the connecting path from the clause alone, so no
                // orientation reasoning is duplicated here.
                let endpoints = if first_left == second_left {
                    (first_right, second_right)
                } else if first_left == second_right {
                    (first_right, second_left)
                } else if first_right == second_left {
                    (first_left, second_right)
                } else if first_right == second_right {
                    (first_left, second_left)
                } else {
                    continue;
                };
                if endpoints.0 == endpoints.1 {
                    continue;
                }
                let conclusion = self.ctx.terms.mk_app(
                    Symbol::named("="),
                    [endpoints.0, endpoints.1],
                    Sort::Bool,
                );
                let negated_conclusion = self.ctx.terms.mk_not_raw(conclusion);
                if !ay_core::proof_validation::recognize_lia_divisibility(
                    &self.ctx.terms,
                    &[negated_conclusion],
                ) {
                    continue;
                }

                let (first_fact, first_provenance) = facts[first_index];
                let (second_fact, second_provenance) = facts[second_index];
                let mut candidate = Proof::new();
                let first_unit =
                    self.derive_string_length_fact(&mut candidate, first_fact, first_provenance)?;
                let second_unit =
                    self.derive_string_length_fact(&mut candidate, second_fact, second_provenance)?;
                let negated_first = self.ctx.terms.mk_not_raw(first_fact);
                let negated_second = self.ctx.terms.mk_not_raw(second_fact);
                let transitivity = candidate.add_rule_step(
                    AletheRule::EqTransitive,
                    vec![negated_first, negated_second, conclusion],
                    Vec::new(),
                    Vec::new(),
                );
                let after_first = candidate.add_resolution(
                    vec![negated_second, conclusion],
                    first_fact,
                    transitivity,
                    first_unit,
                );
                let chained = candidate.add_resolution(
                    vec![conclusion],
                    second_fact,
                    after_first,
                    second_unit,
                );
                let divisibility = candidate.add_step(ProofStep::TheoryLemma {
                    theory: "LIA".to_string(),
                    clause: vec![negated_conclusion],
                    farkas: Some(FarkasAnnotation::new(vec![num_rational::Rational64::from(
                        1,
                    )])),
                    kind: TheoryLemmaKind::LiaGeneric,
                    lia: Some(ay_core::LiaAnnotation::Divisibility),
                });
                candidate.add_resolution(Vec::new(), conclusion, chained, divisibility);
                if self.string_length_candidate_is_committable(&candidate, authored) {
                    return Some(candidate);
                }
            }
        }
        None
    }

    /// Emit the steps that establish one derived length fact as a UNIT clause,
    /// returning the id of that unit.
    ///
    /// An authored root is simply assumed. A tautology is a unit
    /// `StringLengthLemma`. A root-conditioned fact is the `StringLengthLemma`
    /// over `(or (not root) fact)`, clausified by `AletheRule::Or` and resolved
    /// against the authored `root`. In every case the emitted lemma clause has
    /// already been accepted by the checker's own matcher.
    fn derive_string_length_fact(
        &mut self,
        candidate: &mut Proof,
        fact: TermId,
        provenance: StringLengthFactProvenance,
    ) -> Option<ProofId> {
        match provenance {
            StringLengthFactProvenance::Authored => Some(candidate.add_assume(fact, None)),
            StringLengthFactProvenance::Tautology => Some(candidate.add_theory_lemma_with_kind(
                "STRINGS",
                vec![fact],
                TheoryLemmaKind::StringLengthLemma,
            )),
            StringLengthFactProvenance::FromRoot { root, or_term } => {
                let lemma = candidate.add_theory_lemma_with_kind(
                    "STRINGS",
                    vec![or_term],
                    TheoryLemmaKind::StringLengthLemma,
                );
                let negated_root = self.ctx.terms.mk_not_raw(root);
                let clausified = candidate.add_rule_step(
                    AletheRule::Or,
                    vec![negated_root, fact],
                    vec![lemma],
                    Vec::new(),
                );
                let assume = candidate.add_assume(root, None);
                Some(candidate.add_resolution(vec![fact], root, clausified, assume))
            }
            StringLengthFactProvenance::FromRootClause { root, kind } => {
                let negated_root = self.ctx.terms.mk_not_raw(root);
                let lemma =
                    candidate.add_theory_lemma_with_kind("STRINGS", vec![negated_root, fact], kind);
                let assume = candidate.add_assume(root, None);
                Some(candidate.add_resolution(vec![fact], root, lemma, assume))
            }
        }
    }

    /// The `str.len` lower bound implied by an authored `(str.in_re x R)`, or
    /// `None` when the CHECKER'S OWN minimum-length computation declines.
    ///
    /// The bound is `ay_proof::regex_min_length`'s value, not one this producer
    /// derives: the checker owns the regex semantics, and the emitted clause is
    /// kept only when `ay_proof::recognize_regex_length_lower_bound` — the exact
    /// precondition of the strict validator — already accepts it. A bound of
    /// zero is dropped because `str.len` non-negativity already supplies it.
    fn build_regex_length_lower_bound(&mut self, root: TermId) -> Option<TermId> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(root) else {
            return None;
        };
        if (name != "str.in_re" && name != "str.in.re") || args.len() != 2 {
            return None;
        }
        let (subject, regex) = (args[0], args[1]);
        let minimum = ay_proof::regex_min_length(&self.ctx.terms, regex)?;
        if minimum <= BigInt::from(0) {
            return None;
        }
        let bound = self.ctx.terms.mk_int(minimum);
        let length = self.string_length_of(subject);
        let fact = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [bound, length], Sort::Bool);
        let negated_root = self.ctx.terms.mk_not_raw(root);
        ay_proof::recognize_regex_length_lower_bound(&self.ctx.terms, &[negated_root, fact])
            .then_some(fact)
    }

    /// `(= (str.len (str.++ a…)) (+ (str.len a)…))` for a `str.++` term, or
    /// `None` when the checker's own matcher does not accept it.
    fn build_concat_length_sum(&mut self, concat: TermId) -> Option<TermId> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(concat) else {
            return None;
        };
        if name != "str.++" || args.len() < 2 {
            return None;
        }
        let args: Vec<TermId> = args.clone();
        let length_of_concat = self.string_length_of(concat);
        let parts: Vec<TermId> = args.iter().map(|&arg| self.string_length_of(arg)).collect();
        // RAW `+` and `=`: the normalizing builders fold `(+ l l)` to `(* 2 l)`
        // and would leave a term the concat-sum schema (which matches summands
        // against operands as a multiset of `str.len` applications) rejects.
        let sum = self.ctx.terms.mk_app(Symbol::named("+"), parts, Sort::Int);
        let fact = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [length_of_concat, sum], Sort::Bool);
        ay_proof::recognize_string_length_lemma(&self.ctx.terms, &[fact]).then_some(fact)
    }

    /// `(= (str.len "abc") 3)` for a string constant, or `None`.
    fn build_constant_length(&mut self, constant: TermId) -> Option<TermId> {
        let TermData::Const(Constant::String(literal)) = self.ctx.terms.get(constant) else {
            return None;
        };
        let length = BigInt::from(literal.chars().count());
        let length_of_constant = self.string_length_of(constant);
        let value = self.ctx.terms.mk_int(length);
        let fact =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [length_of_constant, value], Sort::Bool);
        ay_proof::recognize_string_length_lemma(&self.ctx.terms, &[fact]).then_some(fact)
    }

    /// `(<= 0 (str.len x))` for a string-sorted term, or `None`.
    fn build_length_non_negativity(&mut self, subject: TermId) -> Option<TermId> {
        if self.ctx.terms.sort(subject) != &Sort::String {
            return None;
        }
        let length = self.string_length_of(subject);
        let zero = self.ctx.terms.mk_int(BigInt::from(0));
        let fact = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [zero, length], Sort::Bool);
        ay_proof::recognize_string_length_lemma(&self.ctx.terms, &[fact]).then_some(fact)
    }

    /// The equal-length consequence of an authored `(= left right)` over
    /// strings, as `(fact, (or (not root) fact))`, or `None`.
    ///
    /// When one side is a string constant the consequence is stated against its
    /// literal length, which keeps the arithmetic closed over one fewer opaque
    /// atom; otherwise it is the symmetric `str.len` equality.
    fn build_equal_length_congruence(
        &mut self,
        root: TermId,
        left: TermId,
        right: TermId,
    ) -> Option<(TermId, TermId)> {
        let left_constant_length = Self::string_constant_length(&self.ctx.terms, left);
        let right_constant_length = Self::string_constant_length(&self.ctx.terms, right);
        let fact = match (left_constant_length, right_constant_length) {
            (Some(length), _) => {
                let length_of_right = self.string_length_of(right);
                let value = self.ctx.terms.mk_int(length);
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [length_of_right, value], Sort::Bool)
            }
            (_, Some(length)) => {
                let length_of_left = self.string_length_of(left);
                let value = self.ctx.terms.mk_int(length);
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [length_of_left, value], Sort::Bool)
            }
            (None, None) => {
                let length_of_left = self.string_length_of(left);
                let length_of_right = self.string_length_of(right);
                self.ctx.terms.mk_app(
                    Symbol::named("="),
                    [length_of_left, length_of_right],
                    Sort::Bool,
                )
            }
        };
        self.close_root_conditioned_fact(root, fact)
    }

    /// The length bound implied by an authored containment predicate, as
    /// `(fact, (or (not root) fact))`, or `None`.
    fn build_containment_length_bound(
        &mut self,
        root: TermId,
        contained: TermId,
        container: TermId,
    ) -> Option<(TermId, TermId)> {
        let length_of_contained = self.string_length_of(contained);
        let length_of_container = self.string_length_of(container);
        // `<=`, NOT the solver's `(>= container contained)`: the checker's
        // containment schema matches exactly `(<= len(contained) len(container))`.
        let fact = self.ctx.terms.mk_app(
            Symbol::named("<="),
            [length_of_contained, length_of_container],
            Sort::Bool,
        );
        self.close_root_conditioned_fact(root, fact)
    }

    /// Wrap `fact` as `(or (not root) fact)` and keep the pair only when the
    /// CHECKER'S OWN matcher accepts that disjunction as a length theorem.
    fn close_root_conditioned_fact(
        &mut self,
        root: TermId,
        fact: TermId,
    ) -> Option<(TermId, TermId)> {
        let negated_root = self.ctx.terms.mk_not_raw(root);
        let or_term = self
            .ctx
            .terms
            .mk_app(Symbol::named("or"), [negated_root, fact], Sort::Bool);
        ay_proof::recognize_string_length_lemma(&self.ctx.terms, &[or_term])
            .then_some((fact, or_term))
    }

    /// `(str.len t)` for a string-sorted `t`, interned raw.
    fn string_length_of(&mut self, term: TermId) -> TermId {
        self.ctx
            .terms
            .mk_app(Symbol::named("str.len"), [term], Sort::Int)
    }

    /// The code-point length of a string-constant term.
    fn string_constant_length(terms: &TermStore, term: TermId) -> Option<BigInt> {
        match terms.get(term) {
            TermData::Const(Constant::String(literal)) => {
                Some(BigInt::from(literal.chars().count()))
            }
            _ => None,
        }
    }

    /// Whether `term` is a binary arithmetic atom over Int/Real operands — the
    /// shape `la_generic` consumes, with uninterpreted subterms (`(str.len x)`)
    /// treated as opaque variables.
    fn is_arith_atom_local(terms: &TermStore, term: TermId) -> bool {
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            return false;
        };
        args.len() == 2
            && matches!(name.as_str(), "=" | "<" | "<=" | ">" | ">=")
            && args
                .iter()
                .all(|&arg| matches!(terms.sort(arg), Sort::Int | Sort::Real))
    }

    /// Walk the authored roots and collect the string-theory subterms the
    /// length-arithmetic reconstruction can build facts from.
    ///
    /// Returns `None` when the walk exceeds `visit_budget`, so an enormous
    /// problem declines cheaply instead of being traversed in full.
    fn collect_string_relevant_subterms(
        terms: &TermStore,
        roots: &[TermId],
        visit_budget: usize,
    ) -> Option<StringRelevantSubterms> {
        let mut found = StringRelevantSubterms::default();
        let mut stack: Vec<TermId> = roots.to_vec();
        // Membership only — never iterated — so the walk stays deterministic
        // and `found`'s order is fixed by the stack discipline alone.
        let mut visited: ay_core::kani_compat::DetHashSet<TermId> =
            ay_core::kani_compat::DetHashSet::default();
        let mut visits = 0_usize;

        while let Some(term) = stack.pop() {
            visits += 1;
            if visits > visit_budget {
                return None;
            }
            if !visited.insert(term) {
                continue;
            }

            if terms.sort(term) == &Sort::String {
                if !found.length_subjects.contains(&term) {
                    found.length_subjects.push(term);
                }
                if matches!(terms.get(term), TermData::Const(Constant::String(_)))
                    && !found.string_constants.contains(&term)
                {
                    found.string_constants.push(term);
                }
            }
            match terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    match (name.as_str(), args.len()) {
                        ("str.++", n) if n >= 2 => {
                            if !found.concats.contains(&term) {
                                found.concats.push(term);
                            }
                        }
                        // (contained, container) per SMT-LIB argument order.
                        ("str.contains", 2) => found.containments.push((term, args[1], args[0])),
                        ("str.prefixof" | "str.suffixof", 2) => {
                            found.containments.push((term, args[0], args[1]));
                        }
                        ("=", 2) if terms.sort(args[0]) == &Sort::String => {
                            found.string_equalities.push((term, args[0], args[1]));
                        }
                        _ => {}
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.push(*condition);
                    stack.push(*then_branch);
                    stack.push(*else_branch);
                }
                _ => {}
            }
        }
        Some(found)
    }

    /// Rebuild a CONGRUENCE VALUE-CONFLICT refutation directly from exact
    /// authored roots (#trust-count→0, the UFLIA `f(p)=u, f(q)=v, p=q` shape).
    ///
    /// The problem asserts two values for the same function symbol at
    /// arguments that an authored equality identifies:
    ///
    /// ```text
    /// (assert (= (cur bx) 1))
    /// (assert (= (cur by) 2))
    /// (assert (= bx by))
    /// ```
    ///
    /// `bx = by` forces `cur(bx) = cur(by)` by congruence, and `1 = 2` is then
    /// arithmetically infeasible. AY decides this every time, but the EUF lane
    /// reports the conflict as ONE clause over the three authored literals and
    /// labels it `Generic` — `euf.rs`'s documented "derived array/EUF
    /// consequences remain honest Generic lemmas until an explicit primitive
    /// proof expansion is available". Strict mode has no validator for
    /// `Generic`, discharging that clause IS re-proving the problem so the
    /// deferred-trust rescue cannot help either, and the mandatory publication
    /// gate correctly turned a correct `unsat` into `unknown`:
    ///
    /// ```text
    /// strict UNSAT proof validation failed: step t3 uses unsupported theory
    /// lemma kind Generic in strict mode; deferred-trust discharge failed: ...
    /// ```
    ///
    /// THE FIX IS A DERIVATION, NOT A RELAXATION. Both halves of the conflict
    /// already have strict validators, so the refutation is emitted as the two
    /// primitive rules the `Generic` label was standing in for:
    ///
    /// ```text
    /// (assume h0 (= (cur bx) 1))
    /// (assume h1 (= (cur by) 2))
    /// (assume h2 (= bx by))
    /// (step c0 (cl (not (= bx by)) (= (cur bx) (cur by))) :rule eq_congruent)
    /// (step c1 (cl (= (cur bx) (cur by))) :rule resolution :premises (c0 h2))
    /// (step f0 (cl (not (= (cur bx) 1)) (not (= (cur by) 2))
    ///               (not (= (cur bx) (cur by)))) :rule la_generic)
    /// (step f1 (cl (not (= (cur by) 2)) (not (= (cur bx) (cur by))))
    ///          :rule resolution :premises (f0 h0))
    /// (step f2 (cl (not (= (cur bx) (cur by)))) :rule resolution :premises (f1 h1))
    /// (step f3 (cl) :rule resolution :premises (f2 c1))
    /// ```
    ///
    /// NOTHING IS TAKEN ON THE PRODUCER'S WORD. The congruence clause is
    /// admitted only as [`TheoryLemmaKind::EufCongruent`], whose validator
    /// (`ay-proof`'s `validate_euf_congruent`) independently re-derives that
    /// both sides are applications of the SAME symbol with the SAME arity and
    /// that there is exactly one premise equality per argument position
    /// connecting `f_args[i]` to `g_args[i]`. The value conflict is admitted
    /// only after `try_lra_farkas_reconstruction` — the same LRA solver the
    /// checker's `la_generic` validator replays — produces an actual Farkas
    /// certificate for it; a satisfiable value pair yields no certificate and
    /// the candidate is never built.
    ///
    /// Fail-closed at every step, mirroring
    /// [`Self::replace_with_exact_authored_store_permutation_refutation`]: it
    /// runs only on a proof the strict checker already rejects; every `assume`
    /// is an exact authored root; and the rebuilt proof must derive the empty
    /// clause, keep every reachable assume inside the authored scope, and pass
    /// `check_proof_strict_with_datatypes` before it replaces anything. If any
    /// of that fails the proof — and the `unknown` — is left exactly as found.
    fn replace_with_exact_authored_congruence_value_refutation(&mut self, proof: &mut Proof) {
        /// Authored-scope size beyond which this pass declines. The search
        /// below is quadratic in the authored equalities and then runs a
        /// bounded subset scan, and declining costs nothing but the `unknown`
        /// that is already being published.
        const MAX_AUTHORED_ROOTS: usize = 64;
        /// Cap on the Farkas premise subset scan (`sum_{i<=N} C(roots, i)`
        /// solver calls). The value conflict this closes needs two premises;
        /// the bound keeps a pathological authored scope from turning every
        /// rejected proof into an exponential search.
        const MAX_FARKAS_PREMISES: usize = 4;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }

        // Authored equalities, decoded once. Both the congruence argument
        // premises and the two value premises are drawn from this one list, so
        // nothing outside the authored scope can enter the rebuilt proof.
        let equalities: Vec<(TermId, TermId, TermId)> = authored
            .iter()
            .filter_map(|&root| {
                decode_eq_local(&self.ctx.terms, root).map(|(lhs, rhs)| (root, lhs, rhs))
            })
            .collect();

        for &(value_root_a, a_lhs, a_rhs) in &equalities {
            for (app_a, _value_a) in [(a_lhs, a_rhs), (a_rhs, a_lhs)] {
                let Some((symbol_a, args_a)) = as_app_local(&self.ctx.terms, app_a) else {
                    continue;
                };
                if args_a.is_empty() || ay_frontend::is_reserved_symbol(symbol_a.name()) {
                    continue;
                }
                for &(value_root_b, b_lhs, b_rhs) in &equalities {
                    if value_root_b == value_root_a {
                        continue;
                    }
                    for (app_b, _value_b) in [(b_lhs, b_rhs), (b_rhs, b_lhs)] {
                        if app_b == app_a {
                            continue;
                        }
                        let Some((symbol_b, args_b)) = as_app_local(&self.ctx.terms, app_b) else {
                            continue;
                        };
                        if symbol_b != symbol_a || args_b.len() != args_a.len() {
                            continue;
                        }
                        if self.ctx.terms.sort(app_a) != self.ctx.terms.sort(app_b) {
                            continue;
                        }

                        // One congruence premise per argument position, in
                        // position order — `validate_euf_congruent` requires
                        // exactly that and accepts either orientation, so the
                        // EXACT authored equality term is used where the
                        // arguments differ and a reflexivity step where they
                        // do not. A position with neither is not a congruence
                        // instance and the candidate is abandoned.
                        let mut argument_premises: Vec<(TermId, Option<TermId>)> =
                            Vec::with_capacity(args_a.len());
                        let mut positions_matched = true;
                        for (&arg_a, &arg_b) in args_a.iter().zip(args_b.iter()) {
                            if arg_a == arg_b {
                                let reflexive = self.ctx.terms.mk_app(
                                    Symbol::named("="),
                                    [arg_a, arg_b],
                                    Sort::Bool,
                                );
                                argument_premises.push((reflexive, None));
                                continue;
                            }
                            let authored_equality = equalities.iter().find(|&&(_, lhs, rhs)| {
                                (lhs == arg_a && rhs == arg_b) || (lhs == arg_b && rhs == arg_a)
                            });
                            let Some(&(equality_root, _, _)) = authored_equality else {
                                positions_matched = false;
                                break;
                            };
                            argument_premises.push((equality_root, Some(equality_root)));
                        }
                        if !positions_matched {
                            continue;
                        }

                        let congruence_conclusion =
                            self.ctx
                                .terms
                                .mk_app(Symbol::named("="), [app_a, app_b], Sort::Bool);
                        let mut congruence_clause: Vec<TermId> = argument_premises
                            .iter()
                            .map(|&(equality, _)| self.ctx.terms.mk_not_raw(equality))
                            .collect();
                        congruence_clause.push(congruence_conclusion);

                        // The value conflict. `try_lra_farkas_reconstruction`
                        // is the decision procedure here: it re-runs the LRA
                        // solver over the candidate clause's literals and
                        // returns a certificate only when their conjunction is
                        // genuinely infeasible. No schema is duplicated here.
                        let negated_conclusion = self.ctx.terms.mk_not_raw(congruence_conclusion);
                        let Some((farkas_clause, farkas, farkas_kind, farkas_premises)) = self
                            .search_authored_farkas_conflict(
                                &[negated_conclusion],
                                &authored,
                                MAX_FARKAS_PREMISES,
                            )
                        else {
                            continue;
                        };

                        let mut candidate = Proof::new();
                        let mut assumed: Vec<(TermId, ProofId)> = Vec::new();
                        let assume_authored = |candidate: &mut Proof,
                                               assumed: &mut Vec<(TermId, ProofId)>,
                                               root: TermId|
                         -> ProofId {
                            if let Some(&(_, id)) = assumed.iter().find(|&&(term, _)| term == root)
                            {
                                return id;
                            }
                            let id = candidate.add_assume(root, None);
                            assumed.push((root, id));
                            id
                        };

                        // Congruence, then discharge one argument premise at a
                        // time against its exact authored root (or against a
                        // checked reflexivity step for a shared argument).
                        let mut current = candidate.add_theory_lemma_with_kind(
                            "EUF",
                            congruence_clause.clone(),
                            TheoryLemmaKind::EufCongruent,
                        );
                        let mut residual = congruence_clause.clone();
                        for &(equality, authored_root) in &argument_premises {
                            let negated = self.ctx.terms.mk_not_raw(equality);
                            residual.retain(|&literal| literal != negated);
                            let unit = match authored_root {
                                Some(root) => assume_authored(&mut candidate, &mut assumed, root),
                                None => candidate.add_rule_step(
                                    AletheRule::EqReflexive,
                                    vec![equality],
                                    Vec::new(),
                                    Vec::new(),
                                ),
                            };
                            current =
                                candidate.add_resolution(residual.clone(), equality, current, unit);
                        }
                        let congruence_unit = current;

                        // The Farkas lemma, then discharge each of its authored
                        // premises the same way, leaving the single negated
                        // congruence conclusion to resolve against.
                        let mut current = candidate.add_theory_lemma_with_farkas_and_kind(
                            "LRA",
                            farkas_clause.clone(),
                            farkas,
                            farkas_kind,
                        );
                        let mut residual = farkas_clause.clone();
                        for &root in &farkas_premises {
                            let negated = Self::negated_root_literal(&mut self.ctx.terms, root);
                            residual.retain(|&literal| literal != negated);
                            let unit = assume_authored(&mut candidate, &mut assumed, root);
                            current =
                                candidate.add_resolution(residual.clone(), root, current, unit);
                        }
                        candidate.add_resolution(
                            Vec::new(),
                            congruence_conclusion,
                            current,
                            congruence_unit,
                        );

                        if ay_proof::validate_reachable_assumes_in_problem_scope(
                            &candidate, &authored,
                        )
                        .is_ok()
                            && Self::proof_derives_empty_clause(&candidate)
                            && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                        {
                            *proof = candidate;
                            return;
                        }
                    }
                }
            }
        }
    }

    /// The clause literal that an authored root discharges by resolution.
    ///
    /// An authored `(not X)` is refuted by the literal `X`; anything else by
    /// its negation. Keeping this in one place is what lets the resolution
    /// chains above stay orientation-agnostic.
    fn negated_root_literal(terms: &mut TermStore, root: TermId) -> TermId {
        match terms.get(root) {
            TermData::Not(inner) => *inner,
            _ => terms.mk_not_raw(root),
        }
    }

    /// Find a minimal authored premise set that, together with `trailing`,
    /// forms an arithmetically infeasible literal conjunction, plus the Farkas
    /// certificate that proves it.
    ///
    /// The returned clause is `(cl negate(r_1) … negate(r_k) trailing…)`, which
    /// is exactly what `la_generic`'s strict validator replays. Subsets are
    /// tried by increasing cardinality so the emitted lemma carries no
    /// zero-coefficient baggage (the same reason
    /// [`Self::replace_with_exact_authored_affine_euf_refutation`]'s
    /// `derive_affine_literal` prefers small premise sets).
    ///
    /// The infeasibility decision is entirely
    /// `proof_farkas::try_lra_farkas_reconstruction`'s: this function only
    /// enumerates candidate premise sets and never concludes anything about a
    /// clause the solver declined. It is also the only expensive thing here, so
    /// the scan is bounded on all three axes (roots, cardinality, calls) and
    /// declining simply leaves the verdict the `unknown` it already was.
    fn search_authored_farkas_conflict(
        &mut self,
        trailing: &[TermId],
        authored: &[TermId],
        max_premises: usize,
    ) -> Option<(Vec<TermId>, FarkasAnnotation, TheoryLemmaKind, Vec<TermId>)> {
        /// Cap on the roots entering the subset scan, so the `C(roots, k)`
        /// enumeration below stays bounded on a large authored scope.
        const MAX_SCANNED_ROOTS: usize = 12;
        /// Hard cap on LRA solver calls per search. This runs on proofs the
        /// strict checker rejected, which is most of them on a mixed suite, so
        /// the worst case has to be bounded independently of the scope shape.
        const MAX_FARKAS_CALLS: usize = 256;

        let roots: Vec<TermId> = authored
            .iter()
            .copied()
            .filter(|root| !trailing.contains(root))
            .take(MAX_SCANNED_ROOTS)
            .collect();
        let limit = 1_u32.checked_shl(roots.len() as u32)?;
        let mut calls = 0_usize;
        // Cardinality 0 is the ground case: `trailing` alone is infeasible when
        // negated, so the lemma needs no premises at all (a ground-true bound
        // such as `(<= 0 1)`).
        for cardinality in 0..=max_premises.min(roots.len()) {
            for mask in 0_u32..limit {
                if mask.count_ones() as usize != cardinality {
                    continue;
                }
                let selected: Vec<TermId> = roots
                    .iter()
                    .enumerate()
                    .filter_map(|(index, &root)| ((mask & (1_u32 << index)) != 0).then_some(root))
                    .collect();
                let mut clause: Vec<TermId> = selected
                    .iter()
                    .map(|&root| Self::negated_root_literal(&mut self.ctx.terms, root))
                    .collect();
                clause.extend_from_slice(trailing);
                calls += 1;
                if calls > MAX_FARKAS_CALLS {
                    return None;
                }
                let mut farkas = None;
                let mut kind = TheoryLemmaKind::Generic;
                if !super::proof_farkas::try_lra_farkas_reconstruction(
                    &self.ctx.terms,
                    &clause,
                    &mut farkas,
                    &mut kind,
                ) {
                    continue;
                }
                let farkas = farkas?;
                // `try_lra_farkas_reconstruction` already narrows a trust-kind
                // inference to `LraFarkas`; anything else it returns is a
                // strict-validated arithmetic kind for this exact clause. A
                // residual trust kind would be a certificate with no validator,
                // so it is refused here rather than emitted.
                if kind.is_trust() {
                    continue;
                }
                return Some((clause, farkas, kind, selected));
            }
        }
        None
    }

    /// Whether a sticky datatype-member identity is still live under `surface`.
    fn live_datatype_member_has_surface(&self, identity: &str, surface: &str) -> bool {
        self.ctx.is_live_datatype_member_identity(identity)
            && self.ctx.dt_surface_name(identity).unwrap_or(identity) == surface
    }

    /// Datatype selector-projection collapse (#trust-count→0). The analogue of
    /// `promote_array_row_collapse` for datatypes: an assertion
    /// `(not (= (sel_i (C a_0 .. a_n)) a_i))` folds to `false` at elaboration
    /// (the selector projects field `i` of the constructor application), so the
    /// UNSAT proof degenerates to a single empty-clause `trust` step. Reconstruct
    /// the refutation FROM THE PARSED ASSERTION as
    ///   assume      (not (= (sel_i (C a_0 .. a_n)) a_i))   the input hypothesis
    ///   lemma       (= (sel_i (C a_0 .. a_n)) a_i)          strict-validated
    ///   resolution  □
    /// The constructor application and raw selector term the fold erased are
    /// rebuilt via `mk_app` (no fold) at the constructor's / selector's declared
    /// return sorts. SOUND + fail-closed: the candidate lemma is gated through
    /// the strict checker's OWN recognizer (`recognize_datatype_selector_project`,
    /// keyed on the constructor→selector registry), so a reconstruction is
    /// committed only when the strict checker will independently re-validate it;
    /// any mismatch (wrong selector, wrong field, unresolved symbol) leaves the
    /// trust step untouched.
    fn promote_dt_selector_collapse(&mut self, proof: &mut Proof) {
        if !Self::proof_needs_schema_collapse_reconstruction(proof) {
            return;
        }
        // Snapshot the registry + parsed assertions before mutating `terms`.
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        let selectors: Vec<(String, Vec<String>)> = self
            .ctx
            .ctor_selectors_iter()
            .map(|(ctor, sels)| (ctor.clone(), sels.clone()))
            .collect();
        if selectors.is_empty() {
            return;
        }
        for asrt in &parsed {
            let Some((ctor, arg_syms, sel, val)) = match_dt_selector_negation(asrt) else {
                continue;
            };
            let Some(arg_ids) = arg_syms
                .iter()
                .map(|s| self.ctx.terms.lookup(s))
                .collect::<Option<Vec<TermId>>>()
            else {
                continue;
            };
            let Some(val_id) = self.ctx.terms.lookup(val) else {
                continue;
            };
            let arg_sorts: Vec<Sort> = arg_ids
                .iter()
                .map(|arg| self.ctx.terms.sort(*arg).clone())
                .collect();
            let val_sort = self.ctx.terms.sort(val_id).clone();

            // Parsed assertions carry surface member names, while the live
            // declaration may be a parametric instance or a scoped
            // reincarnation with a private core identity. Resolve through the
            // exact constructor→selector registry and full signatures; never
            // rebuild a surface App that could denote an older declaration.
            let mut resolved: Option<(String, Sort, String, Sort)> = None;
            let mut ambiguous = false;
            for (ctor_identity, selector_identities) in &selectors {
                if !self.live_datatype_member_has_surface(ctor_identity, ctor) {
                    continue;
                }
                let Some(ctor_info) = self.ctx.exact_datatype_member_info(ctor_identity) else {
                    continue;
                };
                if ctor_info.arg_sorts != arg_sorts {
                    continue;
                }
                for selector_identity in selector_identities {
                    if !self.live_datatype_member_has_surface(selector_identity, sel) {
                        continue;
                    }
                    let Some(selector_info) =
                        self.ctx.exact_datatype_member_info(selector_identity)
                    else {
                        continue;
                    };
                    if selector_info.arg_sorts != std::slice::from_ref(&ctor_info.sort)
                        || selector_info.sort != val_sort
                    {
                        continue;
                    }
                    let candidate = (
                        ctor_identity.clone(),
                        ctor_info.sort.clone(),
                        selector_identity.clone(),
                        selector_info.sort.clone(),
                    );
                    if resolved.replace(candidate).is_some() {
                        ambiguous = true;
                    }
                }
            }
            let Some((ctor_identity, ctor_sort, selector_identity, sel_sort)) = resolved else {
                continue;
            };
            if ambiguous {
                continue;
            }
            // Rebuild the constructor application and the raw selector term (the
            // ROW-of-datatypes fold erased the latter); `mk_app` interns raw.
            let ctor_term =
                self.ctx
                    .terms
                    .mk_app(Symbol::named(&ctor_identity), arg_ids, ctor_sort);
            let sel_term =
                self.ctx
                    .terms
                    .mk_app(Symbol::named(&selector_identity), [ctor_term], sel_sort);
            let eq_t = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [sel_term, val_id], Sort::Bool);
            // Gate on the checker's own recognizer: commit only if strict mode
            // will re-validate this exact lemma (no classifier/checker drift).
            if !ay_proof::recognize_datatype_selector_project(&self.ctx.terms, &[eq_t], &selectors)
            {
                continue;
            }
            let neg_t = self.ctx.terms.mk_not_raw(eq_t);

            self.record_rebuilt_authored_proof_premise(neg_t);
            proof.steps.clear();
            proof.named_steps.clear();
            let assume_id = proof.add_assume(neg_t, None);
            let lemma_id = proof.add_theory_lemma_with_kind(
                "datatype",
                vec![eq_t],
                TheoryLemmaKind::DatatypeSelectorProject,
            );
            proof.add_resolution(vec![], eq_t, assume_id, lemma_id);
            return;
        }
    }

    /// Run the three reflexive-collapse promoters in their proof-critical order.
    ///
    /// Self-equality collapse (#trust-count→0, ANY width): a `(not (= X X))`
    /// assertion with SYNTACTICALLY IDENTICAL sides (the machine-lowering-vs-IR
    /// reconstruction obligations whose two encoders coincide, e.g.
    /// `Iadd→AddRR` = `bvadd==bvadd`) folds to `false`, degenerating to the
    /// `:rule false` collapse. Reconstruct assume + `refl` + resolution — refl
    /// proves identical-sides equality at ANY sort/width, so it covers the
    /// 32/64-bit ALU family the bounded `BvBitBlast` pass below cannot. SOUND +
    /// fail-closed (only fires when the rebuilt sides are the SAME hash-consed
    /// TermId). Runs FIRST so identical-sides obligations get the width-agnostic
    /// refl proof; genuinely-distinct sides fall through to the bounded pass.
    ///
    /// `(and P (not (= P true)))` contradiction collapse (#trust-count→0, ANY
    /// width): the external-codegen dom-bounds obligation family (a constant bounds
    /// check dominated by an IDENTICAL one) renders as `P ∧ ¬P` and folds to
    /// `false`, degenerating to the Carcara-rejected `:rule false` collapse.
    /// Reconstruct assume + and_pos/not_equiv2/true + resolutions — pure
    /// propositional rules, so ANY faithfully-rebuildable BV comparison atom
    /// `P` is covered at any width. SOUND + fail-closed; see method.
    ///
    /// `(and P (not (= X X)))` self-equality collapse (#trust-count→0, ANY
    /// sort): the external-codegen GUARDED-division obligation family carries its
    /// `b ≠ 0` guard as a first conjunct, so neither the top-level
    /// self-equality pass (needs a bare `(not (= X X))`) nor the dom-bounds
    /// pass above (needs `(not (= P true))`) matches, and the refutation
    /// degenerated to the `hole`-rendering rescue. Reconstruct assume +
    /// and_pos + refl + resolutions — propositional rules plus reflexivity,
    /// so the guard is carried verbatim and never interpreted. SOUND +
    /// fail-closed; see method.
    fn promote_reflexive_collapse_family(&mut self, proof: &mut Proof) {
        self.promote_self_eq_collapse(proof);
        self.promote_and_true_eq_contradiction_collapse(proof);
        self.promote_and_self_eq_contradiction_collapse(proof);
    }

    /// Bitvector identity collapse (#trust-count→0). A small-width BV assertion
    /// `(not (= (OP a b) c))` whose equality is a bounded BV tautology (e.g.
    /// `bvand x x = x`) folds to `false` during elaboration, degenerating the
    /// UNSAT proof to a single empty-clause `trust` step. Reconstruct the
    /// refutation FROM THE PARSED ASSERTION as
    ///   assume      (not (= (OP a b) c))      the input hypothesis
    ///   lemma       (= (OP a b) c)             strict-validated
    ///   resolution  □
    /// The lemma is a `BvBitBlast` step, which the strict checker validates by
    /// EXHAUSTIVE bounded evaluation (`validate_bounded_clause_semantics`: every
    /// assignment over the small-width vars must satisfy the clause) — a genuine
    /// bounded decision procedure, not a syntactic stamp.
    ///
    /// SOUND + fail-closed on three independent gates: (1) the operand/value are
    /// all symbols resolved via `lookup`; (2) a FAITHFULNESS guard — the rebuilt
    /// `(OP a b)` term must be the raw application (if `mk_app` folded it, the
    /// `assume` would no longer match the real input, so we skip); (3) the lemma
    /// is gated through the checker's own `recognize_bv_bitblast`, so it is
    /// committed only when strict mode will re-validate it by exhaustive
    /// evaluation. Any miss leaves the trust step untouched.
    /// Self-equality collapse (#trust-count→0, ANY width). A `(not (= X X))`
    /// assertion whose two sides are SYNTACTICALLY IDENTICAL — the external-codegen
    /// machine-lowering-vs-IR reconstruction obligations whose two encoders
    /// coincide (e.g. `Iadd→AddRR` reduces both sides to `bvadd`) — folds to
    /// `false` at elaboration, degenerating the UNSAT proof to the `:rule false`
    /// collapse (which Carcara rejects: its `false` rule wants the literal
    /// constant, not `(not (= X X))`). Reconstruct the Carcara-checkable
    /// refutation FROM THE PARSED ASSERTION:
    ///   assume      (not (= X X))
    ///   step        (= X X)          :rule refl      (reflexivity)
    ///   resolution  □
    /// Unlike [`Self::promote_bv_identity_collapse`] (gated on the bounded
    /// `BvBitBlast` recognizer, width ≤ 4), `refl` proves identical-sides
    /// equality at ANY sort/width, so this covers the 32/64-bit ALU reconstruction
    /// family. SOUND + fail-closed: only fires when the faithfully-rebuilt sides
    /// are the SAME hash-consed `TermId` (genuine syntactic reflexivity, exactly
    /// what Alethe `refl` certifies); a non-identical pair leaves the trust step
    /// for the other passes.
    fn promote_self_eq_collapse(&mut self, proof: &mut Proof) {
        if !Self::proof_is_single_empty_trust(proof) {
            return;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        for asrt in &parsed {
            let Some((lhs, rhs)) = match_eq_negation(asrt) else {
                continue;
            };
            // Faithfully rebuild both sides (same 1:1 structural translation the
            // BV pass uses), then require they are the IDENTICAL hash-consed term.
            let (Some(l_id), Some(r_id)) = (
                build_bv_pterm(&mut self.ctx.terms, lhs),
                build_bv_pterm(&mut self.ctx.terms, rhs),
            ) else {
                continue;
            };
            if l_id != r_id {
                continue;
            }
            let eq_t = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [l_id, r_id], Sort::Bool);
            let neg_t = self.ctx.terms.mk_not_raw(eq_t);
            // Every printed term must survive the printer's surface-override
            // table; see `rebuilt_terms_print_faithfully`.
            if !self.rebuilt_terms_print_faithfully(&[neg_t, eq_t]) {
                continue;
            }

            proof.steps.clear();
            proof.named_steps.clear();
            let assume_id = proof.add_assume(neg_t, None);
            let refl_id = proof.add_step(ProofStep::Step {
                rule: AletheRule::Refl,
                clause: vec![eq_t],
                premises: vec![],
                args: vec![],
            });
            proof.add_resolution(vec![], eq_t, assume_id, refl_id);
            return;
        }
    }

    /// `(and P (not (= P true)))` contradiction collapse (#trust-count→0, ANY
    /// width). The external-codegen dom-bounds obligation family
    /// (`bridge_bounds_check_dom_ult_K_implies_ult_K`: a constant bounds check
    /// dominated by an IDENTICAL check) renders as
    /// `(assert (and P (not (= P true))))` with `P` a BV comparison atom —
    /// `P ∧ ¬P` — which folds to `false` at elaboration, degenerating the
    /// UNSAT proof to the Carcara-rejected `:rule false` collapse (same defect
    /// class as [`Self::promote_self_eq_collapse`]). Reconstruct the
    /// Carcara-checkable refutation FROM THE PARSED ASSERTION:
    ///   assume      A = (and P (not (= P true)))
    ///   and_pos(0)  (cl (not A) P)
    ///   and_pos(1)  (cl (not A) (not (= P true)))
    ///   resolution  (cl P)                        ; pivot A
    ///   resolution  (cl (not (= P true)))         ; pivot A
    ///   not_equiv2  (cl (not P) (not true))
    ///   resolution  (cl (not true))               ; pivot P
    ///   true        (cl true)
    ///   resolution  □                             ; pivot true
    /// SOUND + fail-closed: both `P` occurrences are faithfully rebuilt
    /// ([`build_bv_atom_pterm`], raw `mk_app` + per-node fold guard) and must
    /// be the SAME hash-consed `TermId`; every connective rebuild is
    /// fold-guarded so the `assume` mirrors the real input assertion. A
    /// non-matching shape leaves the trust step for the other passes.
    fn promote_and_true_eq_contradiction_collapse(&mut self, proof: &mut Proof) {
        if !Self::proof_is_single_empty_trust(proof) {
            return;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        for asrt in &parsed {
            let Some((p, p_again)) = match_and_true_eq_contradiction(asrt) else {
                continue;
            };
            let (Some(p_id), Some(p_again_id)) = (
                build_bv_atom_pterm(&mut self.ctx.terms, p),
                build_bv_atom_pterm(&mut self.ctx.terms, p_again),
            ) else {
                continue;
            };
            if p_id != p_again_id {
                continue;
            }
            let true_t = self.ctx.terms.true_term();
            let eq_t = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), vec![p_id, true_t], Sort::Bool);
            if !matches!(
                self.ctx.terms.get(eq_t),
                TermData::App(sym, a) if sym.name() == "=" && a.as_slice() == [p_id, true_t]
            ) {
                continue;
            }
            let not_eq_t = self.ctx.terms.mk_not_raw(eq_t);
            let and_t =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("and"), vec![p_id, not_eq_t], Sort::Bool);
            if !matches!(
                self.ctx.terms.get(and_t),
                TermData::App(sym, a) if sym.name() == "and" && a.as_slice() == [p_id, not_eq_t]
            ) {
                continue;
            }
            let not_and_t = self.ctx.terms.mk_not_raw(and_t);
            let not_p_t = self.ctx.terms.mk_not_raw(p_id);
            let not_true_t = self.ctx.terms.mk_not_raw(true_t);

            proof.steps.clear();
            proof.named_steps.clear();
            let assume_id = proof.add_assume(and_t, None);
            let and_pos_p =
                proof.add_rule_step(AletheRule::AndPos(0), vec![not_and_t, p_id], vec![], vec![]);
            let and_pos_neq = proof.add_rule_step(
                AletheRule::AndPos(1),
                vec![not_and_t, not_eq_t],
                vec![],
                vec![],
            );
            let cl_p = proof.add_resolution(vec![p_id], and_t, and_pos_p, assume_id);
            let cl_neq = proof.add_resolution(vec![not_eq_t], and_t, and_pos_neq, assume_id);
            let cl_notp_nottrue = proof.add_rule_step(
                AletheRule::NotEquiv2,
                vec![not_p_t, not_true_t],
                vec![cl_neq],
                vec![],
            );
            let cl_nottrue = proof.add_resolution(vec![not_true_t], p_id, cl_notp_nottrue, cl_p);
            let cl_true = proof.add_rule_step(AletheRule::True, vec![true_t], vec![], vec![]);
            proof.add_resolution(vec![], true_t, cl_nottrue, cl_true);
            return;
        }
    }

    /// Fail-closed PRINT-FIDELITY gate for the raw-rebuilt terms of a candidate.
    ///
    /// A collapse promoter reconstructs the problem's assertion with raw
    /// constructors precisely because elaboration FOLDED it. The Alethe printer
    /// however also consults the surface-override table, and
    /// `collect_subterm_surface_overrides` keys that table on the ELABORATED
    /// subterm: when a child folded, the child's authored spelling is attached
    /// to the folded RESULT. A raw rebuild that legitimately uses that result
    /// in an UNFOLDED position then prints with the wrong spelling, the
    /// `assume` no longer matches the problem, and an external checker reports
    /// `invalid` — strictly worse than the honest `hole` the promoter replaced,
    /// because no rule can run on a document whose premise is not the problem's.
    ///
    /// Measured instance (QF_ABV):
    /// `(not (= (select (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) d) i d) i) …))`.
    /// `mk_select`'s read-over-write folds that read straight to `d`, so the
    /// override table says "print `d` as `(select (store …) i)`" — and every
    /// `d` in the rebuilt term (the const-array fill AND the stored value) came
    /// back out as the whole read expression.
    ///
    /// The check is a genuine ROUND TRIP: render each term exactly as export
    /// will (same override table), re-parse that text, rebuild it with the same
    /// fold-guarded builder, and require the identical hash-consed `TermId`.
    /// A faithful spelling difference passes — a BV literal printed `#b…` where
    /// the source wrote `(_ bvN W)` re-parses to the same constant — while a
    /// SUBSTITUTED subterm cannot. Anything that fails to render, re-parse or
    /// rebuild is declined, so the promoter leaves the honest `hole` in place.
    ///
    /// Callers pass every term the candidate proof will PRINT, not just the
    /// `assume`: an override can be faithful on the premise and unfaithful on a
    /// term that appears only in a later clause, and one bad literal is enough
    /// to make the document `invalid`.
    ///
    /// SCOPE — deliberately limited to candidates carrying ARRAY content, the
    /// fragment these rebuilders newly admit. The hazard is worst there
    /// (`mk_select`'s read-over-write collapses an entire read to a leaf, so the
    /// misattributed spelling can replace any occurrence of that leaf), and
    /// restricting it keeps every pre-existing pure-BV promotion byte-identical.
    /// The same defect DOES exist on the BV lane — `(not (= (bvand x x) x))` at
    /// width 4 publishes an `assume` of `(not (= (bvand (bvand x x) (bvand x x))
    /// (bvand x x)))`, which carcara rejects — but that is a pre-existing
    /// printer defect the in-tree suite deliberately isolates behind
    /// `published_assumption_scope` (see
    /// `tests/group_proofs/carcara_external_check.rs`), and repairing it is a
    /// separate change from admitting the array fragment. Widening this gate to
    /// the BV lane without that repair only converts those `invalid` documents
    /// into `hole`s and breaks the tests that pin them.
    fn rebuilt_terms_print_faithfully(&mut self, terms: &[TermId]) -> bool {
        if !terms
            .iter()
            .any(|&term| term_contains_array(&self.ctx.terms, term))
        {
            return true;
        }
        let overrides = self.proof_export_term_overrides().unwrap_or_default();
        terms.iter().all(|&term| {
            let rendered =
                ay_proof::format_term_alethe_with_overrides(&self.ctx.terms, term, &overrides);
            parse_rendered_assertion(&rendered)
                .and_then(|reparsed| build_qfbv_pterm(&mut self.ctx.terms, &reparsed))
                == Some(term)
        })
    }

    /// `(and P (not (= X X)))` self-equality collapse (#trust-count→0, ANY
    /// sort). The external-codegen GUARDED-division obligation family
    /// (`bridge_udiv_remainder_*`: `a - (a / b) * b` lowered two ways under a
    /// `b ≠ 0` guard) renders as `(assert (and (not (= b 0)) (not (= X X))))`.
    /// The second conjunct alone is [`Self::promote_self_eq_collapse`]'s shape,
    /// but that pass requires a TOP-LEVEL `(not (= …))`, and
    /// [`Self::promote_and_true_eq_contradiction_collapse`] requires the second
    /// conjunct to be `(not (= P true))` — so neither matches and the whole
    /// (correct) refutation degenerated to the `hole`-rendering rescue.
    /// Reconstruct it FROM THE PARSED ASSERTION:
    ///   assume      A = (and P (not (= X X)))
    ///   and_pos(1)  (cl (not A) (not (= X X)))
    ///   resolution  (cl (not (= X X)))        ; pivot A
    ///   refl        (cl (= X X))
    ///   resolution  □                          ; pivot (= X X)
    /// Pure propositional rules plus `refl`, so the guard `P` is never
    /// interpreted — it is carried verbatim into the `assume` and dropped by
    /// `and_pos`, which is why this works at any width and needs no BV theory.
    ///
    /// SOUND + fail-closed: `P` and both `X` occurrences are faithfully rebuilt
    /// (raw `mk_app`/`mk_not_raw` with a per-node fold guard), the two `X`
    /// rebuilds must be the SAME hash-consed `TermId` (genuine syntactic
    /// reflexivity — exactly what Alethe `refl` certifies), and every
    /// reconstructed connective is re-read to confirm the store did not fold
    /// it, so the `assume` mirrors the real input assertion. Any mismatch
    /// leaves the proof untouched for the later passes.
    fn promote_and_self_eq_contradiction_collapse(&mut self, proof: &mut Proof) {
        if !Self::proof_is_single_empty_trust(proof) {
            return;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        for asrt in &parsed {
            let Some((side, lhs, rhs)) = match_and_self_eq_contradiction(asrt) else {
                continue;
            };
            let Some(side_id) = build_qfbv_pterm(&mut self.ctx.terms, side) else {
                continue;
            };
            if !matches!(self.ctx.terms.sort(side_id), Sort::Bool) {
                continue;
            }
            // Same faithful rebuild pair the self-equality passes use: the BV
            // fragment first, then the boolean layer for sides that need it.
            let (Some(l_id), Some(r_id)) = (
                build_bv_pterm(&mut self.ctx.terms, lhs)
                    .or_else(|| build_qfbv_pterm(&mut self.ctx.terms, lhs)),
                build_bv_pterm(&mut self.ctx.terms, rhs)
                    .or_else(|| build_qfbv_pterm(&mut self.ctx.terms, rhs)),
            ) else {
                continue;
            };
            if l_id != r_id {
                continue;
            }
            let eq_t = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [l_id, r_id], Sort::Bool);
            if !matches!(
                self.ctx.terms.get(eq_t),
                TermData::App(sym, a) if sym.name() == "=" && a.as_slice() == [l_id, r_id]
            ) {
                continue;
            }
            let not_eq_t = self.ctx.terms.mk_not_raw(eq_t);
            if !matches!(self.ctx.terms.get(not_eq_t), TermData::Not(inner) if *inner == eq_t) {
                continue;
            }
            let and_t =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("and"), vec![side_id, not_eq_t], Sort::Bool);
            if !matches!(
                self.ctx.terms.get(and_t),
                TermData::App(sym, a) if sym.name() == "and" && a.as_slice() == [side_id, not_eq_t]
            ) {
                continue;
            }
            let not_and_t = self.ctx.terms.mk_not_raw(and_t);
            if !matches!(self.ctx.terms.get(not_and_t), TermData::Not(inner) if *inner == and_t) {
                continue;
            }
            // Every printed term must survive the printer's surface-override
            // table; see `rebuilt_terms_print_faithfully`.
            if !self.rebuilt_terms_print_faithfully(&[and_t, not_and_t, not_eq_t, eq_t]) {
                continue;
            }

            proof.steps.clear();
            proof.named_steps.clear();
            let assume_id = proof.add_assume(and_t, None);
            let and_pos_neq = proof.add_rule_step(
                AletheRule::AndPos(1),
                vec![not_and_t, not_eq_t],
                vec![],
                vec![],
            );
            let cl_neq = proof.add_resolution(vec![not_eq_t], and_t, and_pos_neq, assume_id);
            let refl_id = proof.add_rule_step(AletheRule::Refl, vec![eq_t], vec![], vec![]);
            proof.add_resolution(vec![], eq_t, cl_neq, refl_id);
            self.record_rebuilt_authored_proof_premise(and_t);
            return;
        }
    }

    fn promote_bv_identity_collapse(&mut self, proof: &mut Proof) {
        if !Self::proof_needs_schema_collapse_reconstruction(proof) {
            return;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        for asrt in &parsed {
            let Some((lhs, rhs)) = match_eq_negation(asrt) else {
                continue;
            };
            // Faithfully rebuild both sides erased by the identity fold. `build_qfbv_pterm`
            // translates the frontend AST 1:1 (symbol→TermId, literal→`mk_bitvec`, op→raw
            // constructor) with a per-node faithfulness guard. Its Boolean layer covers BV-valued
            // `ite` nodes nested below concat/extract in code-generator obligations.
            let (Some(l_id), Some(r_id)) = (
                build_bv_pterm(&mut self.ctx.terms, lhs)
                    .or_else(|| build_qfbv_pterm(&mut self.ctx.terms, lhs)),
                build_bv_pterm(&mut self.ctx.terms, rhs)
                    .or_else(|| build_qfbv_pterm(&mut self.ctx.terms, rhs)),
            ) else {
                continue;
            };
            // Both sides must share one BV sort for `=` to be well-formed.
            if self.ctx.terms.sort(l_id) != self.ctx.terms.sort(r_id)
                || !matches!(self.ctx.terms.sort(l_id), Sort::BitVec(_))
            {
                continue;
            }
            let eq_t = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [l_id, r_id], Sort::Bool);
            let reflexive = l_id == r_id;
            let neg_t = self.ctx.terms.mk_not_raw(eq_t);
            // Every printed term must survive the printer's surface-override
            // table; see `rebuilt_terms_print_faithfully`.
            if !self.rebuilt_terms_print_faithfully(&[neg_t, eq_t]) {
                continue;
            }

            let mut candidate = Proof::new();
            let assume_id = candidate.add_assume(neg_t, None);
            let lemma_id = if reflexive {
                candidate.add_rule_step(AletheRule::EqReflexive, vec![eq_t], Vec::new(), Vec::new())
            } else if let Some(step) = add_bvand_commutative_congruence_proof(
                &mut self.ctx.terms,
                &mut candidate,
                l_id,
                r_id,
            ) {
                step
            } else if ay_proof::recognize_bv_bitblast(&self.ctx.terms, &[eq_t]) {
                candidate.add_theory_lemma_with_kind("bv", vec![eq_t], TheoryLemmaKind::BvBitBlast)
            } else {
                continue;
            };
            candidate.add_resolution(vec![], eq_t, assume_id, lemma_id);

            self.record_rebuilt_authored_proof_premise(neg_t);
            *proof = candidate;
            return;
        }
    }

    /// Linear-arithmetic identity collapse (#trust-count→0). An integer assertion
    /// `(not (= L R))` whose equality is a linear-arithmetic tautology — e.g.
    /// `(* x 0) = 0` or `(* x 1) = x` — folds to `false` during elaboration,
    /// degenerating the UNSAT proof to a single empty-clause `trust` step.
    /// Reconstruct the refutation FROM THE PARSED ASSERTION as
    ///   assume      (not (= L R))      the input hypothesis
    ///   lemma       (= L R)             strict-validated (LiaGeneric/LinearIdentity)
    ///   resolution  □
    /// The strict checker validates the lemma by confirming `L - R` is the
    /// identically-zero integer linear form (`validate_lia_linear_identity`).
    ///
    /// SOUND + fail-closed on the same gates as the BV pass: both sides rebuilt
    /// by the faithful recursive `build_int_pterm` (raw `mk_app`/`mk_int`, a
    /// per-node guard that the op did not fold), both `Int`-sorted, and the lemma
    /// gated through the checker's own `recognize_lia_linear_identity` before
    /// commit. Genuinely-nonlinear identities (`(* x y) = (* y x)`) fail the
    /// linear check and keep the trust step.
    fn promote_nia_linear_identity_collapse(&mut self, proof: &mut Proof) {
        if !Self::proof_needs_schema_collapse_reconstruction(proof) {
            return;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        for asrt in &parsed {
            let Some((lhs, rhs)) = match_eq_negation(asrt) else {
                continue;
            };
            let (Some(l_id), Some(r_id)) = (
                build_int_pterm(&mut self.ctx.terms, lhs),
                build_int_pterm(&mut self.ctx.terms, rhs),
            ) else {
                continue;
            };
            if !matches!(self.ctx.terms.sort(l_id), Sort::Int)
                || !matches!(self.ctx.terms.sort(r_id), Sort::Int)
            {
                continue;
            }
            let eq_t = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [l_id, r_id], Sort::Bool);
            if !ay_core::proof_validation::recognize_lia_linear_identity(&self.ctx.terms, &[eq_t]) {
                continue;
            }
            let neg_t = self.ctx.terms.mk_not_raw(eq_t);

            self.record_rebuilt_authored_proof_premise(neg_t);
            proof.steps.clear();
            proof.named_steps.clear();
            let assume_id = proof.add_assume(neg_t, None);
            let lemma_id = proof.add_step(ProofStep::TheoryLemma {
                theory: "LIA".to_string(),
                clause: vec![eq_t],
                // The strict checker validates via the `LinearIdentity` annotation
                // (`L - R ≡ 0`); the Alethe printer additionally requires a Farkas
                // coefficient per literal to render `lia_generic` (#8821), so
                // attach the trivial `[1]` for the single literal — purely for
                // rendering, mirroring the divisibility promotion.
                farkas: Some(FarkasAnnotation::new(vec![num_rational::Rational64::from(
                    1,
                )])),
                kind: TheoryLemmaKind::LiaGeneric,
                lia: Some(ay_core::LiaAnnotation::LinearIdentity),
            });
            proof.add_resolution(vec![], eq_t, assume_id, lemma_id);
            return;
        }
    }

    /// Reconstruct a strict proof for an authored impossible Euclidean
    /// remainder equality such as `(= (mod x 3) 4)`.
    ///
    /// The LIA division encoder can discover this contradiction while creating
    /// its quotient/remainder auxiliaries, before any checkable clause-level
    /// range certificate remains. The resulting proof retains either a direct
    /// empty `trust` or a trust-backed auxiliary/Farkas closure. Rebuild it as:
    ///
    /// ```text
    /// assume        (= (mod x d) r)
    /// lia_mod_range (not (= (mod x d) r))
    /// resolution    □
    /// ```
    ///
    /// Soundness is carried by three independent gates: the assertion is
    /// rebuilt structurally from the retained frontend AST; the checker-owned
    /// [`ay_core::proof_validation::recognize_lia_mod_range`] predicate accepts
    /// only constant `d != 0` and `r` outside `0 <= r < |d|`; and the complete
    /// candidate proof is replayed by the strict checker before replacement.
    /// Every unsupported shape retains the original trust step (fail-closed).
    fn promote_lia_mod_range_collapse(&mut self, proof: &mut Proof) {
        // The division rewrite can leave a multi-step terminal derivation whose
        // first leaf is still Trust (auxiliary range fact + authored equality +
        // Farkas closure), so this is deliberately not keyed only on the legacy
        // single-empty-trust shape. Do not replace an already certified proof.
        let has_untrusted_step = proof.steps.iter().any(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Trust | AletheRule::Hole,
                    ..
                }
            ) || matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust())
        });
        if !has_untrusted_step {
            return;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        for assertion in &parsed {
            let FrontendTerm::App(eq_name, eq_args) = assertion else {
                continue;
            };
            if eq_name != "=" || eq_args.len() != 2 {
                continue;
            }
            for (mod_position, remainder_position) in [(0usize, 1usize), (1, 0)] {
                let FrontendTerm::App(mod_name, mod_args) = &eq_args[mod_position] else {
                    continue;
                };
                if mod_name != "mod" || mod_args.len() != 2 {
                    continue;
                }
                let (Some(dividend), Some(divisor), Some(remainder)) = (
                    build_int_pterm(&mut self.ctx.terms, &mod_args[0]),
                    build_int_pterm(&mut self.ctx.terms, &mod_args[1]),
                    build_int_pterm(&mut self.ctx.terms, &eq_args[remainder_position]),
                ) else {
                    continue;
                };
                if ![dividend, divisor, remainder]
                    .iter()
                    .all(|&term| matches!(self.ctx.terms.sort(term), Sort::Int))
                {
                    continue;
                }

                let modulus =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("mod"), [dividend, divisor], Sort::Int);
                if !matches!(
                    self.ctx.terms.get(modulus),
                    TermData::App(symbol, args)
                        if symbol.name() == "mod" && args.as_slice() == [dividend, divisor]
                ) {
                    continue;
                }
                let equality_args = if mod_position == 0 {
                    [modulus, remainder]
                } else {
                    [remainder, modulus]
                };
                let equality = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), equality_args, Sort::Bool);
                if !matches!(
                    self.ctx.terms.get(equality),
                    TermData::App(symbol, args)
                        if symbol.name() == "=" && args.as_slice() == equality_args
                ) {
                    continue;
                }
                let disequality = self.ctx.terms.mk_not_raw(equality);
                if !ay_core::proof_validation::recognize_lia_mod_range(
                    &self.ctx.terms,
                    &[disequality],
                ) {
                    continue;
                }

                let mut candidate = Proof::new();
                let assumption = candidate.add_assume(equality, None);
                let theorem = candidate.add_theory_lemma_with_kind(
                    "LIA",
                    vec![disequality],
                    TheoryLemmaKind::LiaModRange,
                );
                candidate.add_resolution(Vec::new(), equality, assumption, theorem);

                self.record_rebuilt_authored_proof_premise(equality);
                let Ok(quality) = self.check_proof_strict_with_datatypes(&candidate) else {
                    continue;
                };
                if quality.trust_count != 0 {
                    continue;
                }
                *proof = candidate;
                self.last_proof_term_overrides = None;
                return;
            }
        }
    }

    /// NIA pin-substitution collapse (#trust-count→0). When a nonlinear
    /// multiplication is pinned by substituting a constant for one factor — e.g.
    /// `(= (* x y) 7) ∧ (= x 2)`, where `x = 2` turns `x·y = 7` into the
    /// integer-infeasible `2y = 7` — the elaborator folds `(* x y)[x:=2]` to the
    /// canonical `(* y 2)` and the live classifier emits the residual
    /// `(= 7 (* y 2))` as a single `trust` `Step`. After
    /// `promote_lia_divisibility_lemmas`, the proof is exactly:
    ///   [0] Step{Trust, clause:[(= 7 (* y 2))]}
    ///   [1] TheoryLemma{LiaGeneric, Divisibility, clause:[(not (= 7 (* y 2)))]}
    ///   [2] Step{ThResolution, premises:[1,0], clause:[]}
    /// The divisibility lemma is already strict-checkable; ONLY the trust `Step`
    /// remains. Reconstruct that step — which is the substitution
    /// `(= (* x y) 7) ∧ (= x 2) ⊢ (= 7 (* y 2))` — from the parsed assertions as
    ///   assume      (= (* x y) 7)                    [A_mul]
    ///   assume      (= x 2)                           [A_sub, the pin]
    ///   eq_reflexive (= w w)                          [non-pinned factor]
    ///   eq_congruent (= (* x y) (* 2 y))              [substitute the pin]
    ///   LinearIdentity (= (* 2 y) (* y 2))            [commutativity bridge]
    ///   eq_transitive 7 = (* x y) = (* 2 y) = (* y 2) ⟹ (= 7 (* y 2))
    ///   resolution chain ⟹ [(= 7 (* y 2))]            [reproduce the trust clause]
    /// then re-emit the divisibility lemma + close to the empty clause. SOUND +
    /// fail-closed: every emitted step is one of `eq_reflexive` / `eq_congruent` /
    /// `eq_transitive` / `LinearIdentity` / `ThResolution` (all independently
    /// re-validated by the strict checker), the bridge is gated through the
    /// checker's own `recognize_lia_linear_identity`, the raw congruence/bridge
    /// terms carry per-node faithfulness guards, and the WHOLE rebuilt proof is
    /// gated through `check_proof_strict` with `trust_count == 0` — any miss
    /// discards the reconstruction and keeps the original trust proof.
    ///
    /// Scope (first version): the BINARY-multiplication, single-pinned-factor
    /// shape only. Multi-factor / n-ary / multi-pin → declines (fall back).
    fn promote_nia_pin_substitution(&mut self, proof: &mut Proof) {
        // ── (1) Detection: the exact 3-step pinned-multiplication shape. ──
        if proof.steps.len() != 3 {
            return;
        }
        // step[0]: Step{Trust, premises:[], clause:[trust_c]} where trust_c is a
        // positive equality with one side an integer constant and the other a
        // canonical BINARY multiplication.
        let ProofStep::Step {
            rule: AletheRule::Trust,
            clause: trust_clause,
            premises: trust_premises,
            ..
        } = &proof.steps[0]
        else {
            return;
        };
        if !trust_premises.is_empty() || trust_clause.len() != 1 {
            return;
        }
        let trust_c = trust_clause[0];
        let Some((tl, tr)) = decode_eq_local(&self.ctx.terms, trust_c) else {
            return;
        };
        // Exactly one side is an integer constant `k7`; the other is a binary `*`.
        let (k7, mul_canon) = match (
            is_int_const_local(&self.ctx.terms, tl),
            is_int_const_local(&self.ctx.terms, tr),
        ) {
            (true, false) => (tl, tr),
            (false, true) => (tr, tl),
            _ => return,
        };
        let mul_canon_args = match self.ctx.terms.get(mul_canon) {
            TermData::App(Symbol::Named(n), args) if n == "*" && args.len() == 2 => args.clone(),
            _ => return,
        };
        // step[1]: TheoryLemma{LiaGeneric, Divisibility, clause:[(not trust_c)]}.
        let ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::LiaGeneric,
            clause: div_clause,
            lia: Some(ay_core::LiaAnnotation::Divisibility),
            farkas: div_farkas,
            ..
        } = &proof.steps[1]
        else {
            return;
        };
        if div_clause.len() != 1 {
            return;
        }
        let div_neg = div_clause[0];
        // The divisibility negation must be exactly `(not trust_c)` (id-equal).
        if !matches!(self.ctx.terms.get(div_neg), TermData::Not(inner) if *inner == trust_c) {
            return;
        }
        let div_farkas = div_farkas.clone();
        // step[2]: Step{ThResolution, premises:{0,1}, clause:[]}.
        let ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: close_clause,
            premises: close_premises,
            ..
        } = &proof.steps[2]
        else {
            return;
        };
        if !close_clause.is_empty()
            || close_premises.len() != 2
            || !close_premises.contains(&ProofId(0))
            || !close_premises.contains(&ProofId(1))
        {
            return;
        }

        // ── (2) Recover the substitution witnesses from the parsed assertions. ──
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        // A_mul: `(= M K)` with `M` a binary `*` over two atoms and `K == k7`.
        // A_sub candidates: `(= s v)` with one side a constant (the pins).
        let mut a_mul_terms: Option<(TermId, [TermId; 2])> = None; // (mul_xy, [arg0,arg1])
        let mut subs: Vec<(TermId, TermId)> = Vec::new(); // (a_sub_id, pinned_var)
        for asrt in &parsed {
            if let Some((mul_xy, args2)) = self.match_pin_product_assertion(asrt, k7) {
                if a_mul_terms.is_none() {
                    a_mul_terms = Some((mul_xy, args2));
                }
                continue;
            }
            if let Some((a_sub_id, pinned_var, _k)) = self.match_pin_substitution_assertion(asrt) {
                subs.push((a_sub_id, pinned_var));
            }
        }
        let Some((mul_xy, mul_args)) = a_mul_terms else {
            return;
        };
        // Exactly one of `mul_xy`'s two factors must be pinned by a substitution;
        // the other stays. (Binary mul, single pinned factor.)
        let mut pin: Option<(TermId, TermId, TermId, TermId)> = None; // (a_sub, v, kv, w)
        for &(a_sub_id, v) in &subs {
            let (idx, w) = if mul_args[0] == v {
                (0usize, mul_args[1])
            } else if mul_args[1] == v {
                (1usize, mul_args[0])
            } else {
                continue;
            };
            // Recover the constant `kv` from the substitution assertion.
            let Some((sl, sr)) = decode_eq_local(&self.ctx.terms, a_sub_id) else {
                continue;
            };
            let kv = if sl == v && is_int_const_local(&self.ctx.terms, sr) {
                sr
            } else if sr == v && is_int_const_local(&self.ctx.terms, sl) {
                sl
            } else {
                continue;
            };
            // Verify the pin REALLY produces the canonical mul on the trust clause:
            // `mk_mul` of the substituted factors must be id-identical to `mul_canon`.
            let mut sub_factors = mul_args;
            sub_factors[idx] = kv;
            let probe = self.ctx.terms.mk_mul(sub_factors.to_vec());
            if probe != mul_canon {
                continue;
            }
            if pin.is_some() {
                // Ambiguous (both factors pinned) → out of scope; fall back.
                return;
            }
            pin = Some((a_sub_id, v, kv, w));
        }
        let Some((a_sub, v, kv, w)) = pin else {
            return;
        };
        // The non-pinned factor must appear in the canonical mul (sanity: the
        // bridge connects to a `mul_canon` that genuinely shares `w`).
        if !mul_canon_args.contains(&w) {
            return;
        }

        // ── (3) Build the reconstruction terms (RAW where canonicalization would
        //         break the structural eq_congruent / eq_transitive matching). ──
        // raw_sub_mul = (* <pinned→kv> <w>) in mul_xy's positional arg order.
        let mut raw_factors = mul_args;
        for f in raw_factors.iter_mut() {
            if *f == v {
                *f = kv;
            }
        }
        let raw_sub_mul = self
            .ctx
            .terms
            .mk_app(Symbol::named("*"), raw_factors, Sort::Int);
        // Faithfulness guard: the raw substituted mul must NOT have folded.
        if !matches!(
            self.ctx.terms.get(raw_sub_mul),
            TermData::App(Symbol::Named(n), a)
                if n == "*" && a.as_slice() == raw_factors.as_slice()
        ) {
            return;
        }
        // cong_eq = (= (* x y) (* <kv> y))  — RAW `=` (distinct sides won't fold).
        let cong_eq = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [mul_xy, raw_sub_mul], Sort::Bool);
        if !matches!(
            self.ctx.terms.get(cong_eq),
            TermData::App(Symbol::Named(n), a)
                if n == "=" && a.as_slice() == [mul_xy, raw_sub_mul]
        ) {
            return;
        }
        // bridge = (= (* <kv> y) (* y <kv>))  — RAW `=`, validated LinearIdentity.
        let bridge =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [raw_sub_mul, mul_canon], Sort::Bool);
        if !matches!(
            self.ctx.terms.get(bridge),
            TermData::App(Symbol::Named(n), a)
                if n == "=" && a.as_slice() == [raw_sub_mul, mul_canon]
        ) {
            return;
        }
        if !ay_core::proof_validation::recognize_lia_linear_identity(&self.ctx.terms, &[bridge]) {
            return;
        }
        // raw_ww = (= w w)  — RAW refl (mk_eq folds `(= w w)` to true).
        let raw_ww = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [w, w], Sort::Bool);
        if !matches!(
            self.ctx.terms.get(raw_ww),
            TermData::App(Symbol::Named(n), a) if n == "=" && a.as_slice() == [w, w]
        ) {
            return;
        }
        // The exact A_mul equality id (must be the elaborated assertion term so the
        // resolution against its assume closes). `a_mul = (= (* x y) 7)`.
        let a_mul = self.ctx.terms.mk_eq(mul_xy, k7);
        let not_a_mul = self.ctx.terms.mk_not_raw(a_mul);
        let not_a_sub = self.ctx.terms.mk_not_raw(a_sub);
        let not_cong = self.ctx.terms.mk_not_raw(cong_eq);
        let not_bridge = self.ctx.terms.mk_not_raw(bridge);
        let not_ww = self.ctx.terms.mk_not_raw(raw_ww);

        // ── (4) Rebuild the proof. Snapshot original for the revert gate. ──
        let original_steps = proof.steps.clone();
        let original_named = proof.named_steps.clone();
        proof.steps.clear();
        proof.named_steps.clear();

        // h0: assume (= (* x y) 7); h1: assume (= x 2).
        let h0 = proof.add_assume(a_mul, Some("h0".to_string()));
        let h1 = proof.add_assume(a_sub, Some("h1".to_string()));
        // refl: (= w w)  :rule eq_reflexive
        let refl = proof.add_step(ProofStep::Step {
            rule: AletheRule::EqReflexive,
            clause: vec![raw_ww],
            premises: Vec::new(),
            args: Vec::new(),
        });
        // cong: substitute the pin. Premises in mul_xy's ARGUMENT ORDER: position
        // holding `v` → ¬(= v kv) (= ¬a_sub); position holding `w` → ¬(= w w).
        let mut cong_clause = Vec::with_capacity(3);
        for &f in &mul_args {
            if f == v {
                cong_clause.push(not_a_sub);
            } else {
                cong_clause.push(not_ww);
            }
        }
        cong_clause.push(cong_eq);
        let cong = proof.add_step(ProofStep::Step {
            rule: AletheRule::EqCongruent,
            clause: cong_clause,
            premises: Vec::new(),
            args: Vec::new(),
        });
        // bridge_lem: (= (* kv y) (* y kv))  :rule lia_generic / LinearIdentity
        let bridge_lem = proof.add_step(ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![bridge],
            farkas: Some(FarkasAnnotation::new(vec![num_rational::Rational64::from(
                1,
            )])),
            kind: TheoryLemmaKind::LiaGeneric,
            lia: Some(ay_core::LiaAnnotation::LinearIdentity),
        });
        // trans: 7 = (* x y) = (* kv y) = (* y kv) ⟹ (= 7 (* y kv))
        //   premises (undirected, negated): ¬a_mul, ¬cong_eq, ¬bridge; conc trust_c.
        let trans = proof.add_step(ProofStep::Step {
            rule: AletheRule::EqTransitive,
            clause: vec![not_a_mul, not_cong, not_bridge, trust_c],
            premises: Vec::new(),
            args: Vec::new(),
        });

        // Resolve the chain down to [trust_c]. Each is a binary ThResolution whose
        // resolvent is computed by `binary_set_resolvent`.
        let trans_clause = vec![not_a_mul, not_cong, not_bridge, trust_c];
        let h0_clause = vec![a_mul];
        let r1c = binary_set_resolvent(&trans_clause, &h0_clause, a_mul, not_a_mul);
        let r1 = proof.add_step(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: r1c.clone(),
            premises: vec![trans, h0],
            args: Vec::new(),
        });
        // cong clause for resolvent computation (reproduce from cong_clause shape).
        let mut cong_full = Vec::with_capacity(3);
        for &f in &mul_args {
            cong_full.push(if f == v { not_a_sub } else { not_ww });
        }
        cong_full.push(cong_eq);
        let r2c = binary_set_resolvent(&r1c, &cong_full, cong_eq, not_cong);
        let r2 = proof.add_step(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: r2c.clone(),
            premises: vec![r1, cong],
            args: Vec::new(),
        });
        let bridge_clause = vec![bridge];
        let r3c = binary_set_resolvent(&r2c, &bridge_clause, bridge, not_bridge);
        let r3 = proof.add_step(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: r3c.clone(),
            premises: vec![r2, bridge_lem],
            args: Vec::new(),
        });
        let h1_clause = vec![a_sub];
        let r4c = binary_set_resolvent(&r3c, &h1_clause, a_sub, not_a_sub);
        let r4 = proof.add_step(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: r4c.clone(),
            premises: vec![r3, h1],
            args: Vec::new(),
        });
        let refl_clause = vec![raw_ww];
        let r5c = binary_set_resolvent(&r4c, &refl_clause, raw_ww, not_ww);
        let r5 = proof.add_step(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: r5c.clone(),
            premises: vec![r4, refl],
            args: Vec::new(),
        });

        // Re-emit the divisibility lemma (reusing its annotation) + close to [].
        let div = proof.add_step(ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![div_neg],
            farkas: div_farkas.or_else(|| {
                Some(FarkasAnnotation::new(vec![num_rational::Rational64::from(
                    1,
                )]))
            }),
            kind: TheoryLemmaKind::LiaGeneric,
            lia: Some(ay_core::LiaAnnotation::Divisibility),
        });
        // Closing resolution: r5c = [trust_c] (positive) against div = [¬trust_c].
        // `binary_set_resolvent` drops `pivot_neg` from c1 and `pivot_pos` from c2,
        // so here pivot_pos = div_neg (dropped from div) and pivot_neg = trust_c
        // (dropped from r5c) — the OPPOSITE polarity arrangement from the chain
        // steps above, where the positive pivot lived in c2.
        let empty = binary_set_resolvent(&r5c, &[div_neg], div_neg, trust_c);
        proof.add_step(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: empty,
            premises: vec![r5, div],
            args: Vec::new(),
        });

        // ── (5) WHOLE-PROOF revert gate. ──
        match ay_proof::check_proof_strict(proof, &self.ctx.terms) {
            Ok(q) if q.trust_count == 0 => { /* keep the reconstruction */ }
            _ => {
                proof.steps = original_steps;
                proof.named_steps = original_named;
            }
        }
    }

    /// Match a parsed pin-PRODUCT assertion `(= M K)` (either orientation) where
    /// `M` is a binary `(* a b)` over two `Int` atoms and `K` rebuilds to the same
    /// integer constant `k7` as the trust clause. Returns `(mul_xy, [arg0, arg1])`
    /// (the CANONICAL `mk_mul` rebuild + its stored arg ids). Fail-closed.
    fn match_pin_product_assertion(
        &mut self,
        asrt: &FrontendTerm,
        k7: TermId,
    ) -> Option<(TermId, [TermId; 2])> {
        let FrontendTerm::App(op, args) = asrt else {
            return None;
        };
        if op != "=" || args.len() != 2 {
            return None;
        }
        for (mi, ki) in [(0usize, 1usize), (1, 0)] {
            let FrontendTerm::App(mop, margs) = &args[mi] else {
                continue;
            };
            if mop != "*" || margs.len() != 2 {
                continue;
            }
            let (Some(k_id), Some(a0), Some(a1)) = (
                build_int_pterm(&mut self.ctx.terms, &args[ki]),
                build_int_pterm(&mut self.ctx.terms, &margs[0]),
                build_int_pterm(&mut self.ctx.terms, &margs[1]),
            ) else {
                continue;
            };
            if k_id != k7 {
                continue;
            }
            let mul_xy = self.ctx.terms.mk_mul(vec![a0, a1]);
            let stored = match self.ctx.terms.get(mul_xy) {
                TermData::App(Symbol::Named(n), a) if n == "*" && a.len() == 2 => [a[0], a[1]],
                _ => continue,
            };
            return Some((mul_xy, stored));
        }
        None
    }

    /// Match a parsed pin-SUBSTITUTION assertion `(= s v)` (either orientation)
    /// where exactly one side is an `Int` variable atom and the other an integer
    /// constant. Returns `(a_sub_id, var_id, const_id)` with `a_sub_id` the
    /// CANONICAL `mk_eq` rebuild (id-identical to the elaborated assertion).
    fn match_pin_substitution_assertion(
        &mut self,
        asrt: &FrontendTerm,
    ) -> Option<(TermId, TermId, TermId)> {
        let FrontendTerm::App(op, args) = asrt else {
            return None;
        };
        if op != "=" || args.len() != 2 {
            return None;
        }
        let l = build_int_pterm(&mut self.ctx.terms, &args[0])?;
        let r = build_int_pterm(&mut self.ctx.terms, &args[1])?;
        let l_var = matches!(self.ctx.terms.get(l), TermData::Var(_, _));
        let r_var = matches!(self.ctx.terms.get(r), TermData::Var(_, _));
        let l_const = is_int_const_local(&self.ctx.terms, l);
        let r_const = is_int_const_local(&self.ctx.terms, r);
        let (var_id, const_id) = if l_var && r_const {
            (l, r)
        } else if r_var && l_const {
            (r, l)
        } else {
            return None;
        };
        let a_sub_id = self.ctx.terms.mk_eq(var_id, const_id);
        Some((a_sub_id, var_id, const_id))
    }

    /// Boolean tautology collapse (#trust-count→0). An assertion `A` that is a
    /// propositional CONTRADICTION — e.g. `(not (= (not (not p)) p))` or
    /// `(= p (not p))` — folds to `false` during elaboration, degenerating the
    /// UNSAT proof to a single empty-clause `trust` step. Reconstruct the
    /// refutation FROM THE PARSED ASSERTION as
    ///   assume      A            the input hypothesis (always false)
    ///   lemma       (not A)       strict-validated (a Boolean TAUTOLOGY)
    ///   resolution  □
    /// The strict checker validates the lemma by EXHAUSTIVE bounded evaluation
    /// over the Bool/small-BV variables (`validate_bool_tautology`) — a genuine
    /// bounded decision procedure.
    ///
    /// SOUND + fail-closed: `A` is rebuilt by the faithful `build_bool_pterm`
    /// (raw `mk_not_raw`/`mk_app`, per-node guard, so the `assume` matches the
    /// real input), and the lemma `(not A)` is gated through the checker's own
    /// `recognize_bool_tautology` before commit (so `A` is committed as
    /// refutable only when `¬A` is genuinely a tautology). Any miss — a non-Bool
    /// term, an unbounded variable, or `¬A` not a tautology — leaves the trust
    /// step untouched.
    fn promote_bool_tautology_collapse(&mut self, proof: &mut Proof) {
        if !Self::proof_needs_schema_collapse_reconstruction(proof) {
            return;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        for asrt in &parsed {
            let Some(a_t) = build_bool_pterm(&mut self.ctx.terms, asrt) else {
                continue;
            };
            if !matches!(self.ctx.terms.sort(a_t), Sort::Bool) {
                continue;
            }
            let not_a = self.ctx.terms.mk_not_raw(a_t);
            // Gate: `¬A` must be a genuine Boolean tautology (⟺ `A` is always
            // false), re-validated by the checker's exhaustive bounded evaluator.
            if !ay_proof::recognize_bool_tautology(&self.ctx.terms, &[not_a]) {
                continue;
            }

            self.record_rebuilt_authored_proof_premise(a_t);
            proof.steps.clear();
            proof.named_steps.clear();
            let assume_id = proof.add_assume(a_t, None);
            let lemma_id = proof.add_theory_lemma_with_kind(
                "bool",
                vec![not_a],
                TheoryLemmaKind::BoolTautology,
            );
            proof.add_resolution(vec![], a_t, assume_id, lemma_id);
            return;
        }
    }

    /// If-then-else identical-branches collapse (#trust-count→0). An assertion
    /// `(not (= (ite c x x) x))` folds to `false` during elaboration (the term
    /// builder reduces `(ite c x x) → x`), degenerating the UNSAT proof to a
    /// single empty-clause `trust` step. Reconstruct the refutation FROM THE
    /// PARSED ASSERTION as
    ///   assume      (not (= (ite c x x) x))    the input hypothesis
    ///   lemma       (= (ite c x x) x)           strict-validated (IteSame)
    ///   resolution  □
    /// The `ite` the fold erased is rebuilt with the RAW `mk_ite_raw` (which does
    /// NOT collapse equal branches), so the lemma keeps its `ite` for the strict
    /// checker's syntactic `validate_ite_same`.
    ///
    /// SOUND + fail-closed: the condition and the branch/value are all symbols
    /// resolved via `lookup`, the branches are the same `TermId`, and the lemma
    /// is gated through the checker's own `recognize_ite_same` before commit. The
    /// axiom holds for ANY condition and ANY sort of the branch. Any miss leaves
    /// the trust step untouched.
    fn promote_ite_same_collapse(&mut self, proof: &mut Proof) {
        if !Self::proof_needs_schema_collapse_reconstruction(proof) {
            return;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        for asrt in &parsed {
            let Some((cond, x)) = match_ite_same_negation(asrt) else {
                continue;
            };
            let (Some(cond_id), Some(x_id)) =
                (self.ctx.terms.lookup(cond), self.ctx.terms.lookup(x))
            else {
                continue;
            };
            if !matches!(self.ctx.terms.sort(cond_id), Sort::Bool) {
                continue;
            }
            // Rebuild `(ite cond x x)` RAW — `mk_ite_raw` keeps the `ite` that the
            // folding `mk_ite` would collapse to `x`.
            let ite_t = self.ctx.terms.mk_ite_raw(cond_id, x_id, x_id);
            let eq_t = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [ite_t, x_id], Sort::Bool);
            if !ay_proof::recognize_ite_same(&self.ctx.terms, &[eq_t]) {
                continue;
            }
            let neg_t = self.ctx.terms.mk_not_raw(eq_t);

            self.record_rebuilt_authored_proof_premise(neg_t);
            proof.steps.clear();
            proof.named_steps.clear();
            let assume_id = proof.add_assume(neg_t, None);
            let lemma_id =
                proof.add_theory_lemma_with_kind("ite", vec![eq_t], TheoryLemmaKind::IteSame);
            proof.add_resolution(vec![], eq_t, assume_id, lemma_id);
            return;
        }
    }

    /// Whether `proof` is the degenerate whole-proof collapse that the
    /// `promote_*_collapse` passes reconstruct from the parsed assertion. Two
    /// encodings represent the same "the single assertion folded to `false` at
    /// elaboration, leaving no structure to certify" condition:
    ///
    /// 1. **Legacy single empty `trust` step** — one `AletheRule::Trust`,
    ///    empty clause, no premises (pre-807ffb8f, when a term-less fresh var
    ///    fell back to Trust).
    /// 2. **`:rule false` collapse** (807ffb8f) — once the Tseitin encoder emits
    ///    a proof-carrying clause for `Const(Bool(false))`, the reconstructed
    ///    UNSAT proof of a fold-to-`false` assertion is the 3-step shape
    ///    `[ Assume(X), Step{rule:False, clause:[¬X], args:[X]},
    ///       Resolution{clause:[]} ]` — trust-free but with the original theory
    ///    structure erased (`X` is the raw input assertion). This is the shape
    ///    the failing collapse/firewall tests now see.
    ///
    /// 3. **Boolean-constant refutation** — the encoder first derives `¬false`
    ///    with `:rule false`, retains `false` as an honest hole, then resolves
    ///    them. This is the current fold-to-false shape when no authored raw
    ///    assertion survived into the initial proof.
    ///
    /// Any shape means the load-bearing theory lemma was folded away, so the
    /// promote passes should attempt reconstruction. The passes each re-parse
    /// the assertion and re-gate through the strict checker's own recognizer, so
    /// widening this trigger cannot fabricate an unchecked lemma (a mismatch
    /// leaves the proof untouched).
    fn proof_is_single_empty_trust(proof: &Proof) -> bool {
        Self::proof_is_legacy_empty_trust(proof)
            || Self::proof_is_false_rule_collapse(proof)
            || Self::proof_is_false_constant_collapse(proof)
            || Self::proof_is_assumed_false_collapse(proof)
    }

    /// Shape 4: `[Assume(false), <unit step concluding not-false>, Resolution([])]`.
    ///
    /// The assumption is the `false` CONSTANT — the elaborated remains of an
    /// assertion that folded all the way down — so the whole derivation says
    /// only "the elaborated assertion list contains `false`". Whatever theory
    /// label the middle step carries (`BoolTautology` from the propositional
    /// fallback, `OrderIteTautology` from the order-ITE replacement, a bare
    /// `false`/`hole` step from the encoder) it concludes a Boolean-constant
    /// fact, not the authored theory theorem, so the collapse promoters must
    /// still get their chance to rebuild the real refutation.
    ///
    /// Recognizing the assumed constant is the entire discriminator: the same
    /// three-step skeleton over a real atom `p` is an ordinary unit refutation
    /// and must NOT be treated as a collapse. This predicate takes only a
    /// `Proof`, so it names `false` through [`TermStore::PREALLOCATED_FALSE`],
    /// the interning position `TermStore::new` asserts for it.
    ///
    /// Like the other shapes this is only a TRIGGER: every caller rebuilds the
    /// authored surface assertion and re-gates through the strict checker's own
    /// recognizer before replacing anything.
    fn proof_is_assumed_false_collapse(proof: &Proof) -> bool {
        if proof.steps.len() != 3 {
            return false;
        }
        let ProofStep::Assume(assumed) = proof.steps[0] else {
            return false;
        };
        if assumed != TermStore::PREALLOCATED_FALSE {
            return false;
        }
        let derives_not_false = matches!(
            &proof.steps[1],
            ProofStep::TheoryLemma { clause, .. } if clause.len() == 1
        ) || matches!(
            &proof.steps[1],
            ProofStep::Step { clause, premises, .. }
                if clause.len() == 1 && premises.is_empty()
        );
        let closes = matches!(
            &proof.steps[2],
            ProofStep::Resolution { clause, pivot, .. }
                if clause.is_empty() && *pivot == assumed
        ) || matches!(
            &proof.steps[2],
            ProofStep::Step {
                rule: AletheRule::Resolution | AletheRule::ThResolution,
                clause,
                ..
            } if clause.is_empty()
        );
        derives_not_false && closes
    }

    /// Whether a completed refutation is eligible for replacement by a
    /// schema-specific authored contradiction. Even a native trust-free proof
    /// can have collapsed the authored theory formula into a generic
    /// `BoolTautology`; that loses the dedicated Alethe lowering and Lean
    /// firewall artifact. The replacement routines independently recognize and
    /// strict-check the exact reconstructed theorem before committing it, so it
    /// is safe to try them on every completed refutation.
    fn proof_needs_schema_collapse_reconstruction(proof: &Proof) -> bool {
        Self::proof_derives_empty_clause(proof)
    }

    /// Shape 1: a single empty-clause `trust` step with no premises.
    fn proof_is_legacy_empty_trust(proof: &Proof) -> bool {
        proof.steps.len() == 1
            && matches!(
                &proof.steps[0],
                ProofStep::Step { rule: AletheRule::Trust, clause, premises, .. }
                    if clause.is_empty() && premises.is_empty()
            )
    }

    /// Shape 2: the `:rule false` collapse `[Assume(X), Step{rule:False,
    /// clause:[¬X], args:[X]}, Resolution{clause:[]}]` (807ffb8f). Keyed on the
    /// load-bearing `false` step (single-literal conclusion, `X` as its arg)
    /// closing to the empty clause, so it is robust to how the empty clause is
    /// spelled (a dedicated `Resolution` node or an equivalent `Step`).
    fn proof_is_false_rule_collapse(proof: &Proof) -> bool {
        if proof.steps.len() != 3 {
            return false;
        }
        if !matches!(&proof.steps[0], ProofStep::Assume(_)) {
            return false;
        }
        if !matches!(
            &proof.steps[1],
            ProofStep::Step { rule: AletheRule::False, clause, args, .. }
                if clause.len() == 1 && args.len() == 1
        ) {
            return false;
        }
        matches!(
            &proof.steps[2],
            ProofStep::Resolution { clause, .. } if clause.is_empty()
        ) || matches!(
            &proof.steps[2],
            ProofStep::Step {
                rule: AletheRule::Resolution | AletheRule::ThResolution,
                clause,
                ..
            } if clause.is_empty()
        )
    }

    /// Shape 3: `[False([¬false]), Hole/Trust([false]), Resolution([])]`.
    ///
    /// This is only a trigger for schema-specific reconstruction; callers still
    /// rebuild and strictly validate the authored theorem before replacement.
    fn proof_is_false_constant_collapse(proof: &Proof) -> bool {
        if proof.steps.len() != 3 {
            return false;
        }
        let false_axiom = matches!(
            &proof.steps[0],
            ProofStep::Step { rule: AletheRule::False, clause, premises, .. }
                if clause.len() == 1 && premises.is_empty()
        );
        let false_hole = matches!(
            &proof.steps[1],
            ProofStep::Step {
                rule: AletheRule::Hole | AletheRule::Trust,
                clause,
                premises,
                ..
            } if clause.len() == 1 && premises.is_empty()
        ) || matches!(
            &proof.steps[1],
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                clause,
                ..
            } if clause.len() == 1
        );
        let closes = matches!(
            &proof.steps[2],
            ProofStep::Resolution { clause, .. } if clause.is_empty()
        ) || matches!(
            &proof.steps[2],
            ProofStep::Step {
                rule: AletheRule::Resolution | AletheRule::ThResolution,
                clause,
                ..
            } if clause.is_empty()
        );
        false_axiom && false_hole && closes
    }

    // Farkas synthesis functions extracted to proof_farkas.rs (#6763).
    // Resolution strategies extracted to proof_resolution.rs (#6763).

    fn collect_hidden_problem_equality_assertions(&mut self) -> Vec<TermId> {
        let true_id = self.ctx.terms.true_term();
        let parsed_assertions: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        let problem_assertions = self.proof_original_problem_assertions();
        let mut hidden = Vec::new();

        for (&canonical, parsed) in problem_assertions.iter().zip(parsed_assertions.iter()) {
            if canonical != true_id || !super::proof_farkas::frontend_term_is_equality(parsed) {
                continue;
            }

            let Some(Some(CommandResult::CheckSatAssuming(term_ids))) = self
                .ctx
                .process_command(&Command::CheckSatAssuming(vec![parsed.clone()]))
                .ok()
            else {
                continue;
            };
            let [term_id] = term_ids.as_slice() else {
                continue;
            };

            if matches!(
                self.ctx.terms.get(*term_id),
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2
            ) && !hidden.contains(term_id)
            {
                hidden.push(*term_id);
            }
        }

        // (#6759) In the with_deferred_postprocessing path, provenance-aware
        // original problem assertions may contain equalities not present in
        // ctx.assertions (which holds simplified/temporary forms). Include
        // these directly so the Farkas reconstruction can find them for
        // Not(true) replacement.
        for &term in &problem_assertions {
            if !hidden.contains(&term)
                && !self.ctx.assertions.contains(&term)
                && matches!(
                    self.ctx.terms.get(term),
                    TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2
                )
            {
                hidden.push(term);
            }
        }

        hidden
    }

    /// Term overrides handed to the Alethe printer: the surface-syntax
    /// spellings collected from the parsed input during solving, extended with
    /// renderings for the frontend's invented single-constructor field
    /// constants — the `v!field` names eager datatype elimination mints, which
    /// NO problem-file text ever names (see `Context::dt_field_surface_over-
    /// rides`; measured on QF_DT blocksworld: 14 such names in 26,366
    /// occurrences left carcara 1.1.0 failing in the PARSER with
    /// `identifier 's_tmp___!left' is not defined`, before any rule ran).
    ///
    /// The SOURCE-derived entry WINS on a key present in both. It is derived
    /// from bytes that literally appear in the `.smt2` the checker reads, so it
    /// is authoritative about identity in a way a synthesized rendering is not;
    /// it keeps `collect_surface_term_overrides`' single first-wins ordering
    /// discipline; and it makes every term that has a source override today
    /// keep a byte-identical rendering, so no currently-checking proof can
    /// move. (In practice the two agree: a field term only acquires a source
    /// override when the input literally wrote `(left s_)`.)
    fn proof_export_term_overrides(
        &self,
    ) -> Option<ay_core::kani_compat::DetHashMap<TermId, String>> {
        let fields = self.ctx.dt_field_surface_overrides();
        if fields.is_empty() {
            return self.last_proof_term_overrides.clone();
        }
        let mut merged = fields;
        if let Some(source) = self.last_proof_term_overrides.as_ref() {
            for (term, rendering) in source {
                merged.insert(*term, rendering.clone());
            }
        }
        Some(merged)
    }

    /// Get proof (get-proof command)
    ///
    /// Returns a proof that the assertions are unsatisfiable in Alethe format.
    pub(super) fn get_proof(&self) -> String {
        // Live SMT enablement cannot relabel an old solve-time proof request.
        if !self.is_producing_proofs() {
            return "(error \"proof generation is not enabled, set :produce-proofs to true\")"
                .to_string();
        }

        if self.last_unsat_proof_reconstruction_suppressed {
            return "(error \"proof was not generated for this independently certified result\")"
                .to_string();
        }

        // Check that last result was unsat
        match self.last_result {
            Some(SolveResult::Unsat(_)) => {
                // Export the stored proof in Alethe format
                match self.last_proof() {
                    Some(proof) => {
                        let Some(scope) = self.proof_export_scope_assertions_for(proof) else {
                            return "(error \"finite-enum proof authority is stale\")".to_string();
                        };
                        if self.last_proof_has_finite_enum_sidecar() {
                            let Some(overrides) =
                                self.finite_enum_surface_overrides_for_proof(proof)
                            else {
                                return "(error \"finite-enum proof has no authenticated external surface\")"
                                    .to_string();
                            };
                            ay_proof::try_export_alethe_with_problem_scope_overrides_and_budget(
                                proof,
                                &self.ctx.terms,
                                &scope,
                                Some(overrides),
                                Some(MAX_FINITE_ENUM_RENDER_WORK),
                            )
                            .unwrap_or_else(|_| {
                                "(error \"finite-enum proof exceeds the bounded rendering envelope\")"
                                    .to_string()
                            })
                        } else {
                            let overrides = self.proof_export_term_overrides();
                            export_alethe_with_problem_scope_and_overrides(
                                proof,
                                &self.ctx.terms,
                                &scope,
                                overrides.as_ref(),
                            )
                        }
                    }
                    None => "(error \"proof was not generated\")".to_string(),
                }
            }
            Some(SolveResult::Sat) => {
                "(error \"proof is not available, last result was sat\")".to_string()
            }
            Some(SolveResult::Unknown) => {
                "(error \"proof is not available, last result was unknown\")".to_string()
            }
            None => {
                "(error \"proof is not available, no check-sat has been performed\")".to_string()
            }
        }
    }

    /// Export the last proof through the same problem-scoped Alethe path used by
    /// `(get-proof)`.
    ///
    /// File-backed SMT proof output must not emit declarations for symbols that
    /// are already declared by the SMT-LIB problem. External checkers such as
    /// Carcara read the problem file separately and expect the proof file to
    /// contain only proof commands.
    #[must_use]
    pub fn try_export_last_proof_alethe_for_problem_scope(
        &self,
    ) -> Option<Result<String, AlethePrintError>> {
        if self.last_unsat_proof_reconstruction_suppressed {
            return None;
        }
        let proof = self.last_proof()?;
        // #A2b: `proof_reconstruction_step_budget` is set ONLY for the
        // synthesized-default certificate (never for explicit `--proof`,
        // `--strict-proofs`, `--self-check`, or `:produce-proofs`). Extend
        // that contract over Alethe EMISSION as well: rendering work is
        // capped so a seconds-fast UNSAT verdict is never followed by
        // minutes of certificate materialization (QF_ALIA pp-family). On
        // exhaustion the caller prints the honest "no proof certificate
        // emitted" warning; the verdict is already out and unchanged.
        if self.last_proof_has_finite_enum_sidecar() {
            let Some(overrides) = self.finite_enum_surface_overrides_for_proof(proof) else {
                return Some(Err(AlethePrintError::UnavailableAuthenticatedSurface {
                    reason: "the finite-enum proof surface is absent or stale",
                }));
            };
            let Some(scope) = self.proof_export_scope_assertions_for(proof) else {
                return Some(Err(AlethePrintError::UnavailableAuthenticatedSurface {
                    reason: "the finite-enum proof scope is absent or stale",
                }));
            };
            return Some(
                ay_proof::try_export_alethe_with_problem_scope_overrides_and_budget(
                    proof,
                    &self.ctx.terms,
                    &scope,
                    Some(overrides),
                    Some(MAX_FINITE_ENUM_RENDER_WORK),
                ),
            );
        }
        let emission_budget = self
            .proof_reconstruction_step_budget
            .map(|_| DEFAULT_ALETHE_EMISSION_WORK_BUDGET);
        let scope = self.proof_export_scope_assertions_for(proof)?;
        let overrides = self.proof_export_term_overrides();
        Some(
            ay_proof::try_export_alethe_with_problem_scope_overrides_and_budget(
                proof,
                &self.ctx.terms,
                &scope,
                overrides.as_ref(),
                emission_budget,
            ),
        )
    }

    /// Streaming variant of
    /// [`Self::try_export_last_proof_alethe_for_problem_scope`]: renders the
    /// certificate directly into `out` instead of materializing it as one
    /// in-memory `String` (#rss-vs-z3 peak-RSS fix for large default-mode
    /// certificates — the byte stream is identical). On error the sink may
    /// hold a partial prefix; file-backed callers should write to a temp
    /// path and rename on success.
    #[must_use]
    pub fn try_export_last_proof_alethe_for_problem_scope_to<W: std::io::Write>(
        &self,
        out: &mut W,
    ) -> Option<Result<(), ay_proof::AletheStreamError>> {
        if self.last_unsat_proof_reconstruction_suppressed {
            return None;
        }
        let proof = self.last_proof()?;
        // #A2b: same emission-budget contract as the String variant above.
        if self.last_proof_has_finite_enum_sidecar() {
            let Some(overrides) = self.finite_enum_surface_overrides_for_proof(proof) else {
                return Some(Err(ay_proof::AletheStreamError::Print(
                    AlethePrintError::UnavailableAuthenticatedSurface {
                        reason: "the finite-enum proof surface is absent or stale",
                    },
                )));
            };
            let Some(scope) = self.proof_export_scope_assertions_for(proof) else {
                return Some(Err(ay_proof::AletheStreamError::Print(
                    AlethePrintError::UnavailableAuthenticatedSurface {
                        reason: "the finite-enum proof scope is absent or stale",
                    },
                )));
            };
            return Some(
                ay_proof::try_export_alethe_with_problem_scope_overrides_and_budget_to(
                    out,
                    proof,
                    &self.ctx.terms,
                    &scope,
                    Some(overrides),
                    Some(MAX_FINITE_ENUM_RENDER_WORK),
                ),
            );
        }
        let emission_budget = self
            .proof_reconstruction_step_budget
            .map(|_| DEFAULT_ALETHE_EMISSION_WORK_BUDGET);
        let scope = self.proof_export_scope_assertions_for(proof)?;
        let overrides = self.proof_export_term_overrides();
        Some(
            ay_proof::try_export_alethe_with_problem_scope_overrides_and_budget_to(
                out,
                proof,
                &self.ctx.terms,
                &scope,
                overrides.as_ref(),
                emission_budget,
            ),
        )
    }

    /// Problem-declared symbol names for the Alethe round-trip self-check.
    ///
    /// Used only as the fallback scope when the problem text is not readable
    /// from disk (stdin mode); the disk path scans the real declarations,
    /// including sorts.
    #[must_use]
    pub fn proof_export_problem_symbol_names(&self) -> Vec<String> {
        let scope = self.last_proof.as_ref().map_or_else(
            || self.proof_export_scope_assertions(),
            |proof| {
                self.proof_export_scope_assertions_for(proof)
                    .unwrap_or_default()
            },
        );
        ay_proof::problem_scope_symbol_names(&self.ctx.terms, &scope)
    }

    fn proof_export_scope_assertions_for(&self, proof: &Proof) -> Option<Vec<TermId>> {
        if self.last_proof_has_finite_enum_sidecar() {
            self.finite_enum_scope_for_proof(proof)
        } else {
            Some(self.proof_export_scope_assertions())
        }
    }

    /// Exact authored premise scope for Alethe authority checks. Combined
    /// preprocessing may expose both temporary problem representatives and
    /// original source assertions; proof reconstruction may re-intern the
    /// exact parsed source form; check-sat-assuming adds another authored
    /// source. Derived temporary constraints are intentionally absent.
    pub(crate) fn proof_export_scope_assertions(&self) -> Vec<TermId> {
        let mut scope = self.proof_problem_assertions();
        for assertion in self.proof_original_problem_assertions() {
            if !scope.contains(&assertion) {
                scope.push(assertion);
            }
        }
        // Proof reconstruction deliberately rebuilds the parsed source form
        // with raw constructors when elaboration folded it away (and creates
        // fresh alpha-renamed binders for quantified input). These terms are
        // genuine authored premises, captured once by the same provenance
        // path used by `proof_legit_assume_set`; excluding them here would let
        // the internal authority gate accept a proof that Alethe export then
        // rejects as a non-problem `assume`.
        for &assertion in &self.last_proof_rebuild_originals {
            if !scope.contains(&assertion) {
                scope.push(assertion);
            }
        }
        if let Some(assumptions) = &self.last_assumptions {
            for &assumption in assumptions {
                if !scope.contains(&assumption) {
                    scope.push(assumption);
                }
            }
        }
        if !self.boolean_constant_premises_authored().1 {
            scope.retain(|&term| term != self.ctx.terms.false_term());
        }
        scope
    }

    /// Admit one raw term reconstructed from a parsed source assertion as an
    /// authored proof premise. Callers must finish their structural and strict
    /// lemma-recognizer gates before recording it; arbitrary solver-derived
    /// terms never enter this set.
    pub(super) fn record_rebuilt_authored_proof_premise(&mut self, premise: TermId) {
        if !self.last_proof_rebuild_originals.contains(&premise) {
            self.last_proof_rebuild_originals.push(premise);
        }
    }

    /// Record eager array axioms as theory lemmas for proof attribution (#6722).
    ///
    /// Mirrors the DT selector axiom pattern in `solve_dt()`: each eager axiom
    /// that will appear in the DPLL assertion set is annotated in the proof
    /// tracker so SAT trace reconstruction can emit `TheoryLemma(ArraySelectStore)`
    /// steps instead of anonymous original clauses.
    ///
    /// Whether the internal proof tracker is RECORDING.
    ///
    /// NOT the same question as "did the caller ask for a proof" — use
    /// [`Executor::is_producing_proofs`] for that. `begin_public_solve` turns
    /// the tracker on for EVERY public decision (the mandatory UNSAT
    /// certificate does not depend on `:produce-proofs`), so this predicate is
    /// always true on the public path — with ONE explicit, opt-in carve-out:
    /// a competition-mode executor with no proof demand
    /// (`competition_shedding_active`, #proof-capability B1) leaves the
    /// tracker disabled, so on such sessions this predicate is false on the
    /// public path. The dead-gate inventory below is written against the
    /// certified default; under competition shedding those gates go LIVE and
    /// are audited (and kept dead where unvetted) by the B2 gate census.
    /// UNSAT publication stays fail-closed either way.
    ///
    /// That matters because a preprocessing or routing pass gated on
    /// `!produce_proofs_enabled()` is therefore DEAD, not opted out. Ten such
    /// gates — the LIA and LRA eager/incremental arms, `eq_diffvar`,
    /// `GuardedEqMining`, the second variable-substitution round, the packed-mux
    /// derived equalities, the QF_ABV dense-array initializer rewrite, and the
    /// non-string `seq` UNSAT corroboration — were written against the OLD
    /// meaning and silently stopped firing when the certificate became
    /// mandatory. Two QF_ABV instances regressed from `unsat` to `unknown` as a
    /// direct result. They now gate on `is_producing_proofs()`, which still
    /// means what their comments say.
    ///
    /// Use this one only where the question really is "is a proof being built"
    /// — recording hooks and the UNSAT postcondition asserts.
    pub(super) fn produce_proofs_enabled(&self) -> bool {
        self.proof_tracker.is_enabled()
            || matches!(
                self.ctx.get_option("produce-proofs"),
                Some(OptionValue::Bool(true))
            )
    }

    /// Skip preprocessing variable substitution when proofs are requested
    /// (#campaign-rank-4). Variable substitution rewrites assertions in
    /// place, which detaches the reconstructed proof's Assume leaves from the
    /// original assertions and forces Trust-step fallbacks — fatal for
    /// proof-based Craig interpolation.
    ///
    /// Enabled per-solver via `(set-option :ay-proof-no-varsubst true)`.
    /// (The former process-wide `AY_PROOF_NO_VARSUBST=1` env override is
    /// removed; the option is the only switch.) Only consulted when proof
    /// production is on; never affects verdicts, only proof shape.
    pub(super) fn proof_no_varsubst_enabled(&self) -> bool {
        matches!(
            self.ctx.get_option("ay-proof-no-varsubst"),
            Some(OptionValue::Bool(true))
        )
    }

    /// Check if strict proof checking is enabled (#4420).
    ///
    /// When `(set-option :check-proofs-strict true)` is set, the internal
    /// proof checker rejects `trust` and `hole` steps, requiring fully
    /// reconstructed proofs.
    pub(in crate::executor) fn strict_proofs_enabled(&self) -> bool {
        matches!(
            self.ctx.get_option("check-proofs-strict"),
            Some(OptionValue::Bool(true))
        )
    }
}

/// Replay a SAT clause trace into a standalone LRAT binary certificate.
///
/// Returns `None` when the trace is truncated or when the original-clause ID
/// layout no longer matches the contiguous `1..=n` numbering external LRAT
/// checkers expect from the input CNF.
fn clause_trace_to_lrat_bytes(trace: &ay_sat::ClauseTrace) -> Option<Vec<u8>> {
    if trace.is_truncated() || !trace.has_empty_clause() {
        return None;
    }

    let original_count =
        trace
            .original_clauses()
            .enumerate()
            .try_fold(0u64, |_, (idx, entry)| {
                let expected_id = u64::try_from(idx).ok()?.checked_add(1)?;
                (entry.id == expected_id).then_some(expected_id)
            })?;

    let mut output = ay_sat::ProofOutput::lrat_binary(Vec::new(), original_count);
    let mut next_learned_id = original_count + 1;
    for entry in trace.learned_clauses() {
        if entry.id < next_learned_id {
            return None;
        }
        output.advance_past(entry.id);
        let assigned_id = output.add(entry.clause, entry.resolution_hints).ok()?;
        if assigned_id != entry.id {
            return None;
        }
        next_learned_id = assigned_id + 1;
    }
    output.into_vec().ok()
}

/// Remap a step's premise `ProofId`s through `remap` (old index → new id).
/// Premises always reference EARLIER steps, so `remap` is fully populated for
/// every id this step can name. `Assume`/`TheoryLemma` carry no premises.
fn remap_step_premises(step: ProofStep, remap: &[ProofId]) -> ProofStep {
    let m = |id: ProofId| -> ProofId { remap.get(id.0 as usize).copied().unwrap_or(id) };
    match step {
        ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        } => ProofStep::Resolution {
            clause,
            pivot,
            clause1: m(clause1),
            clause2: m(clause2),
        },
        ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } => ProofStep::Step {
            rule,
            clause,
            premises: premises.into_iter().map(m).collect(),
            args,
        },
        ProofStep::Anchor {
            end_step,
            variables,
        } => ProofStep::Anchor {
            end_step: m(end_step),
            variables,
        },
        other => other,
    }
}

/// Strip `Not` wrappers, returning `(inner, negated)`.
fn strip_not_local(terms: &TermStore, mut t: TermId) -> (TermId, bool) {
    let mut negated = false;
    while let TermData::Not(inner) = terms.get(t) {
        t = *inner;
        negated = !negated;
    }
    (t, negated)
}

/// Decode `(= a b)` → `(a, b)`.
/// Whether `t` is an integer constant term (`(Const (Int n))`).
fn is_int_const_local(terms: &TermStore, t: TermId) -> bool {
    matches!(terms.get(t), TermData::Const(Constant::Int(_)))
}

fn decode_eq_local(terms: &TermStore, t: TermId) -> Option<(TermId, TermId)> {
    match terms.get(t) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Which strict validator refutes the endpoint equality reached by
/// [`Executor::replace_with_exact_authored_equality_chain_refutation`].
///
/// Selected by the checker's own recognizer, never asserted by the producer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EndpointRefutation {
    /// `TheoryLemmaKind::LiaGeneric` with an `Divisibility` annotation.
    LiaDivisibility,
    /// `TheoryLemmaKind::BvBitBlast` — re-derived by exhaustive bounded
    /// evaluation or a replayed bit-blast/LRAT refutation.
    BvBitBlast,
}

/// Decode a function application → `(symbol, args)`.
fn as_app_local(terms: &TermStore, t: TermId) -> Option<(Symbol, Vec<TermId>)> {
    match terms.get(t) {
        TermData::App(sym, args) => Some((sym.clone(), args.clone())),
        _ => None,
    }
}

/// Exact proof plan for the compact shadowed-store equality theorem generated
/// by `add_shadowed_store_equality_axioms`.
struct ShadowedStoreEqualityProofPlan {
    original_clause: Vec<TermId>,
    flat_clause: Vec<TermId>,
    packed_or: Option<TermId>,
    not_array_eq: TermId,
    lhs_outer: TermId,
    rhs_outer: TermId,
    lhs_inner: TermId,
    rhs_inner: TermId,
    inner_index: TermId,
    outer_index_eq: TermId,
    lhs_value: TermId,
    rhs_value: TermId,
    value_eq: TermId,
}

fn store_parts_local(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
            Some((args[0], args[1], args[2]))
        }
        _ => None,
    }
}

fn select_parts_local(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "select" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Recognize the context-dependent unit equality
///
/// ```text
/// select(store(a, i, v), j) = select(a, j)
/// ```
///
/// in either equality orientation, returning `(i, j)`.  This deliberately
/// does not claim the unit is valid; callers must recover the `i != j`
/// hypothesis and build the guarded ROW2 clause.
fn row2_unit_indices_local(terms: &TermStore, equality: TermId) -> Option<(TermId, TermId)> {
    let (lhs, rhs) = decode_eq_local(terms, equality)?;
    for (store_read, base_read) in [(lhs, rhs), (rhs, lhs)] {
        let Some((store, read_index)) = select_parts_local(terms, store_read) else {
            continue;
        };
        let Some((base, store_index, _)) = store_parts_local(terms, store) else {
            continue;
        };
        let Some((other_base, other_read_index)) = select_parts_local(terms, base_read) else {
            continue;
        };
        if base == other_base && read_index == other_read_index && store_index != read_index {
            return Some((store_index, read_index));
        }
    }
    None
}

fn equality_matches_pair_local(
    terms: &TermStore,
    equality: TermId,
    expected_lhs: TermId,
    expected_rhs: TermId,
) -> bool {
    decode_eq_local(terms, equality).is_some_and(|(lhs, rhs)| {
        (lhs == expected_lhs && rhs == expected_rhs) || (lhs == expected_rhs && rhs == expected_lhs)
    })
}

/// Recognize exactly
///
/// ```text
/// not (= (store (store a i v) j x)
///        (store (store a i w) j x))
/// OR (= i j)
/// OR (= v w)
/// ```
///
/// either as a flat clause or as a unit whose term is that disjunction.  The
/// clause normally has three literals; it has two when `(= i j)` and `(= v w)`
/// are the very same term and `mk_or` removes the duplicate.  No contextual
/// matching is permitted here: every shared component must be the same
/// `TermId`.
fn plan_shadowed_store_equality_proof(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<ShadowedStoreEqualityProofPlan> {
    let (flat_clause, packed_or) = match clause {
        [only] => match terms.get(*only) {
            TermData::App(Symbol::Named(name), args) if name == "or" => (args.clone(), Some(*only)),
            _ => return None,
        },
        _ => (clause.to_vec(), None),
    };
    if !(2..=3).contains(&flat_clause.len()) {
        return None;
    }

    for &not_array_eq in &flat_clause {
        let TermData::Not(array_eq) = terms.get(not_array_eq) else {
            continue;
        };
        let Some((lhs_outer, rhs_outer)) = decode_eq_local(terms, *array_eq) else {
            continue;
        };
        if !matches!(terms.sort(lhs_outer), Sort::Array(_))
            || terms.sort(lhs_outer) != terms.sort(rhs_outer)
        {
            continue;
        }

        let Some((lhs_inner, lhs_outer_index, lhs_outer_value)) =
            store_parts_local(terms, lhs_outer)
        else {
            continue;
        };
        let Some((rhs_inner, rhs_outer_index, rhs_outer_value)) =
            store_parts_local(terms, rhs_outer)
        else {
            continue;
        };
        if lhs_outer_index != rhs_outer_index || lhs_outer_value != rhs_outer_value {
            continue;
        }

        let Some((lhs_base, lhs_inner_index, lhs_value)) = store_parts_local(terms, lhs_inner)
        else {
            continue;
        };
        let Some((rhs_base, rhs_inner_index, rhs_value)) = store_parts_local(terms, rhs_inner)
        else {
            continue;
        };
        if lhs_base != rhs_base
            || lhs_inner_index != rhs_inner_index
            || lhs_inner_index == lhs_outer_index
            || lhs_value == rhs_value
        {
            continue;
        }

        let mut outer_index_eq = None;
        let mut value_eq = None;
        for &literal in &flat_clause {
            if literal == not_array_eq {
                continue;
            }
            let mut matched = false;
            if equality_matches_pair_local(terms, literal, lhs_inner_index, lhs_outer_index) {
                if outer_index_eq.is_some_and(|existing| existing != literal) {
                    return None;
                }
                outer_index_eq = Some(literal);
                matched = true;
            }
            if equality_matches_pair_local(terms, literal, lhs_value, rhs_value) {
                if value_eq.is_some_and(|existing| existing != literal) {
                    return None;
                }
                value_eq = Some(literal);
                matched = true;
            }
            if !matched {
                return None;
            }
        }
        let (Some(outer_index_eq), Some(value_eq)) = (outer_index_eq, value_eq) else {
            continue;
        };
        // Exactly one positive literal is valid only for the genuine duplicate
        // case; with two positives the two theorem roles must remain distinct.
        if (flat_clause.len() == 2) != (outer_index_eq == value_eq) {
            continue;
        }

        return Some(ShadowedStoreEqualityProofPlan {
            original_clause: clause.to_vec(),
            flat_clause,
            packed_or,
            not_array_eq,
            lhs_outer,
            rhs_outer,
            lhs_inner,
            rhs_inner,
            inner_index: lhs_inner_index,
            outer_index_eq,
            lhs_value,
            rhs_value,
            value_eq,
        });
    }

    None
}

fn raw_select_local(terms: &mut TermStore, array: TermId, index: TermId) -> Option<TermId> {
    let Sort::Array(array_sort) = terms.sort(array).clone() else {
        return None;
    };
    if terms.sort(index) != &array_sort.index_sort {
        return None;
    }
    Some(terms.mk_app(
        Symbol::named("select"),
        [array, index],
        array_sort.element_sort,
    ))
}

fn push_proof_step_local(steps: &mut Vec<ProofStep>, step: ProofStep) -> ProofId {
    let id = ProofId(steps.len() as u32);
    steps.push(step);
    id
}

fn clauses_match_as_sets_local(lhs: &[TermId], rhs: &[TermId]) -> bool {
    lhs.iter().all(|term| rhs.contains(term)) && rhs.iter().all(|term| lhs.contains(term))
}

fn push_th_resolution_local(
    steps: &mut Vec<ProofStep>,
    lhs_id: ProofId,
    lhs_clause: &[TermId],
    rhs_id: ProofId,
    rhs_clause: &[TermId],
    pivot_pos: TermId,
    pivot_neg: TermId,
) -> (ProofId, Vec<TermId>) {
    let resolvent = binary_set_resolvent(lhs_clause, rhs_clause, pivot_pos, pivot_neg);
    let id = push_proof_step_local(
        steps,
        ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: resolvent.clone(),
            premises: vec![lhs_id, rhs_id],
            args: Vec::new(),
        },
    );
    (id, resolvent)
}

/// Emit the primitive proof for one exact shadowed-store equality plan.
/// Returns the replacement step id whose clause is byte-for-byte the original
/// compact lemma representation (flat, or a packed unit `(or ...)`).
fn emit_shadowed_store_equality_proof(
    terms: &mut TermStore,
    steps: &mut Vec<ProofStep>,
    plan: &ShadowedStoreEqualityProofPlan,
) -> Option<ProofId> {
    let lhs_outer_read = raw_select_local(terms, plan.lhs_outer, plan.inner_index)?;
    let rhs_outer_read = raw_select_local(terms, plan.rhs_outer, plan.inner_index)?;
    let lhs_inner_read = raw_select_local(terms, plan.lhs_inner, plan.inner_index)?;
    let rhs_inner_read = raw_select_local(terms, plan.rhs_inner, plan.inner_index)?;

    let select_eq = terms.mk_eq(lhs_outer_read, rhs_outer_read);
    let lhs_row2_eq = terms.mk_eq(lhs_outer_read, lhs_inner_read);
    let rhs_row2_eq = terms.mk_eq(rhs_outer_read, rhs_inner_read);
    let lhs_row1_eq = terms.mk_eq(lhs_inner_read, plan.lhs_value);
    let rhs_row1_eq = terms.mk_eq(rhs_inner_read, plan.rhs_value);

    // `select` is binary.  Reuse the generic congruence emitter so the
    // unchanged index position is justified by a raw reflexive equality and
    // resolved away, rather than silently omitting a required premise.
    let congruence_plans = vec![
        (plan.lhs_outer, plan.rhs_outer, vec![plan.not_array_eq]),
        (plan.inner_index, plan.inner_index, Vec::new()),
    ];
    let (select_cong_id, select_cong_clause) =
        emit_congruence_split_steps(terms, steps, &congruence_plans, select_eq, true);
    if !clauses_match_as_sets_local(&select_cong_clause, &[plan.not_array_eq, select_eq]) {
        return None;
    }

    // Preserve the inner reads in raw syntax.  `mk_select` would fold each one
    // directly to the stored value and turn the ROW2 clauses below into
    // derived ROW2+ROW1 consequences that the strict ROW checker must reject.
    let lhs_row1_id = push_proof_step_local(
        steps,
        ProofStep::TheoryLemma {
            theory: "array".to_string(),
            clause: vec![lhs_row1_eq],
            farkas: None,
            kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
            lia: None,
        },
    );
    let rhs_row1_id = push_proof_step_local(
        steps,
        ProofStep::TheoryLemma {
            theory: "array".to_string(),
            clause: vec![rhs_row1_eq],
            farkas: None,
            kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
            lia: None,
        },
    );
    let lhs_row2_clause = vec![plan.outer_index_eq, lhs_row2_eq];
    let lhs_row2_id = push_proof_step_local(
        steps,
        ProofStep::TheoryLemma {
            theory: "array".to_string(),
            clause: lhs_row2_clause.clone(),
            farkas: None,
            kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
            lia: None,
        },
    );
    let rhs_row2_clause = vec![plan.outer_index_eq, rhs_row2_eq];
    let rhs_row2_id = push_proof_step_local(
        steps,
        ProofStep::TheoryLemma {
            theory: "array".to_string(),
            clause: rhs_row2_clause.clone(),
            farkas: None,
            kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
            lia: None,
        },
    );

    // v = innerL = outerL = outerR = innerR = w.
    let not_select_eq = terms.mk_not(select_eq);
    let not_lhs_row2_eq = terms.mk_not(lhs_row2_eq);
    let not_rhs_row2_eq = terms.mk_not(rhs_row2_eq);
    let not_lhs_row1_eq = terms.mk_not(lhs_row1_eq);
    let not_rhs_row1_eq = terms.mk_not(rhs_row1_eq);
    let transitive_clause = vec![
        not_lhs_row1_eq,
        not_lhs_row2_eq,
        not_select_eq,
        not_rhs_row2_eq,
        not_rhs_row1_eq,
        plan.value_eq,
    ];
    let transitive_id = push_proof_step_local(
        steps,
        ProofStep::Step {
            rule: AletheRule::EqTransitive,
            clause: transitive_clause.clone(),
            premises: Vec::new(),
            args: Vec::new(),
        },
    );

    let (mut current_id, mut current_clause) = push_th_resolution_local(
        steps,
        transitive_id,
        &transitive_clause,
        select_cong_id,
        &select_cong_clause,
        select_eq,
        not_select_eq,
    );
    (current_id, current_clause) = push_th_resolution_local(
        steps,
        current_id,
        &current_clause,
        lhs_row2_id,
        &lhs_row2_clause,
        lhs_row2_eq,
        not_lhs_row2_eq,
    );
    (current_id, current_clause) = push_th_resolution_local(
        steps,
        current_id,
        &current_clause,
        rhs_row2_id,
        &rhs_row2_clause,
        rhs_row2_eq,
        not_rhs_row2_eq,
    );
    (current_id, current_clause) = push_th_resolution_local(
        steps,
        current_id,
        &current_clause,
        lhs_row1_id,
        &[lhs_row1_eq],
        lhs_row1_eq,
        not_lhs_row1_eq,
    );
    (current_id, current_clause) = push_th_resolution_local(
        steps,
        current_id,
        &current_clause,
        rhs_row1_id,
        &[rhs_row1_eq],
        rhs_row1_eq,
        not_rhs_row1_eq,
    );

    if !clauses_match_as_sets_local(&current_clause, &plan.flat_clause) {
        return None;
    }

    if let Some(or_term) = plan.packed_or {
        // Convert the derived flat clause back to the unit formula used by the
        // assertion-level proof tracker.  For every disjunct d, `or_neg`
        // supplies `(or D) OR (not d)`; resolving all d leaves `(or D)`.
        for &disjunct in &plan.flat_clause {
            let negated_disjunct = terms.mk_not_raw(disjunct);
            let or_neg_clause = vec![or_term, negated_disjunct];
            let or_neg_id = push_proof_step_local(
                steps,
                ProofStep::Step {
                    rule: AletheRule::OrNeg,
                    clause: or_neg_clause.clone(),
                    premises: Vec::new(),
                    args: Vec::new(),
                },
            );
            (current_id, current_clause) = push_th_resolution_local(
                steps,
                current_id,
                &current_clause,
                or_neg_id,
                &or_neg_clause,
                negated_disjunct,
                disjunct,
            );
        }
    }

    if !clauses_match_as_sets_local(&current_clause, &plan.original_clause) {
        return None;
    }
    // Clause order is semantically irrelevant, but preserving the exact old
    // vector keeps downstream proof-id substitution and deterministic output
    // maximally transparent.
    match &mut steps[current_id.0 as usize] {
        ProofStep::Step { clause, .. } | ProofStep::Resolution { clause, .. } => {
            *clause = plan.original_clause.clone();
        }
        _ => return None,
    }
    Some(current_id)
}

/// Plan the decomposition of a fused EUF congruence-over-equalities clause
/// `(cl ¬(=…) … ¬(=…) (= (f A) (f B)))`. Returns one `(Aᵢ, Bᵢ, chain)` per
/// argument position, where `chain` is the list of premise literals forming the
/// transitive path `Aᵢ`→`Bᵢ` (empty iff `Aᵢ == Bᵢ`, a reflexive position).
///
/// Returns `None` (→ fall back to the trust lemma) unless:
/// - the conclusion is a positive `(= (f A) (f B))` with the SAME symbol and
///   equal, non-zero arity;
/// - every premise is a negated equality;
/// - the per-position argument pairs `(Aᵢ, Bᵢ)` are pairwise DISTINCT (so the
///   `eq_congruent` premises and resolution pivots are unambiguous);
/// - the premise edges partition into EDGE-DISJOINT chains that use EVERY premise
///   exactly once (no shared/redundant premises). The chain check mirrors
///   `validate_euf_transitive` so each emitted `eq_transitive` validates.
fn plan_euf_congruence_split(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<Vec<(TermId, TermId, Vec<TermId>)>> {
    if clause.is_empty() {
        return None;
    }
    let last = *clause.last()?;
    let (inner, neg) = strip_not_local(terms, last);
    if neg {
        return None;
    }
    let (l, r) = decode_eq_local(terms, inner)?;
    let (lsym, largs) = as_app_local(terms, l)?;
    let (rsym, rargs) = as_app_local(terms, r)?;
    if lsym != rsym || largs.is_empty() || largs.len() != rargs.len() {
        return None;
    }

    // Premises → undirected edges, each tagged with its literal id.
    let mut edges: Vec<(TermId, TermId, TermId)> = Vec::with_capacity(clause.len() - 1);
    for &lit in &clause[..clause.len() - 1] {
        let (pi, pneg) = strip_not_local(terms, lit);
        if !pneg {
            return None;
        }
        let (a, b) = decode_eq_local(terms, pi)?;
        edges.push((a, b, lit));
    }

    let mut plans: Vec<(TermId, TermId, Vec<TermId>)> = Vec::with_capacity(largs.len());
    let mut used: Vec<TermId> = Vec::new();
    for (ai, bi) in largs.iter().copied().zip(rargs.iter().copied()) {
        if ai == bi {
            // Reflexive position: synthesized `(= Aᵢ Aᵢ)` premise, no chain edges.
            plans.push((ai, bi, Vec::new()));
        } else {
            // Each varying position is reached by a chain of premise equalities.
            // Positions may SHARE a chain (e.g. `g(a,a)=g(b,b)`); the resolution
            // chain deduplicates, and the `check_proof` gate is the backstop.
            let path = euf_chain_path(&edges, ai, bi)?;
            for lit in &path {
                if !used.contains(lit) {
                    used.push(*lit);
                }
            }
            plans.push((ai, bi, path));
        }
    }
    // Every premise must be accounted for by some position's chain (no redundant
    // premise the resolution chain cannot consume).
    if used.len() != edges.len() {
        return None;
    }
    Some(plans)
}

/// Emit the per-position `eq_transitive`/`eq_reflexive` derivations, the
/// `eq_congruent` step over the direct per-argument equalities, and the binary
/// `th_resolution` chain that discharges each per-argument equality — the
/// shared emission core of the pure congruence split and the relational
/// (class-4) split. `plans` comes from [`plan_euf_congruence_split`]; `conc`
/// is the congruence conclusion `(= (f A) (f B))`. Returns the id and clause
/// of the final resolvent `(cl <chain ¬eqs> conc)`.
fn emit_congruence_split_steps(
    terms: &mut TermStore,
    new_steps: &mut Vec<ProofStep>,
    plans: &[(TermId, TermId, Vec<TermId>)],
    conc: TermId,
    direct_single_edges: bool,
) -> (ProofId, Vec<TermId>) {
    // (1) Per-position derivation of each `(= Aᵢ Bᵢ)`.
    let mut derivs: Vec<(ProofId, TermId, TermId)> = Vec::new(); // (id, pos_eq, neg_eq)
    let mut g_premises: Vec<TermId> = Vec::with_capacity(plans.len());
    for (ai, bi, chain) in plans {
        // Single-edge chain whose premise equality IS `(= Aᵢ Bᵢ)` (either
        // orientation): use the original literal directly as the eq_congruent
        // premise. A 1-edge `eq_transitive` would be the degenerate 2-term
        // clause `(cl ¬E E)`, which external checkers reject (`eq_transitive`
        // requires >= 3 terms). The literal then survives into the final
        // resolvent, exactly as the fused clause carries it.
        if direct_single_edges && chain.len() == 1 {
            let (e, _) = strip_not_local(terms, chain[0]);
            if let Some((p, q)) = decode_eq_local(terms, e) {
                if (p == *ai && q == *bi) || (p == *bi && q == *ai) {
                    g_premises.push(chain[0]);
                    continue;
                }
            }
        }
        let did = ProofId(new_steps.len() as u32);
        let pos_eq = if chain.is_empty() {
            // Reflexive position. `mk_eq(x, x)` folds to
            // `true`, which would degenerate the eq_congruent
            // premise — so build the RAW `(= x x)` via `mk_app`
            // (no reflexive folding) and discharge it with
            // eq_reflexive. The raw term lives only inside this
            // split's steps (it is resolved away before the
            // final clause), so no non-canonical term escapes.
            let raw_eq = terms.mk_app(Symbol::named("="), [*ai, *ai], Sort::Bool);
            new_steps.push(ProofStep::Step {
                rule: AletheRule::EqReflexive,
                clause: vec![raw_eq],
                premises: Vec::new(),
                args: Vec::new(),
            });
            raw_eq
        } else {
            let pos_eq = terms.mk_eq(*ai, *bi);
            let mut t_clause = chain.clone();
            t_clause.push(pos_eq);
            new_steps.push(ProofStep::Step {
                rule: AletheRule::EqTransitive,
                clause: t_clause,
                premises: Vec::new(),
                args: Vec::new(),
            });
            pos_eq
        };
        let neg_eq = terms.mk_not(pos_eq);
        g_premises.push(neg_eq);
        derivs.push((did, pos_eq, neg_eq));
    }

    // (2) The congruence over the direct per-argument equalities.
    let mut g_clause = g_premises;
    g_clause.push(conc);
    let g_id = ProofId(new_steps.len() as u32);
    let mut cur_clause = g_clause.clone();
    new_steps.push(ProofStep::Step {
        rule: AletheRule::EqCongruent,
        clause: g_clause,
        premises: Vec::new(),
        args: Vec::new(),
    });

    // (3) Resolve the congruence against each position's
    // derivation on the pivot `(= Aᵢ Bᵢ)`.
    let mut cur_id = g_id;
    for (did, pos_eq, neg_eq) in &derivs {
        let deriv_clause = match &new_steps[did.0 as usize] {
            ProofStep::Step { clause, .. } => clause.clone(),
            _ => unreachable!("derivation is always a Step"),
        };
        let resolvent = binary_set_resolvent(&cur_clause, &deriv_clause, *pos_eq, *neg_eq);
        let rid = ProofId(new_steps.len() as u32);
        new_steps.push(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: resolvent.clone(),
            premises: vec![cur_id, *did],
            args: Vec::new(),
        });
        cur_id = rid;
        cur_clause = resolvent;
    }
    (cur_id, cur_clause)
}

/// A plan for the EUF-congruence-chain + arithmetic-comparison split (class 4).
struct RelationalCongruencePlan {
    /// Per-position `(Aᵢ, Bᵢ, chain)` plans (from [`plan_euf_congruence_split`]).
    plans: Vec<(TermId, TermId, Vec<TermId>)>,
    /// `(= (f A) (f B))` — the synthesized congruence conclusion.
    cong_eq: TermId,
    /// `¬(= (f A) (f B))`.
    cong_neg: TermId,
    /// The arithmetic bridge clause `(cl ¬(= (f A) (f B)) ¬(R (f A) (f B)))`.
    la_clause: Vec<TermId>,
    /// Its solver-synthesized Farkas certificate.
    la_farkas: FarkasAnnotation,
    /// The certified kind reported by the Farkas reconstruction.
    la_kind: TheoryLemmaKind,
}

/// Recognize a fused cross-theory EUF+arith conflict
/// `(cl ¬(=A1 B1) … ¬(=Am Bm) ¬(R s t))` where `R ∈ {<, <=, >, >=}`, `s` and
/// `t` are applications of the SAME symbol with equal arity, and the premise
/// equalities chain-connect every argument position (using EVERY premise) —
/// e.g. `x=y ∧ f(x)<f(y) ⊢ ⊥`, `a=b ∧ b=c ∧ f(a)>f(c) ⊢ ⊥`. Returns the
/// pieces to emit the congruence derivation + a solver-checked `la_generic`
/// bridge (`(= s t)` contradicts `(R s t)` with `s`, `t` as opaque atoms) +
/// their resolution. `None` (→ fall back) for any other shape; the
/// `check_proof` revert gate is the final backstop.
fn plan_euf_relational_congruence(
    terms: &mut TermStore,
    clause: &[TermId],
) -> Option<RelationalCongruencePlan> {
    if clause.len() < 2 {
        return None;
    }
    // Exactly one negated arithmetic comparison; every other literal a
    // negated equality.
    let mut rel_idx: Option<usize> = None;
    for (i, &lit) in clause.iter().enumerate() {
        let (inner, neg) = strip_not_local(terms, lit);
        if !neg {
            return None;
        }
        if decode_eq_local(terms, inner).is_some() {
            continue;
        }
        if is_arith_cmp(terms, inner) {
            if rel_idx.replace(i).is_some() {
                return None;
            }
        } else {
            return None;
        }
    }
    let rel_idx = rel_idx?;
    let rel_lit = clause[rel_idx];
    let (rel_atom, _) = strip_not_local(terms, rel_lit);
    let (_, cmp_args) = as_app_local(terms, rel_atom)?;
    let (s, t) = (cmp_args[0], cmp_args[1]);
    if s == t {
        return None;
    }
    let (ssym, sargs) = as_app_local(terms, s)?;
    let (tsym, targs) = as_app_local(terms, t)?;
    if ssym != tsym || sargs.is_empty() || sargs.len() != targs.len() {
        return None;
    }

    // Synthesize the congruence conclusion and plan its derivation over the
    // equality premises (which must chain-connect every argument position and
    // use every premise).
    let cong_eq = terms.mk_eq(s, t);
    // Fail-closed on constant-fold surprises: `cong_eq` must still decode as an
    // equality application; the decoded operand pair itself is not needed.
    let _ = decode_eq_local(terms, cong_eq)?;
    let mut euf_clause: Vec<TermId> = clause
        .iter()
        .enumerate()
        .filter(|&(i, _)| i != rel_idx)
        .map(|(_, &l)| l)
        .collect();
    euf_clause.push(cong_eq);
    let plans = plan_euf_congruence_split(terms, &euf_clause)?;

    // The arithmetic bridge, certified by the real LRA solver (uninterpreted
    // atoms are opaque variables to the simplex replay and to the semantic
    // Farkas verifier that re-checks the lemma in strict mode).
    let cong_neg = terms.mk_not(cong_eq);
    let la_clause = vec![cong_neg, rel_lit];
    let mut la_farkas = None;
    let mut la_kind = TheoryLemmaKind::LiaGeneric;
    if !super::proof_farkas::try_lra_farkas_reconstruction(
        terms,
        &la_clause,
        &mut la_farkas,
        &mut la_kind,
    ) {
        return None;
    }
    Some(RelationalCongruencePlan {
        plans,
        cong_eq,
        cong_neg,
        la_clause,
        la_farkas: la_farkas?,
        la_kind,
    })
}

/// A plan for the congruence-then-transitivity-to-a-value split.
struct ValuePlan {
    /// The per-argument substitution premises `¬(= Aᵢ Bᵢ)` — reused as the
    /// eq_congruent premises (in argument order).
    cong_premises: Vec<TermId>,
    /// `(= (g A) (g B))`, the congruence conclusion.
    cong_eq: TermId,
    /// `¬(= (g A) (g B))`, the bridging edge in the transitivity chain.
    cong_neg: TermId,
    /// The remaining premise literals — the chain from `(g A)` to the value.
    chain_to_value: Vec<TermId>,
    /// The fused conclusion `(= (g B) V)`.
    conc: TermId,
}

/// Recognize a fused EUF/UFLIA lemma that proves an equality to a VALUE via one
/// (possibly n-ary) congruence feeding a transitivity chain: `(cl ¬(=A1 B1) …
/// ¬(=Am Bm) <chain ¬eqs> (= (g B) V))` where the per-argument substitutions
/// `Aᵢ = Bᵢ` lift to the congruence `(g A) = (g B)`, and the chain `(g B) =
/// (g A) = … = V` reaches `V`. Covers `f(a)=5 ∧ a=3 ⊢ f(3)=5` (unary) and
/// `g(a,c)=v ∧ a=b ∧ c=d ⊢ g(b,d)=v` (n-ary), with both conclusion orientations
/// and a multi-edge chain to the value.
///
/// Returns the pieces to emit `eq_congruent` + `eq_transitive` + their
/// resolution; `None` (→ fall back) for any other shape. Each argument needs a
/// DIRECT substitution premise (reflexive/chained arguments fall back). The chain
/// reachability is checked here (mirroring `validate_euf_transitive`); the
/// `check_proof` revert gate is the final backstop.
fn plan_euf_value_congruence(terms: &mut TermStore, clause: &[TermId]) -> Option<ValuePlan> {
    if clause.len() < 2 {
        return None;
    }
    let conc = *clause.last()?;
    let (cinner, cneg) = strip_not_local(terms, conc);
    if cneg {
        return None;
    }
    let (x, y) = decode_eq_local(terms, cinner)?;
    let premises: Vec<TermId> = clause[..clause.len() - 1].to_vec();

    for &(gb, v) in &[(x, y), (y, x)] {
        let Some((gsym, gb_args)) = as_app_local(terms, gb) else {
            continue;
        };
        if gb_args.is_empty() {
            continue;
        }
        let gb_sort = terms.sort(gb).clone();

        // For each argument position (in order), find a DIRECT substitution
        // premise `¬(= Aᵢ Bᵢ)`; collect the `Aᵢ` to form `(g A)`.
        let mut a_args: Vec<TermId> = Vec::with_capacity(gb_args.len());
        let mut used: Vec<usize> = Vec::new();
        let mut cong_premises: Vec<TermId> = Vec::new();
        let mut all_args_ok = true;
        for &bi in &gb_args {
            let mut found = false;
            for (j, &lit) in premises.iter().enumerate() {
                if used.contains(&j) {
                    continue;
                }
                let (li, lneg) = strip_not_local(terms, lit);
                if !lneg {
                    continue;
                }
                let Some((p, q)) = decode_eq_local(terms, li) else {
                    continue;
                };
                let ai = if p == bi {
                    q
                } else if q == bi {
                    p
                } else {
                    continue;
                };
                if ai == bi {
                    continue;
                }
                a_args.push(ai);
                used.push(j);
                cong_premises.push(lit);
                found = true;
                break;
            }
            if !found {
                all_args_ok = false;
                break;
            }
        }
        if !all_args_ok {
            continue;
        }

        let ga = terms.mk_app(gsym.clone(), a_args.as_slice(), gb_sort.clone());
        if ga == gb {
            continue;
        }
        let cong_eq = terms.mk_eq(ga, gb);
        let cong_neg = terms.mk_not(cong_eq);

        // The remaining premises + the congruence bridge `(g A)~(g B)` must form a
        // transitive chain `(g B) → … → V` using every edge.
        let chain_to_value: Vec<TermId> = premises
            .iter()
            .enumerate()
            .filter(|(j, _)| !used.contains(j))
            .map(|(_, &l)| l)
            .collect();
        let mut t_edges: Vec<(TermId, TermId, TermId)> = vec![(ga, gb, cong_neg)];
        let mut edges_ok = true;
        for &l in &chain_to_value {
            let (li, lneg) = strip_not_local(terms, l);
            if !lneg {
                edges_ok = false;
                break;
            }
            let Some((ra, rb)) = decode_eq_local(terms, li) else {
                edges_ok = false;
                break;
            };
            t_edges.push((ra, rb, l));
        }
        if !edges_ok {
            continue;
        }
        if let Some(path) = euf_chain_path(&t_edges, gb, v) {
            if path.len() == t_edges.len() {
                return Some(ValuePlan {
                    cong_premises,
                    cong_eq,
                    cong_neg,
                    chain_to_value,
                    conc,
                });
            }
        }
    }
    None
}

/// A plan for the cross-theory EUF-congruence + LIA-conflict split.
struct LiaValuePlan {
    /// `¬(= A B)` — the substitution premise / eq_congruent premise.
    sub_lit: TermId,
    /// `(= (f A) (f B))` — the congruence conclusion.
    cong_eq: TermId,
    /// `¬(= (f A) (f B))`.
    cong_neg: TermId,
    /// `¬(= (f A) v)` — the value premise, used in the transitivity chain.
    val_lit: TermId,
    /// `(= (f B) v)` — the derived equality (eq_transitive conclusion).
    derived_eq: TermId,
    /// `¬(= (f B) v)`.
    derived_neg: TermId,
    /// The LIA conflict clause `(cl ¬(= (f B) v) ¬arith)` — its second literal
    /// is the arithmetic conflict literal `¬(arith on (f B))`.
    la_clause: Vec<TermId>,
    /// Its solver-synthesized Farkas certificate.
    la_farkas: FarkasAnnotation,
}

/// `(R a b)` with `R` a linear-arithmetic comparison.
fn is_arith_cmp(terms: &TermStore, t: TermId) -> bool {
    matches!(terms.get(t),
        TermData::App(Symbol::Named(n), args)
            if args.len() == 2 && matches!(n.as_str(), "<" | "<=" | ">" | ">="))
}

/// Recognize a fused cross-theory EUF+LIA conflict
/// `(cl ¬(R (f B) ·) ¬(= A B) ¬(= (f A) v))` — e.g. `f(a)=5 ∧ a=b ∧ f(b)>5 ⊢ ⊥`
/// — where the substitution `A=B` lifts (congruence) to `(f A)=(f B)`, the value
/// `(f A)=v` transports (transitivity) to `(f B)=v`, and `(f B)=v` contradicts
/// the arithmetic literal. Returns the pieces to emit `eq_congruent` +
/// `eq_transitive` + a solver-checked `la_generic` + their resolution.
///
/// Unary `f`, single substitution, exactly three literals — the common
/// "function value with an arithmetic constraint" pattern. The LIA Farkas is
/// synthesized by the real LRA solver (`try_lra_farkas_reconstruction`), so it is
/// valid by construction; the `check_proof` revert gate is the final backstop.
fn plan_euf_lia_value_conflict(terms: &mut TermStore, clause: &[TermId]) -> Option<LiaValuePlan> {
    if clause.len() != 3 {
        return None;
    }
    for ai in 0..3 {
        let arith_lit = clause[ai];
        let (a_inner, a_neg) = strip_not_local(terms, arith_lit);
        if !a_neg || !is_arith_cmp(terms, a_inner) {
            continue;
        }
        let Some((_, cmp_args)) = as_app_local(terms, a_inner) else {
            continue;
        };
        for &fb in &cmp_args {
            let Some((fsym, fb_args)) = as_app_local(terms, fb) else {
                continue;
            };
            if fb_args.len() != 1 {
                continue;
            }
            let b = fb_args[0];
            for vi in 0..3 {
                if vi == ai {
                    continue;
                }
                let val_lit = clause[vi];
                let (v_inner, v_neg) = strip_not_local(terms, val_lit);
                if !v_neg {
                    continue;
                }
                let Some((p, q)) = decode_eq_local(terms, v_inner) else {
                    continue;
                };
                for &(fa, v) in &[(p, q), (q, p)] {
                    let Some((fasym, fa_args)) = as_app_local(terms, fa) else {
                        continue;
                    };
                    if fasym != fsym || fa_args.len() != 1 {
                        continue;
                    }
                    let a = fa_args[0];
                    if a == b || fa == fb {
                        continue;
                    }
                    let si = 3 - ai - vi; // the remaining literal index
                    let sub_lit = clause[si];
                    let (s_inner, s_neg) = strip_not_local(terms, sub_lit);
                    if !s_neg {
                        continue;
                    }
                    let Some((sp, sq)) = decode_eq_local(terms, s_inner) else {
                        continue;
                    };
                    if !((sp == a && sq == b) || (sp == b && sq == a)) {
                        continue;
                    }
                    // Build the derived equality `(= (f B) v)` and the LIA conflict
                    // clause, then have the LRA solver synthesize its Farkas.
                    let derived_eq = terms.mk_eq(fb, v);
                    let derived_neg = terms.mk_not(derived_eq);
                    let la_clause = vec![derived_neg, arith_lit];
                    let mut la_farkas = None;
                    let mut la_kind = TheoryLemmaKind::LiaGeneric;
                    if !super::proof_farkas::try_lra_farkas_reconstruction(
                        terms,
                        &la_clause,
                        &mut la_farkas,
                        &mut la_kind,
                    ) {
                        continue;
                    }
                    let la_farkas = la_farkas?;
                    let cong_eq = terms.mk_eq(fa, fb);
                    let cong_neg = terms.mk_not(cong_eq);
                    return Some(LiaValuePlan {
                        sub_lit,
                        cong_eq,
                        cong_neg,
                        val_lit,
                        derived_eq,
                        derived_neg,
                        la_clause,
                        la_farkas,
                    });
                }
            }
        }
    }
    None
}

/// Return the premise literals on a simple path `x`→`y` over the undirected
/// `edges` (BFS), or `None` if `x` and `y` are not connected — mirroring the
/// reachability `validate_euf_transitive` requires.
fn euf_chain_path(edges: &[(TermId, TermId, TermId)], x: TermId, y: TermId) -> Option<Vec<TermId>> {
    use std::collections::{HashMap, VecDeque};
    // node -> (prev_node, edge_literal)
    let mut adj: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::new();
    for &(a, b, lit) in edges {
        adj.entry(a).or_default().push((b, lit));
        adj.entry(b).or_default().push((a, lit));
    }
    let mut parent: HashMap<TermId, (TermId, TermId)> = HashMap::new();
    parent.insert(x, (x, x));
    let mut q = VecDeque::new();
    q.push_back(x);
    while let Some(cur) = q.pop_front() {
        if cur == y {
            break;
        }
        if let Some(ns) = adj.get(&cur) {
            for &(nb, lit) in ns {
                if let std::collections::hash_map::Entry::Vacant(slot) = parent.entry(nb) {
                    slot.insert((cur, lit));
                    q.push_back(nb);
                }
            }
        }
    }
    parent.get(&y)?;
    let mut path = Vec::new();
    let mut cur = y;
    while cur != x {
        let (prev, lit) = parent[&cur];
        path.push(lit);
        cur = prev;
    }
    Some(path)
}

/// Binary resolution of `c1` (the clause supplying `pivot_neg`) and `c2` (the
/// clause supplying `pivot_pos`) on the pivot, as a deduplicated literal set:
/// `(c1 \ {pivot_neg}) ∪ (c2 \ {pivot_pos})`.
///
/// Standard resolution removes ONLY the resolved literal from each side — so a
/// `pivot_neg` that also occurs in `c2` (as a non-pivot literal, e.g. the shared
/// chain edge `¬(=a b)` when resolving `g(a,a)=g(b,b)` against its single-edge
/// `eq_transitive`) SURVIVES into the resolvent. Dropping it from `c2` too would
/// be unsound bookkeeping (it would lose a literal the original fused clause
/// keeps); the previous "drop the pivot from both clauses" form only happened to
/// work for edge-disjoint chains where `c2` never carries `pivot_neg`.
fn binary_set_resolvent(
    c1: &[TermId],
    c2: &[TermId],
    pivot_pos: TermId,
    pivot_neg: TermId,
) -> Vec<TermId> {
    let mut out: Vec<TermId> = Vec::with_capacity(c1.len() + c2.len());
    for &l in c1 {
        if l != pivot_neg && !out.contains(&l) {
            out.push(l);
        }
    }
    for &l in c2 {
        if l != pivot_pos && !out.contains(&l) {
            out.push(l);
        }
    }
    out
}

/// Match a true ROW1-negation assertion `(not (= (select (store a i e) i) e))`
/// — both indices the same symbol and the stored value the same symbol as the
/// compared value — returning the `(array, index, value)` symbol names. The
/// select may sit on either side of the equality. Returns `None` for any other
/// shape (fail-closed); only `Symbol` leaves are accepted so the names resolve
/// directly to declared-constant `TermId`s via `TermStore::lookup`.
fn match_row1_negation(asrt: &FrontendTerm) -> Option<(&str, &str, &str)> {
    let FrontendTerm::App(not_op, not_args) = asrt else {
        return None;
    };
    if not_op != "not" || not_args.len() != 1 {
        return None;
    }
    let FrontendTerm::App(eq_op, eq_args) = &not_args[0] else {
        return None;
    };
    if eq_op != "=" || eq_args.len() != 2 {
        return None;
    }
    for (sel_i, val_i) in [(0usize, 1usize), (1, 0)] {
        let FrontendTerm::App(sel_op, sel_args) = &eq_args[sel_i] else {
            continue;
        };
        if sel_op != "select" || sel_args.len() != 2 {
            continue;
        }
        let FrontendTerm::App(store_op, store_args) = &sel_args[0] else {
            continue;
        };
        if store_op != "store" || store_args.len() != 3 {
            continue;
        }
        let (
            FrontendTerm::Symbol(arr),
            FrontendTerm::Symbol(store_idx),
            FrontendTerm::Symbol(store_val),
            FrontendTerm::Symbol(select_idx),
            FrontendTerm::Symbol(compared_val),
        ) = (
            &store_args[0],
            &store_args[1],
            &store_args[2],
            &sel_args[1],
            &eq_args[val_i],
        )
        else {
            continue;
        };
        if store_idx == select_idx && store_val == compared_val {
            return Some((arr, store_idx, store_val));
        }
    }
    None
}

/// Match an authored ROW1 value comparison
/// `(= (select (store a i stored) i) compared)` (either equality
/// orientation), where the store and select indices are the exact same
/// surface term and `stored` differs syntactically from `compared`.
///
/// The returned components are elaborated independently by the caller so the
/// select-over-store application itself can be rebuilt without triggering the
/// eager ROW1 fold.
fn match_row1_value_mismatch(
    assertion: &FrontendTerm,
) -> Option<(
    &FrontendTerm,
    &FrontendTerm,
    &FrontendTerm,
    &FrontendTerm,
    bool,
)> {
    let FrontendTerm::App(eq, args) = assertion else {
        return None;
    };
    if eq != "=" || args.len() != 2 {
        return None;
    }
    for (select_position, compared_position) in [(0usize, 1usize), (1, 0)] {
        let FrontendTerm::App(select, select_args) = &args[select_position] else {
            continue;
        };
        if select != "select" || select_args.len() != 2 {
            continue;
        }
        let FrontendTerm::App(store, store_args) = &select_args[0] else {
            continue;
        };
        if store != "store"
            || store_args.len() != 3
            || store_args[1] != select_args[1]
            || store_args[2] == args[compared_position]
        {
            continue;
        }
        return Some((
            &store_args[0],
            &store_args[1],
            &store_args[2],
            &args[compared_position],
            select_position == 0,
        ));
    }
    None
}

/// Match a datatype selector-projection negation `(not (= (sel (C a_0 .. a_n)) v))`
/// — the selector applied to a constructor application, equated to a symbol —
/// returning `(ctor_name, [arg_symbol], selector_name, value_symbol)`. The
/// selector may sit on either side of the equality. Returns `None` for any other
/// shape (fail-closed); only `Symbol` leaves are accepted so the names resolve to
/// declared-constant `TermId`s. Whether `sel` genuinely projects the field holding
/// `v` is NOT decided here — that is gated by the strict checker's recognizer in
/// the caller, keyed on the constructor→selector registry.
fn match_dt_selector_negation(asrt: &FrontendTerm) -> Option<(&str, Vec<&str>, &str, &str)> {
    let FrontendTerm::App(not_op, not_args) = asrt else {
        return None;
    };
    if not_op != "not" || not_args.len() != 1 {
        return None;
    }
    let FrontendTerm::App(eq_op, eq_args) = &not_args[0] else {
        return None;
    };
    if eq_op != "=" || eq_args.len() != 2 {
        return None;
    }
    for (sel_i, val_i) in [(0usize, 1usize), (1, 0)] {
        let FrontendTerm::App(sel, sel_args) = &eq_args[sel_i] else {
            continue;
        };
        if sel_args.len() != 1 {
            continue;
        }
        let FrontendTerm::App(ctor, ctor_args) = &sel_args[0] else {
            continue;
        };
        let mut arg_syms = Vec::with_capacity(ctor_args.len());
        let mut all_symbols = true;
        for a in ctor_args {
            match a {
                FrontendTerm::Symbol(s) => arg_syms.push(s.as_str()),
                _ => {
                    all_symbols = false;
                    break;
                }
            }
        }
        if !all_symbols {
            continue;
        }
        let FrontendTerm::Symbol(val) = &eq_args[val_i] else {
            continue;
        };
        return Some((ctor.as_str(), arg_syms, sel.as_str(), val.as_str()));
    }
    None
}

/// Same-width bitvector operators whose result sort equals their (first)
/// operand's sort: unary `bvnot`/`bvneg` and the value-producing binary ops.
/// (Width-changing ops — `concat`, `extract`, `*_extend`, `rotate`, `repeat` —
/// are handled by their own `build_bv_pterm` arms with explicit width
/// computation; Bool-producing comparisons `bvult`/… are not equality operands.)
fn bv_samewidth_op_arity(op: &str) -> Option<usize> {
    match op {
        "bvnot" | "bvneg" => Some(1),
        "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor" | "bvadd" | "bvsub"
        | "bvmul" | "bvshl" | "bvlshr" | "bvashr" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem"
        | "bvsmod" => Some(2),
        _ => None,
    }
}

/// Result width of an indexed BV op over an operand of width `src_width` —
/// matching the strict checker's `eval_indexed_bv` exactly. Returns `None` for
/// any op/index shape it does not model (fail-closed). `int2bv` is excluded (its
/// operand is `Int`, not a bitvector, so it is not part of a BV-identity).
fn bv_indexed_result_width(name: &str, indices: &[u32], src_width: u32) -> Option<u32> {
    match name {
        "extract" if indices.len() == 2 => {
            let (hi, lo) = (indices[0], indices[1]);
            (hi >= lo).then(|| hi - lo + 1)
        }
        "zero_extend" | "sign_extend" if indices.len() == 1 => src_width.checked_add(indices[0]),
        "rotate_left" | "rotate_right" if indices.len() == 1 => Some(src_width),
        "repeat" if indices.len() == 1 => src_width.checked_mul(indices[0]),
        _ => None,
    }
}

/// Match an `(ite c x x)`-identity negation `(not (= (ite c x x) x))` — an
/// if-then-else with identical symbol branches, equated to that same symbol —
/// returning `(condition, x)` symbol names. The `ite` may sit on either side.
/// Returns `None` for any other shape (fail-closed); only `Symbol` leaves are
/// accepted so they resolve to declared-constant `TermId`s. The condition is a
/// Bool symbol; `x` may be any sort.
fn match_ite_same_negation(asrt: &FrontendTerm) -> Option<(&str, &str)> {
    let FrontendTerm::App(not_op, not_args) = asrt else {
        return None;
    };
    if not_op != "not" || not_args.len() != 1 {
        return None;
    }
    let FrontendTerm::App(eq_op, eq_args) = &not_args[0] else {
        return None;
    };
    if eq_op != "=" || eq_args.len() != 2 {
        return None;
    }
    for (ite_i, val_i) in [(0usize, 1usize), (1, 0)] {
        let FrontendTerm::App(ite_op, ite_args) = &eq_args[ite_i] else {
            continue;
        };
        if ite_op != "ite" || ite_args.len() != 3 {
            continue;
        }
        let (
            FrontendTerm::Symbol(cond),
            FrontendTerm::Symbol(then_branch),
            FrontendTerm::Symbol(else_branch),
        ) = (&ite_args[0], &ite_args[1], &ite_args[2])
        else {
            continue;
        };
        let FrontendTerm::Symbol(val) = &eq_args[val_i] else {
            continue;
        };
        if then_branch == else_branch && then_branch == val {
            return Some((cond, then_branch));
        }
    }
    None
}

/// Faithfully translate a QF_BV assertion-level frontend term into a `TermId`
/// — the elaborator's translation MINUS the simplifying folds (raw
/// `mk_app`/`mk_not_raw`/`mk_ite_raw`/`mk_bitvec`). This is the boolean layer
/// over [`build_bv_pterm`]'s bitvector fragment: it additionally handles
/// `not`/`and`/`or`/`xor`/`=>`, `=` over Bool or BV sides, the BV comparison
/// predicates, `ite` (Bool condition, Bool or BV branches), Bool-sorted
/// symbols/constants, and the structurally parsed `(_ bvN W)` decimal
/// bitvector spelling. Returns `None` (fail-closed) for
/// anything else, or — the load-bearing soundness guard — for any node the
/// term store FOLDED (the rebuilt term would no longer mirror the surface
/// assertion). Every accepted node is a structure-preserving rebuild, so an
/// `assume` built from the result matches the real input assertion.
fn build_qfbv_pterm(terms: &mut TermStore, pt: &FrontendTerm) -> Option<TermId> {
    match pt {
        FrontendTerm::Symbol(s) => {
            if let Some(id) = terms.lookup(s) {
                return matches!(terms.sort(id), Sort::Bool | Sort::BitVec(_)).then_some(id);
            }
            None
        }
        FrontendTerm::Const(FrontendConstant::True) => Some(terms.true_term()),
        FrontendTerm::Const(FrontendConstant::False) => Some(terms.false_term()),
        FrontendTerm::Const(c) => build_bv_const(terms, c),
        FrontendTerm::IndexedApp(name, indices, args) if args.is_empty() => {
            build_bv_decimal_indexed(terms, name, indices)
        }
        FrontendTerm::App(op, args) if op == "not" && args.len() == 1 => {
            let a = build_qfbv_pterm(terms, &args[0])?;
            if !matches!(terms.sort(a), Sort::Bool) {
                return None;
            }
            let t = terms.mk_not_raw(a);
            matches!(terms.get(t), TermData::Not(inner) if *inner == a).then_some(t)
        }
        FrontendTerm::App(op, args)
            if matches!(op.as_str(), "and" | "or") && args.len() >= 2
                || matches!(op.as_str(), "xor" | "=>") && args.len() == 2 =>
        {
            let arg_ids: Vec<TermId> = args
                .iter()
                .map(|a| build_qfbv_pterm(terms, a))
                .collect::<Option<_>>()?;
            if !arg_ids.iter().all(|&a| matches!(terms.sort(a), Sort::Bool)) {
                return None;
            }
            let t = terms.mk_app(Symbol::named(op), arg_ids.clone(), Sort::Bool);
            matches!(
                terms.get(t),
                TermData::App(sym, a) if sym.name() == op && a.as_slice() == arg_ids.as_slice()
            )
            .then_some(t)
        }
        FrontendTerm::App(op, args) if op == "=" && args.len() == 2 => {
            let l = build_qfbv_pterm(terms, &args[0])?;
            let r = build_qfbv_pterm(terms, &args[1])?;
            if terms.sort(l) != terms.sort(r)
                || !matches!(terms.sort(l), Sort::Bool | Sort::BitVec(_))
            {
                return None;
            }
            let t = terms.mk_app(Symbol::named("="), [l, r], Sort::Bool);
            matches!(
                terms.get(t),
                TermData::App(sym, a) if sym.name() == "=" && a.as_slice() == [l, r]
            )
            .then_some(t)
        }
        FrontendTerm::App(op, args)
            if matches!(
                op.as_str(),
                "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
            ) && args.len() == 2 =>
        {
            let l = build_qfbv_pterm(terms, &args[0])?;
            let r = build_qfbv_pterm(terms, &args[1])?;
            if terms.sort(l) != terms.sort(r) || !matches!(terms.sort(l), Sort::BitVec(_)) {
                return None;
            }
            let t = terms.mk_app(Symbol::named(op), [l, r], Sort::Bool);
            matches!(
                terms.get(t),
                TermData::App(sym, a) if sym.name() == op && a.as_slice() == [l, r]
            )
            .then_some(t)
        }
        FrontendTerm::App(op, args) if op == "ite" => build_qfbv_ite_pterm(terms, args),
        FrontendTerm::App(op, args) if op == "select" => build_qfbv_select_pterm(terms, args),
        // Everything else BV-sorted (same-width ops, concat, indexed ops,
        // hex/binary literals, BV symbols): the existing faithful BV builder.
        // NOTE: subterms of BV ops that need the boolean layer (an `ite`
        // nested under `bvand`, a `(_ bvN W)` operand) are NOT reachable via
        // `build_bv_pterm`'s own recursion, so rebuild those apps here.
        FrontendTerm::App(op, args) => {
            if op == "concat" && args.len() == 2 {
                let a = build_qfbv_pterm(terms, &args[0])?;
                let b = build_qfbv_pterm(terms, &args[1])?;
                let width = terms
                    .sort(a)
                    .bitvec_width()?
                    .checked_add(terms.sort(b).bitvec_width()?)?;
                let t = terms.mk_app(Symbol::named("concat"), vec![a, b], Sort::bitvec(width));
                return matches!(
                    terms.get(t),
                    TermData::App(sym, ar) if sym.name() == "concat" && ar.as_slice() == [a, b]
                )
                .then_some(t);
            }
            let arity = bv_samewidth_op_arity(op)?;
            if args.len() != arity {
                return None;
            }
            let arg_ids: Vec<TermId> = args
                .iter()
                .map(|a| build_qfbv_pterm(terms, a))
                .collect::<Option<_>>()?;
            let sort = terms.sort(arg_ids[0]).clone();
            if !matches!(sort, Sort::BitVec(_)) || !arg_ids.iter().all(|&a| *terms.sort(a) == sort)
            {
                return None;
            }
            let t = terms.mk_app(Symbol::named(op), arg_ids.clone(), sort);
            matches!(
                terms.get(t),
                TermData::App(sym, a) if sym.name() == op && a.as_slice() == arg_ids.as_slice()
            )
            .then_some(t)
        }
        FrontendTerm::IndexedApp(name, idx_strs, args) if args.len() == 1 => {
            let indices: Vec<u32> = idx_strs
                .iter()
                .map(|index| index.as_numeral()?.parse::<u32>().ok())
                .collect::<Option<_>>()?;
            let arg = build_qfbv_pterm(terms, &args[0])?;
            let src_width = terms.sort(arg).bitvec_width()?;
            let width = bv_indexed_result_width(name, &indices, src_width)?;
            let sym = Symbol::indexed(name, indices.clone());
            let t = terms.mk_app(sym, vec![arg], Sort::bitvec(width));
            matches!(
                terms.get(t),
                TermData::App(Symbol::Indexed(n, idx), ar)
                    if n == name && idx.as_slice() == indices.as_slice() && ar.as_slice() == [arg]
            )
            .then_some(t)
        }
        _ => None,
    }
}

/// Translate a structurally parsed `(_ bvN W)` into a `mk_bitvec` term. Returns
/// `None` for every other indexed identifier (fail-closed). The value is
/// reduced modulo `2^W` exactly as SMT-LIB defines it.
fn build_bv_decimal_indexed(
    terms: &mut TermStore,
    name: &str,
    indices: &[FrontendIndex],
) -> Option<TermId> {
    let value_str = name.strip_prefix("bv")?;
    let [FrontendIndex::Numeral(width_str)] = indices else {
        return None;
    };
    if value_str.is_empty()
        || !value_str.bytes().all(|b| b.is_ascii_digit())
        || width_str.is_empty()
        || !width_str.bytes().all(|b| b.is_ascii_digit())
    {
        return None;
    }
    let width: u32 = width_str.parse().ok()?;
    if width == 0 {
        return None;
    }
    let value = BigInt::parse_bytes(value_str.as_bytes(), 10)?;
    let value = value % (BigInt::from(1) << width);
    Some(terms.mk_bitvec(value, width))
}

/// Whether `root`'s term DAG contains any BitVec-sorted node (iterative walk).
fn term_contains_bitvec(terms: &TermStore, root: TermId) -> bool {
    let mut stack = vec![root];
    let mut seen = std::collections::HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if matches!(terms.sort(t), Sort::BitVec(_)) {
            return true;
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, x, y) => {
                stack.push(*c);
                stack.push(*x);
                stack.push(*y);
            }
            _ => {}
        }
    }
    false
}

/// Whether `root`'s term DAG contains any Array-sorted node (iterative walk).
///
/// The scope discriminator for [`Executor::rebuilt_terms_print_faithfully`]:
/// array content is exactly the fragment the faithful rebuilders newly admit,
/// and the one where `mk_select`/`mk_store`'s folds can misattribute a whole
/// read's authored spelling to a single leaf.
fn term_contains_array(terms: &TermStore, root: TermId) -> bool {
    let mut stack = vec![root];
    let mut seen = std::collections::HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if matches!(terms.sort(t), Sort::Array(_)) {
            return true;
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, x, y) => {
                stack.push(*c);
                stack.push(*x);
                stack.push(*y);
            }
            _ => {}
        }
    }
    false
}

/// Faithfully translate an integer-arithmetic frontend term into a `TermId` — the
/// elaborator's translation MINUS the simplifying folds (raw `mk_app`/`mk_int`).
/// Handles `Int`-sorted symbols (declared consts), integer numerals, and the
/// `+`/`-`/`*` operators, recursively. Returns `None` (fail-closed) for anything
/// else — a non-`Int` symbol, a non-integer literal, an unknown op — or, the
/// load-bearing soundness guard, an op application that `mk_app` FOLDED away (so
/// the rebuilt term is no longer the raw `(op args..)` and would silently change
/// the reconstructed assertion). Every accepted node is a structure-preserving
/// rebuild, so the result faithfully represents the surface assertion.
fn build_int_pterm(terms: &mut TermStore, pt: &FrontendTerm) -> Option<TermId> {
    match pt {
        FrontendTerm::Symbol(s) => {
            let id = terms.lookup(s)?;
            matches!(terms.sort(id), Sort::Int).then_some(id)
        }
        FrontendTerm::Const(FrontendConstant::Numeral(n)) => {
            let value = BigInt::parse_bytes(n.as_bytes(), 10)?;
            Some(terms.mk_int(value))
        }
        FrontendTerm::App(op, args)
            if matches!(op.as_str(), "+" | "-" | "*") && !args.is_empty() =>
        {
            let arg_ids: Vec<TermId> = args
                .iter()
                .map(|a| build_int_pterm(terms, a))
                .collect::<Option<_>>()?;
            let t = terms.mk_app(Symbol::named(op), arg_ids.clone(), Sort::Int);
            // Faithfulness guard: the rebuilt term must be the RAW application; if
            // `mk_app` folded it, it no longer mirrors the surface term.
            matches!(
                terms.get(t),
                TermData::App(sym, a) if sym.name() == op && a.as_slice() == arg_ids.as_slice()
            )
            .then_some(t)
        }
        _ => None,
    }
}

/// Faithfully translate a Boolean frontend term into a `TermId` — the
/// elaborator's translation MINUS folds (raw `mk_not_raw`/`mk_app`). Handles
/// `Bool`-sorted symbols, `true`/`false`, `not`, and the propositional
/// connectives `and`/`or`/`xor`/`=>`/`=` over Bool operands, recursively.
/// Returns `None` (fail-closed) for anything else or — the soundness guard — a
/// connective `mk_app` FOLDED (so the rebuilt term no longer mirrors the surface
/// term). `not` is built raw (`mk_not_raw` never folds), so double-negation is
/// preserved for the bounded evaluator.
fn build_bool_pterm(terms: &mut TermStore, pt: &FrontendTerm) -> Option<TermId> {
    match pt {
        FrontendTerm::Symbol(s) => {
            let id = terms.lookup(s)?;
            matches!(terms.sort(id), Sort::Bool).then_some(id)
        }
        FrontendTerm::Const(FrontendConstant::True) => Some(terms.true_term()),
        FrontendTerm::Const(FrontendConstant::False) => Some(terms.false_term()),
        FrontendTerm::App(op, args) if op == "not" && args.len() == 1 => {
            let a = build_bool_pterm(terms, &args[0])?;
            Some(terms.mk_not_raw(a))
        }
        FrontendTerm::App(op, args)
            if matches!(op.as_str(), "and" | "or" | "xor" | "=>" | "=") && args.len() == 2 =>
        {
            let arg_ids: Vec<TermId> = args
                .iter()
                .map(|a| build_bool_pterm(terms, a))
                .collect::<Option<_>>()?;
            let t = terms.mk_app(Symbol::named(op), arg_ids.clone(), Sort::Bool);
            matches!(
                terms.get(t),
                TermData::App(sym, a) if sym.name() == op && a.as_slice() == arg_ids.as_slice()
            )
            .then_some(t)
        }
        _ => None,
    }
}

#[cfg(all(test, feature = "proof-checker"))]
use check::*;
#[cfg(test)]
mod shadowed_store_ext_tests;
#[cfg(test)]
mod tests;
