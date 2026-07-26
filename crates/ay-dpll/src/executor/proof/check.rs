// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof checking, validation, and quality measurement.
//!
//! Contains the internal proof checker integration, proof quality metrics,
//! and proof predicate helpers (derives_empty_clause, etc.).
//!
//! Extracted from `proof.rs` for code health (#5970).

use ay_core::TermStore;
use ay_core::{AletheRule, Proof, ProofStep, TermId};
#[cfg(feature = "proof-checker")]
use ay_proof::{check_proof_partial, PartialProofCheck};
use ay_proof::{ProofCheckError, ProofQuality};

use super::super::Executor;

#[cfg(feature = "proof-checker")]
pub(super) const PROOF_CHECKER_FAILURES_KEY: &str = "proof_checker_failures";
#[cfg(feature = "proof-checker")]
pub(super) const PROOF_CHECKER_SKIPPED_HOLE_STEPS_KEY: &str = "proof_checker_skipped_hole_steps";
#[cfg(feature = "proof-checker")]
pub(super) const PROOF_CHECKER_CHECKED_STEPS_KEY: &str = "proof_checker_checked_steps";
#[cfg(feature = "proof-checker")]
pub(super) const PROOF_CHECKER_TOTAL_STEPS_KEY: &str = "proof_checker_total_steps";

/// Allocation-aware collector used by the runtime firewall diagnostic.
///
/// Each emitter still owns the one `String` it is currently constructing, but
/// the collector never retains enough completed artifacts to cross either
/// caller-supplied bound. This prevents repeated renderings of a large query
/// from accumulating into an unbounded `Vec<String>`.
struct BoundedFirewallArtifacts {
    artifacts: Vec<String>,
    total_bytes: usize,
    max_files: usize,
    max_bytes: usize,
    exceeded: bool,
}

impl BoundedFirewallArtifacts {
    fn new(max_files: usize, max_bytes: usize) -> Self {
        Self {
            artifacts: Vec::new(),
            total_bytes: 0,
            max_files,
            max_bytes,
            exceeded: false,
        }
    }

    fn push(&mut self, artifact: String) -> bool {
        let Some(next_bytes) = self.total_bytes.checked_add(artifact.len()) else {
            self.exceeded = true;
            return false;
        };
        if self.artifacts.len() >= self.max_files || next_bytes > self.max_bytes {
            self.exceeded = true;
            return false;
        }
        self.total_bytes = next_bytes;
        self.artifacts.push(artifact);
        true
    }

    fn remaining_bytes(&self) -> usize {
        self.max_bytes.saturating_sub(self.total_bytes)
    }

    fn finish(self) -> Option<Vec<String>> {
        (!self.exceeded).then_some(self.artifacts)
    }
}

impl Executor {
    /// Populate statistics extra map with proof quality metrics.
    pub(super) fn populate_proof_quality_stats(&mut self, quality: &ProofQuality) {
        use crate::executor_types::StatValue;
        let extra = &mut self.last_statistics.extra;
        extra.insert(
            "proof_steps".to_string(),
            StatValue::Int(u64::from(quality.total_steps)),
        );
        extra.insert(
            "proof_verified".to_string(),
            StatValue::Int(u64::from(quality.verified_count())),
        );
        extra.insert(
            "proof_trust".to_string(),
            StatValue::Int(u64::from(quality.trust_count)),
        );
        extra.insert(
            "proof_complete".to_string(),
            StatValue::String(if quality.is_complete() {
                "true".to_string()
            } else {
                "false".to_string()
            }),
        );
    }

    /// Datatype constructor registry for strict proof validation:
    /// `(datatype_name, [constructor_name, ..])` from the elaboration context.
    ///
    /// Runtime datatype terms carry `Sort::Uninterpreted`, so the proof checker
    /// cannot recover constructor membership from the `TermStore` alone — it is
    /// supplied here, where the `declare-datatype` declarations are known.
    pub(crate) fn datatype_decls_for_strict_proof(&self) -> Vec<(String, Vec<String>)> {
        self.ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect()
    }

    /// Emit diagnostic firewall artifacts without retaining more than the
    /// supplied number of files or aggregate raw-source bytes.
    ///
    /// Returns `None` if either limit would be crossed. The currently rendered
    /// `String` may momentarily exceed `max_bytes`, but it is dropped instead of
    /// joining the retained artifact vector.
    pub fn emit_datatype_firewall_lean_bounded(
        &self,
        proof: &Proof,
        max_files: usize,
        max_bytes: usize,
    ) -> Option<Vec<String>> {
        use ay_core::TheoryLemmaKind as K;
        let decls = self.datatype_decls_for_strict_proof();
        let mut out = BoundedFirewallArtifacts::new(max_files, max_bytes);
        for artifact in proof.steps.iter().filter_map(|step| {
            let ProofStep::TheoryLemma { kind, clause, .. } = step else {
                return None;
            };
            match kind {
                K::DatatypeDistinct if !decls.is_empty() => {
                    crate::executor::lean_firewall::emit_datatype_distinct_firewall_lean(
                        &self.ctx.terms,
                        &decls,
                        clause,
                    )
                }
                K::LraFarkas | K::LiaGeneric => {
                    // Farkas / bound conflicts go through the LIA emitter; a
                    // single-variable LINEAR IDENTITY (e.g. `(* x 0) = 0`,
                    // the `LinearIdentity` annotation) is a different shape —
                    // the LIA emitter declines it, so fall through to the
                    // identity emitter.
                    crate::executor::lean_firewall::emit_lia_firewall_lean(&self.ctx.terms, clause)
                        .or_else(|| {
                            crate::executor::lean_firewall::emit_nia_identity_firewall_lean(
                                &self.ctx.terms,
                                clause,
                            )
                        })
                }
                K::EufTransitive => {
                    crate::executor::lean_firewall::emit_euf_firewall_lean(&self.ctx.terms, clause)
                }
                K::EufCongruent => {
                    crate::executor::lean_firewall::emit_euf_congruence_firewall_lean(
                        &self.ctx.terms,
                        clause,
                    )
                }
                K::EufCongruentPred => {
                    crate::executor::lean_firewall::emit_euf_pred_congruence_firewall_lean(
                        &self.ctx.terms,
                        clause,
                    )
                }
                // Array read-over-write-NEG: the proof carries the
                // self-contained guarded theorem
                // `(i = j) ∨ (= (select (store a i v) j) (select a j))`.
                // The emitter independently recognizes that exact clause
                // and grounds the generic ROW2 theorem (a/i/j/v modeled as
                // opaque components). Guard-less contextual units are
                // declined.
                K::ArraySelectStore { index_eq: false } => {
                    crate::executor::lean_firewall::emit_array_row2_firewall_lean(
                        &self.ctx.terms,
                        clause,
                    )
                }
                // If-then-else identical branches `(= (ite c x x) x)`: holds
                // for any condition and any branch sort; ground via `ite_self`
                // over `Val = branch_sort × Bool`.
                K::IteSame => crate::executor::lean_firewall::emit_ite_same_firewall_lean(
                    &self.ctx.terms,
                    clause,
                ),
                // FP sign-bit identities (`fp.abs` idempotence / `fp.neg`
                // involution). Classification EXCLUSIVITY is a different shape
                // handled by the from-parsed FP emitter below — this declines
                // it (returns None), so the two are complementary.
                K::FpClassification { .. } => {
                    crate::executor::lean_firewall::emit_fp_identity_firewall_lean(
                        &self.ctx.terms,
                        clause,
                    )
                }
                // Small-width BV IDENTITY lemma `(= L R)` over BV variables
                // (e.g. `(= (bvand x x) x)`) — refuted by `decide` over the
                // `BitVec w` model (width from the variable's sort).
                K::BvBitBlast => crate::executor::lean_firewall::emit_bv_identity_firewall_lean(
                    &self.ctx.terms,
                    clause,
                ),
                // Datatype selector projection `(= (sel_i (C f0 f1)) f_i)`:
                // model the datatype as a product, the selector as `.1`/`.2`.
                K::DatatypeSelectorProject => {
                    crate::executor::lean_firewall::emit_dt_selector_projection_firewall_lean(
                        &self.ctx.terms,
                        clause,
                    )
                }
                // Remaining: array ROW-same (bare-trust reconstruction),
                // strings/BV/FP (surface-rewrite-trivialized / non-tautology
                // lemmas) — need lemma reconstruction first. See memory
                // `project_formally_verifying_ay`.
                _ => None,
            }
        }) {
            if !out.push(artifact) {
                return None;
            }
        }

        // String length-vs-literal conflicts: ay's lemma AND the TermId-level
        // assertions are surface-rewrite-trivialized before emit, so reconstruct
        // from the FRONTEND parsed assertions (where the `s = L` / `str.len s = K`
        // structure survives). Appended separately — not driven by a per-step
        // theory-lemma kind.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_string_length_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Sequence length-over-concat conflicts: `seq.len (seq.++ X Y) =
        // seq.len X + seq.len Y + K` (K>0) is unsatisfiable by the verified
        // `SeqThy.len_concat` axiom. ay reduces seq.len/seq.++ eagerly (bare
        // trust), so reconstruct from the frontend assertions and ground the
        // sequence length-additivity axiom over `Val = Seq Int × Seq Int`.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_seq_len_concat_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // String length-over-concat conflicts: `str.len (str.++ X Y) =
        // str.len X + str.len Y + K` (K>0) is unsatisfiable by the verified
        // `StringThy.len_cat` axiom. ay reduces str.len/str.++ eagerly (bare
        // trust), so reconstruct from the frontend assertions and ground the
        // string length-additivity axiom over `Val = StringThy.Str × StringThy.Str`.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_str_len_concat_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // String empty-length conflicts: `str.len s = 0 ∧ s ≠ ""` is
        // unsatisfiable by the verified `StringThy.len_zero_iff` axiom
        // (`len s = 0 ↔ s = ε`). ay reduces str.len eagerly (bare trust), so
        // reconstruct from the frontend assertions and ground the empty-string
        // characterization over `Val = StringThy.Str`.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_str_len_zero_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // `str.at` LENGTH conflicts: `str.len (str.at t i) = N` (N≥2) is
        // unsatisfiable by the verified `AySoundness.StrAt.strAt_len_eq_conflict`
        // (`str.len (str.at s i) ≤ 1`, index-universal). ay reduces str.at eagerly
        // (bare trust), so reconstruct from the frontend assertions and ground the
        // length bound over `Val = StringThy.Str × Nat`.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_str_at_len_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // GROUND `seq.at` value-mismatch conflicts: `seq.unit V = seq.at s i` with
        // an in-range read whose element differs from `V` is unsatisfiable
        // (`SeqThy.seqAt` / `SeqThy.unit`). Reconstruct from the frontend
        // assertions and close by `decide` over `Val = Unit`.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_seq_at_pinned_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // GROUND `seq.nth` + LIA conflicts: a numeric comparison over an in-range
        // total read `seq.nth s i` that is false once bound to `s[i]` (verified
        // `SeqThy.nthD` bridge → pure LIA). Reconstruct from the frontend
        // assertions and close by `decide` over `Val = Unit`.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_seq_nth_ground_lia_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // BOUNDED 2-way `seq.at`-vs-`ite` conflicts: `seq.at s i = ite c TB FB`
        // where both ground branches differ from the in-range read is unsatisfiable
        // regardless of the abstract condition `c` (`SeqThy.seqAt`; the OOB
        // seq.nth in `c` is a red herring, never evaluated). Reconstruct from the
        // frontend assertions and case-split on `Val = Bool`.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_seq_at_ite_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // `seq.suffixof` LAST-ELEMENT-mismatch conflicts: `seq.suffixof x
        // (seq.++ … t)` where the alleged suffix `x` ends in `a` but the whole
        // ends in `b = last t ≠ a` (the last `seq.++` operand `t` is ground and
        // non-empty) is unsatisfiable — a non-empty suffix shares the whole's last
        // element (verified `SeqThy.suffix_append_last_conflict`). Reconstruct from
        // the frontend assertions; the prefix is quantified universally.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_seq_suffixof_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // OOB `seq.extract` feeding an empty-needle `seq.replace` head conflict:
        // `(= (seq.replace HAYSTACK (seq.extract S I N) T) WHOLE)` where the
        // extract offset `I ≥ len S` makes the needle EMPTY (verified
        // `SeqThy.seqExtract_oob`, for every count `N`), so the replace PREPENDS
        // `T` (head pinned by `T` for every haystack — `SeqThy.seqReplaceEmpty_head`)
        // — unsatisfiable when the whole's head differs. ay reduces seq.extract /
        // seq.replace eagerly (bare trust); reconstruct from the frontend
        // assertions with the haystack and count quantified universally.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_seq_extract_oob_replace_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // `str.indexof`-ABSENT `≥ 0` conflicts: `(>= (str.indexof H N s) 0)` where
        // the needle `N` is genuinely absent from the ground literal haystack `H`,
        // so `str.indexof = -1` for EVERY start (verified, CLASSICAL-FREE
        // `IndexOfThy.indexOf_absent_all_start`) and `-1 ≥ 0` is false. ay reduces
        // str.indexof eagerly (bare trust); reconstruct from the frontend
        // assertions with the symbolic start quantified universally.
        match crate::executor::lean_firewall::emit_str_indexof_absent_ge_firewall_lean_from_parsed(
            self.ctx.assertions_parsed(),
            out.remaining_bytes(),
        ) {
            Ok(Some(lean)) => {
                if !out.push(lean) {
                    return None;
                }
            }
            Ok(None) => {}
            Err(()) => return None,
        }

        // `str.indexof`-ABSENT `str.is_digit ∘ str.from_int` conflicts:
        // `(str.is_digit (str.from_int (str.indexof T W k)))` where `W` is absent
        // from the (alias-resolved) ground literal haystack `T`, so `str.indexof =
        // -1`, `str.from_int (-1) = ""`, and `str.is_digit "" = false` (verified,
        // CLASSICAL-FREE `IndexOfThy.indexOf_absent_all_start`). Reconstruct from
        // the frontend assertions, resolving string aliases transitively.
        match crate::executor::lean_firewall::emit_str_indexof_is_digit_firewall_lean_from_parsed(
            self.ctx.assertions_parsed(),
            out.remaining_bytes(),
        ) {
            Ok(Some(lean)) => {
                if !out.push(lean) {
                    return None;
                }
            }
            Ok(None) => {}
            Err(()) => return None,
        }

        // Small-width bit-vector conflicts: ay bit-blasts BV eagerly (bare-trust
        // refutation), so reconstruct from the frontend assertions and refute the
        // conjunction directly by curried `decide` over a `BitVec w` model.
        if let Some(lean) = crate::executor::lean_firewall::emit_bv_firewall_lean_from_parsed(
            self.ctx.assertions_parsed(),
        ) {
            if !out.push(lean) {
                return None;
            }
        }

        // Propositional contradictions (e.g. `(not (= (not (not p)) p))`,
        // `(= p (not p))`): ay refutes the Boolean conflict eagerly (bare-trust);
        // reconstruct from the frontend assertions and refute by `decide` over a
        // `Bool` model.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_bool_tautology_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Array read-over-write-same: `select (store a i v) i ≠ v` is bare-trust
        // (ay refutes arrays eagerly); reconstruct from the frontend assertions
        // and ground the generic McCarthy ROW-same theorem.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_row1_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Nested / multi-store array read-over-write: `select` over a `store`-chain
        // (e.g. `select (store (store a i v1) i v2) j` vs `select (store a i v2) j`)
        // reduces, by the McCarthy axioms, to a value that contradicts the asserted
        // disequality. ay refutes arrays eagerly (bare-trust), so reconstruct from
        // the frontend assertions and ground the composed ROW conflict; declines
        // unless a single base array, backed guards, and matching normal forms make
        // the guarded clause valid.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_nested_store_row_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Store COMMUTATIVITY: two `store`-chains that permute the same writes
        // over a common base — `(not (= (store (store a i v) j w) (store (store a
        // j w) i v)))` directly, or `(not (= (select L k) (select R k)))` through
        // a shared read — are equal under the asserted pairwise index
        // disequalities, so asserting they differ is UNSAT. Reconstruct from the
        // frontend assertions and ground the guarded `row_eq ∨ (⋁ coincidences)`
        // clause (`sel_upd_same`/`sel_upd_other` + extensionality).
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_store_commute_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Array WRITE-BACK identity: `store a i (select a i) ≠ a` is refuted by
        // extensionality (storing the value already present is a no-op). ay
        // refutes arrays eagerly (bare-trust); reconstruct from the frontend
        // assertions and ground the `ArrayThy.ext_nonvacuous` mirror.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_write_back_identity_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Array store-equality ⇒ value-equality (ROW-1 on both sides):
        // `store a i v = store b i w` with `v ≠ w` is UNSAT. Reconstruct from the
        // frontend assertions and ground the `ArrayThy.sel_upd_same` mirror.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_store_eq_select_eq_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Array store-equality ⇒ base-equality at a DISTINCT index (ROW-2):
        // `store a i v = store b i w`, `i ≠ j`, `select a j ≠ select b j` is UNSAT.
        // Reconstruct from the frontend assertions and ground the
        // `ArrayThy.sel_upd_other` mirror.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_store_eq_base_other_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Conflicting stores (ROW-1 through a shared array variable): a variable
        // bound to two stores at the same index with distinct values —
        // `x = store b i e1`, `x = store b i e2`, `e1 ≠ e2` — is UNSAT.
        // Reconstruct from the frontend assertions and ground the
        // `ArrayThy.sel_upd_same` mirror.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_conflicting_stores_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Diamond conflict (store-equality ⇒ ROW-1 vs ROW-2 at one index):
        // `b = store a i v`, `c = store a j w`, `b = c`, `i ≠ j`,
        // `v ≠ select a i` is UNSAT. Reconstruct from the frontend assertions and
        // ground the `ArrayThy.sel_upd_same`/`sel_upd_other` mirror.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_diamond_conflict_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Array-equality ⇒ select-equality (select congruence): `a = b` with
        // `select a i ≠ select b i` is UNSAT. Reconstruct from the frontend
        // assertions and ground the functional-`sel` congruence (`congrFun`).
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_eq_select_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Array-equality ⇒ store-equality (store congruence): `a = b` with
        // `store a i v ≠ store b i v` is UNSAT. Reconstruct from the frontend
        // assertions and ground the functional-`upd` congruence (`congrArg`).
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_store_congruence_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Array equality-chain ⇒ ROW-1: a chain of asserted array equalities
        // carries the read array to a `store … i v` term, so `select a i ≠ v` is
        // UNSAT. Reconstruct from the frontend assertions and ground the
        // `Eq.trans` chain + `ArrayThy.sel_upd_same` mirror.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_eq_chain_row1_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Floating-point classification conflict: a float in two mutually-exclusive
        // IEEE classes (e.g. `(fp.isInfinite x) ∧ (fp.isNaN x)`) is UNSAT. ay reduces
        // FP to bit-vectors and refutes eagerly (bare-trust), so reconstruct from the
        // frontend assertions and ground the verified `FpThy` exclusivity partition.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_fp_classification_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Floating-point `to_fp` NARROWING underflow / RTN-overflow-asymmetry
        // conflict: a single `(fp.isInfinite/isNormal ((_ to_fp EB SB) RTN
        // (fp #b… #b… #b…)))` over a CONCRETE ground source whose RTN-narrowed
        // class the model classifies otherwise (underflow → subnormal/zero, so NOT
        // infinite / NOT normal). ay reduces to_fp to bit-vectors and refutes
        // eagerly (bare-trust); reconstruct from the frontend assertions and ground
        // the exact-dyadic, reference-battery-validated `FpUnderflow` classifier.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_fp_tofp_underflow_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Floating-point `fp.rem` SIGN conflict: a single
        // `(fp.isNegative (fp.rem (fp #b… #b… #b…) (fp #b… #b… #b…)))` over TWO
        // CONCRETE same-format ground operands whose exact round-to-nearest-even
        // remainder the model classifies as NOT negative. ay reduces fp.rem to
        // bit-vectors and refutes eagerly (bare-trust); reconstruct from the
        // frontend assertions and ground the exact-dyadic, reference-battery-
        // validated `FpUnderflow` remainder/sign classifier.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_fp_rem_not_negative_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Floating-point RNE DOT-PRODUCT forward-error proof emission is
        // deliberately disabled. The Lean `FpErrorBound` declarations prove
        // fixed-grid `qround` models, but no theorem connects the parsed
        // IEEE-754 operations and intermediate magnitude bounds to those
        // models. The hook below therefore declines every threshold, including
        // guard2's 2.0, until that semantic bridge exists and is reviewed.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_fp_dot_error_bound_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
                &self.ctx.nullary_defined_terms(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Set subset ground-witness refutation: ay decides set.subset via member
        // saturation (no proof-step theory lemma), so reconstruct from the
        // frontend assertions `(set.member x s) (not (set.member x t))
        // (set.subset s t)` and ground the subset-definition-at-witness lemma.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_set_subset_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Set subset transitivity `(set.subset A B) (set.subset B C)
        // (not (set.subset A C))`: the certificate grounds ⊆-transitivity
        // directly (no Skolemization — unlike the Alethe proof).
        if let Some(lean) =
            crate::executor::lean_firewall::emit_set_subset_transitivity_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Datatype selector congruence: ay's QF_DT pipeline refutes eagerly and
        // folds the term structure away (bare `(cl …) :rule trust`), so
        // reconstruct from the frontend assertions `(= (sel A) v) (= A B)
        // (not (= (sel B) v))` and ground the selector-congruence lemma.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_dt_selector_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Datatype constructor injectivity: `(= (C a …) (C c …)) (not (= a c))`
        // over a genuine constructor `C`. Sound only for real constructors
        // (injectivity is their datatype-theory axiom), so pass the constructor
        // names from the datatype registry.
        if !decls.is_empty() {
            let ctor_names: Vec<String> = decls
                .iter()
                .flat_map(|(_, ctors)| ctors.iter().cloned())
                .collect();
            if let Some(lean) =
                crate::executor::lean_firewall::emit_dt_injective_firewall_lean_from_parsed(
                    self.ctx.assertions_parsed(),
                    &ctor_names,
                )
            {
                if !out.push(lean) {
                    return None;
                }
            }

            // Datatype ACYCLICITY / occurs-check: `t = C(… t …)` where the
            // variable `t` occurs as a proper subterm under ≥1 constructor layer.
            // Beyond the pure-constructor path, sound UNCONDITIONAL rewrites also
            // reduce (B) selector-mediated occurrences `x = C(… (sel x) …)` and
            // (C) tautological-tester `ite` + selector-self-eq under an asserted
            // tester to the same occurs-check. Unsatisfiable by the auto-derived
            // `sizeOf` strictly increasing across constructors; reconstruct from
            // the frontend assertions and ground the generic acyclicity conflict
            // (`AySoundness.Datatype.acyclic_conflict_generic`). Sound only for
            // real constructors, so pass the constructor names, the datatype
            // registry (single-ctor tester tautology), and the constructor→
            // selector map (projection / tester-form reconstruction).
            let ctor_selectors = self.ctor_selector_decls_for_strict_proof();
            if let Some(lean) =
                crate::executor::lean_firewall::emit_dt_occurs_check_firewall_lean_from_parsed(
                    self.ctx.assertions_parsed(),
                    &ctor_names,
                    &decls,
                    &ctor_selectors,
                )
            {
                if !out.push(lean) {
                    return None;
                }
            }

            // Datatype CASE-SPLIT: a residual `C(… t …) = ite g B_true B_false`
            // (boolean-ite-guard) or `((_ is nd) x) ∧ (not (distinct nd(y,x) lf x))`
            // (finite distinct-disjunction). The split is carried as a bounded
            // `by_cases` inside the theory-lemma validity obligation, each branch
            // discharged by a verified Datatype lemma (acyclicity / distinctness /
            // tester mutual-exclusion). Reconstructed from the frontend assertions;
            // fail-closed on any shape not soundly reducible to a bounded split.
            if let Some(lean) =
                crate::executor::lean_firewall::emit_dt_case_split_firewall_lean_from_parsed(
                    self.ctx.assertions_parsed(),
                    &ctor_names,
                    &decls,
                )
            {
                if !out.push(lean) {
                    return None;
                }
            }

            // Datatype TESTER MUTUAL-EXCLUSION: two DISTINCT constructor testers
            // `((_ is Cᵢ) T)` and `((_ is Cⱼ) T)` asserted POSITIVELY on the SAME
            // syntactic term `T` (`T` a single opaque datatype-sorted term — a
            // variable or a UF app like `(f x)`; no congruence involved). No value
            // is headed by two constructors; grounded in the generalization of
            // `AySoundness.Datatype.tester_node_leaf_excl`. Constructors from the
            // datatype registry pin `T`'s sort, so the abstraction is faithful.
            if let Some(lean) =
                crate::executor::lean_firewall::emit_dt_tester_exclusion_firewall_lean_from_parsed(
                    self.ctx.assertions_parsed(),
                    &decls,
                )
            {
                if !out.push(lean) {
                    return None;
                }
            }

            // Datatype EXHAUSTIVENESS (2-constructor case-completeness): a NEGATIVE
            // tester `(not ((_ is C) T))` together with a disequality
            // `(not (= D T))`, where `C` and `D` are the ONLY two constructors of
            // `T`'s datatype (`D` nullary). A value neither `C`-headed nor `D`
            // cannot exist — the exhaustiveness dual of the enum-cardinality
            // pigeonhole. Relevant conjuncts are extracted from a flattened
            // top-level `(and …)`; fail-closed on any other shape.
            if let Some(lean) =
                crate::executor::lean_firewall::emit_dt_exhaustiveness_firewall_lean_from_parsed(
                    self.ctx.assertions_parsed(),
                    &decls,
                )
            {
                if !out.push(lean) {
                    return None;
                }
            }

            // Datatype SELECTOR-OVER-OWN-CONSTRUCTOR: `(= X (C … aᵢ …))` together
            // with `(not (= (sᵢ X) aᵢ))`, where `sᵢ` is `C`'s field-i selector.
            // The selector-over-matching-constructor axiom gives `sᵢ X = aᵢ`,
            // contradicting the disequality. ay routes the residual through a
            // BV/constant compare (so the proof-step `DtSel` projection emitter
            // does not fire); reconstruct from the frontend assertions. Sound only
            // for real constructor→selector maps, so pass `ctor_selectors`.
            if let Some(lean) =
                crate::executor::lean_firewall::emit_dt_selector_over_ctor_firewall_lean_from_parsed(
                    self.ctx.assertions_parsed(),
                    &decls,
                    &ctor_selectors,
                )
            {
                if !out.push(lean) {
                    return None;
                }
            }

            // Datatype TESTER-GUARDED CASE-SPLIT (both branches acyclicity): a
            // residual `t = C(… ite g A B …)` (`g` a constructor tester, `t` a
            // bare variable) whose BOTH branch-substitutions occur-check `t`.
            // Recovered after substituting a forced Boolean unit from a sibling
            // unit-assertion and sound constant-folding; the split is carried as
            // a `by_cases` on the opaque guard, each branch discharged by
            // `acyclic_conflict_generic` at its occurrence depth. Fail-closed on
            // any shape not both-branches-occurs.
            if let Some(lean) =
                crate::executor::lean_firewall::emit_dt_tester_casesplit_occurs_firewall_lean_from_parsed(
                    self.ctx.assertions_parsed(),
                    &ctor_names,
                )
            {
                if !out.push(lean) {
                    return None;
                }
            }

            // Datatype TESTER-GUARDED CASE-SPLIT with a MIXED conflict (a DIFFERENT
            // verified lemma per branch): a residual `(ite g A B) = R` whose
            // else-branch (`g = false`) is an ACYCLICITY occurs-check and whose
            // then-branch (`g = true`) is a constructor DISTINCTNESS conflict. The
            // datatype is faithfully abstracted onto the concrete binary `Tree`
            // (2 recursive fields ↦ `node`, 0 ↦ `leaf`), so the per-constructor
            // recursive-field mask is computed from the datatype registry.
            // Fail-closed on any shape not soundly rendered as occurs+distinct.
            let ctor_rec: Vec<(String, Vec<bool>)> = ctor_names
                .iter()
                .filter_map(|c| {
                    let info = self.ctx.constructor_selector_info(c)?;
                    let (dt_name, _) = self.ctx.is_constructor(c)?;
                    let flags = info
                        .iter()
                        .map(|(_, sort)| {
                            matches!(sort, ay_core::Sort::Datatype(ds) if ds.name == dt_name)
                        })
                        .collect();
                    Some((c.clone(), flags))
                })
                .collect();
            if let Some(lean) =
                crate::executor::lean_firewall::emit_dt_tester_casesplit_mixed_firewall_lean_from_parsed(
                    self.ctx.assertions_parsed(),
                    &ctor_names,
                    &ctor_rec,
                )
            {
                if !out.push(lean) {
                    return None;
                }
            }

            // Datatype NESTED SELECTOR-GUARDED CASE-SPLIT (bench
            // `soundness_qf_dt_derived_terms/fuzz_ufdt_falsesat_881.smt2`): two
            // residual assertions over a binary-recursive constructor `nd` —
            // `T = nd(selR(ite G T (nd Y _ T)) _ selL(nd Y _ Y))` and
            // `(or (and ¬V18 ¬G) (distinct (selR T) (nd (lf …) _ Y) (ite V18 T Y) T))`
            // — jointly unsatisfiable via a NESTED `by_cases`: `G = false` gives an
            // ACYCLICITY occurs-check; `G = true` forces `T = nd(Y,Y)` (selector
            // fixpoint) so the first disjunct is false and an inner split on `V18`
            // makes the `distinct` contain a duplicate (false by reflexivity). The
            // selectors are modelled as total projections whose leaf-case is dead
            // (assert1 forces every selected term to be a `node`). Fail-closed on
            // any shape not exactly this nested selector-guarded template.
            if let Some(lean) =
                crate::executor::lean_firewall::emit_dt_nested_selector_casesplit_firewall_lean_from_parsed(
                    self.ctx.assertions_parsed(),
                    &ctor_rec,
                    &ctor_selectors,
                )
            {
                if !out.push(lean) {
                    return None;
                }
            }

            // Datatype ENUM-CARDINALITY (pigeonhole): a `(distinct T₀ … T_{n-1})`
            // whose `n` arguments all inhabit one FINITE ENUM datatype (every
            // constructor nullary) with only `k < n` constructors. `n` values of
            // a `k`-element type cannot be pairwise distinct. The derived Enum
            // terms are abstracted to `n` opaque enum variables; the pigeonhole is
            // discharged by exhaustive finite `cases`. The common argument sort is
            // resolved from the declared symbol→sort table; the finite-enum
            // datatypes (with their constructor counts) are computed from the
            // registry. Fail-closed unless every argument resolves to the same
            // finite enum with `k < n`.
            let sym_sorts: Vec<(String, String)> = self
                .ctx
                .symbols_iter()
                .filter_map(|(name, info)| match &info.sort {
                    ay_core::Sort::Datatype(ds) => Some((name.clone(), ds.name.clone())),
                    ay_core::Sort::Uninterpreted(s) => Some((name.clone(), s.clone())),
                    _ => None,
                })
                .collect();
            let enum_datatypes: Vec<(String, usize)> = decls
                .iter()
                .filter_map(|(name, ctors)| {
                    let all_nullary = !ctors.is_empty()
                        && ctors.iter().all(|c| {
                            self.ctx
                                .symbol_info(c)
                                .is_some_and(|i| i.arg_sorts.is_empty())
                        });
                    all_nullary.then(|| (name.clone(), ctors.len()))
                })
                .collect();
            if let Some(lean) =
                crate::executor::lean_firewall::emit_dt_enum_cardinality_firewall_lean_from_parsed(
                    self.ctx.assertions_parsed(),
                    &enum_datatypes,
                    &sym_sorts,
                )
            {
                if !out.push(lean) {
                    return None;
                }
            }

            // Datatype F3 (`f³ = f` on a 2-element enum): a two-constructor ENUM
            // datatype, an uninterpreted `fEnum : Enum → Enum`, and the two
            // assertions `(= (fEnum v1) v2)` and
            // `(distinct (fEnum v1) (fEnum (fEnum v2)))`. On a two-element type
            // every self-map satisfies `f x = f (f (f x))`, so `f v1 = v2` forces
            // `f v1 = f (f v2)`, contradicting the disequality. The uninterpreted
            // `fEnum` is faithfully modeled by an ARBITRARY `f : En → En` (the F3
            // theorem holds for all `f`); grounded in the verified
            // `AySoundness.Datatype.F3.f3_conflict`. Reuses the finite-enum
            // registry (`enum_datatypes`, k == 2 required) and symbol→sort table
            // to pin `fEnum`'s type; fail-closed on any other shape.
            if let Some(lean) = crate::executor::lean_firewall::emit_dt_f3_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
                &enum_datatypes,
                &sym_sorts,
            ) {
                if !out.push(lean) {
                    return None;
                }
            }
        }

        // EUF congruence over a transitive chain: `(= x m) (= m y)
        // (not (= (f x) (f y)))`. The executor's trust-split produces
        // eq_transitive/eq_congruent STEPS (not theory-lemma kinds), so the
        // proof-step dispatch above emits nothing for it; reconstruct from the
        // frontend assertions and ground the fused congruence-over-transitivity
        // lemma.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_euf_cong_trans_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // NIA conflict that becomes a single linear equality after substituting
        // constant-pinned variables (e.g. `(* x y)=7 ∧ x=2` ⟶ `2*y=7`): ay
        // treats it as nonlinear bare-trust; reconstruct from the frontend and
        // ground the linear conflict by `omega`.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_nia_linear_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            if !out.push(lean) {
                return None;
            }
        }

        // Word-equation length conflicts: a string equation `A = B` over
        // `str.++`/literals/variables (with optional `str.len v = c` pins) whose
        // LENGTH projection is ℕ-infeasible (e.g. `x·x = "aba"` ⟹ `2·len x = 3`).
        if let Some(lean) =
            crate::executor::lean_firewall::emit_str_word_eq_len_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Structural ground-set subset conflict, VALID subset asserted NEGATED:
        // `(not (set.subset S T))` over concrete finite sets with eval(S) ⊆ eval(T).
        if let Some(lean) =
            crate::executor::lean_firewall::emit_set_subset_structural_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Structural ground-set equality conflict: `(= S T)` over concrete finite
        // sets with eval(S) != eval(T).
        if let Some(lean) =
            crate::executor::lean_firewall::emit_set_eq_structural_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Structural ground-set subset conflict, FALSE subset asserted POSITIVELY:
        // `(set.subset S T)` with eval(S) not-⊆ eval(T).
        if let Some(lean) =
            crate::executor::lean_firewall::emit_set_subset_structural_false_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Array read-over-write-SAME positive MISMATCH: `select (store a i v) ridx
        // = w` with `ridx ≡ i` (arith-normalized) and `v ≠ w` distinct literals.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_row_mismatch_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Nested read-over-write hidden behind an ARRAY-LET `(= b (store …))`
        // (e.g. an element swap): inline the array definition and ground the
        // composed ROW conflict.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_inlined_nested_store_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Array read-over-write hidden behind nullary `define-fun` MACROS (QF_AX
        // store-commute: `(define-fun fwd () _ (store … ))`,
        // `(not (= (select fwd i0) (select rev i0)))` with `(distinct i0 …)`).
        // `assertions_parsed()` keeps macros unexpanded, so substitute their
        // (definitionally-equal) bodies and ground the composed ROW conflict.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_defexpanded_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
                &self.ctx.nullary_defined_terms(),
            )
        {
            out.push(lean);
        }

        // Array WRITE-BACK IDENTITY CHAIN behind `define-fun` macros
        // (`storeinv_sf_chain`): `store (store a i (select a i)) j (select a j) ≠ a`
        // is unsat because each level writes the base's own value back. Expand the
        // macros and ground the pointwise `ext` identity (the LIA firewall below is
        // gated off these array macros so it no longer mis-emits an omega-unclosable
        // artifact for this shape).
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_writeback_chain_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
                &self.ctx.nullary_defined_terms(),
            )
        {
            out.push(lean);
        }

        // Single-index array STORE-INVERSE cross-swap (`storeinv_cross_1idx`):
        // `store a2 i (select a1 i) = store a1 i (select a2 i)` with `a1 ≠ a2`
        // forces `a1 = a2` pointwise (array extensionality), a contradiction.
        // Inline the array-lets and ground the disjunctive `ext` theory lemma.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_storeinv_swap_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
                &self.ctx.nullary_defined_terms(),
            )
        {
            out.push(lean);
        }

        // Fused array-ROW + LINEAR-INTEGER conflict (bucket "array_sum_bound"):
        // `arr = store(base, i, v)` pins `select arr i = v` (RoW-1), and the pinned
        // reads make an integer (in)equality infeasible (closed by `omega`).
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_sum_bound_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
                &self.ctx,
            )
        {
            out.push(lean);
        }

        // Linear-integer conflicts: ay refutes a jointly integer-UNSAT conjunction
        // of linear (in)equalities with a bare `:rule trust` integer step (no
        // `la_generic` lemma clause to ground), so reconstruct from the frontend
        // assertions and discharge the all-negated blocking clause by `omega`.
        // `nullary_defined_terms` gates this OFF array-typed macros (a
        // `store`-bodied `define-fun` disequality is an array, not integer, atom).
        if let Some(lean) = crate::executor::lean_firewall::emit_lia_firewall_lean_from_parsed(
            self.ctx.assertions_parsed(),
            &self.ctx.nullary_defined_terms(),
            &self.ctx,
        ) {
            out.push(lean);
        }

        // NONLINEAR-INTEGER conflicts carried by ONE bilinear product (bucket
        // "nia_product"): the LIA emitter above DECLINES on any `var*var` term
        // because `omega` atomises the product and then cannot close the goal.
        // This one injects the verified `AySoundness.NiaProduct` McCormick corner
        // lemmas, which relate the atomised product to its two factors LINEARLY,
        // and only fires after proving the reconstructed system integer-infeasible
        // over exactly the atom set `omega` will see. Takes the same
        // `nullary_defined_terms` array-macro gate as the LIA emitter: an array
        // disequality is not an Int atom and must not be modelled as one.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_nia_product_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
                &self.ctx.nullary_defined_terms(),
                &self.ctx,
            )
        {
            out.push(lean);
        }

        // EUF + LINEAR-INTEGER fused congruence-value conflict (bucket
        // "euf_uflia"): LIA atoms pin Int vars to a common value and
        // single-application UF value atoms `(= (f x) c1)`, `(= (f y) c2)` (or
        // one negated) contradict via the congruence conclusion `f x = f y`. MUST
        // be inserted BEFORE the emit_general_firewall_lean call.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_euf_lia_congruence_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
                &self.ctx,
            )
        {
            out.push(lean);
        }

        // EUF CONGRUENCE bridge closing an LIA (in)equality/disequality system
        // (bucket "euf_cong_bridge"): a congruence-derived `f s = f t` (from an
        // LIA-implied `s = t`) makes `f a < 0 ∧ f b ≥ 0` (with `a = b`) or
        // `f x ≠ f y` (with `x + 1 = y + 1`) linearly UNSAT — the `omega` cascade
        // then closes it. The GENERAL firewall below reconstructs `f a`, `f b` as
        // INDEPENDENT integers and mis-emits an `omega`-unclosable artifact for
        // this shape, so when this dedicated emitter fires we SUPPRESS the general
        // one (its output would be a redundant fail-lake duplicate). MUST be
        // inserted BEFORE the emit_general_firewall_lean call.
        let euf_cong_bridge =
            crate::executor::lean_firewall::emit_euf_congruence_bridge_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
                &self.ctx,
            );
        let euf_cong_bridge_fired = euf_cong_bridge.is_some();
        if let Some(lean) = euf_cong_bridge {
            out.push(lean);
        }

        // GENERAL whole-DAG firewall: ground the ENTIRE refutation (all `Assume`
        // inputs + all arithmetic/equality `TheoryLemma`s + the resolution DAG)
        // as a SINGLE certificate over one shared `Nat → Int` model — the
        // Nelson–Oppen composition shape generalised from `CombinedExample`.
        // Complementary to the per-lemma emitters above (which ground each lemma
        // in isolation); only fires for fully-renderable arithmetic/equality
        // proofs, declining otherwise. Skipped when the EUF-congruence-bridge
        // emitter already covered this conflict (avoids an omega-unclosable
        // duplicate for the `f a`/`f b`-in-bounds shape).
        if !euf_cong_bridge_fired {
            if let Some(lean) =
                crate::executor::lean_firewall::emit_general_firewall_lean(&self.ctx.terms, proof)
            {
                if !out.push(lean) {
                    return None;
                }
            }
        }
        out.finish()
    }

    /// Strict proof check that also validates datatype constructor-distinctness
    /// lemmas (#8419 / trust_count→0).
    ///
    /// `DatatypeDistinct` steps (promoted from `Generic` at proof finalization
    /// by `promote_datatype_distinct_lemmas`) cannot be validated from the
    /// `TermStore` alone — runtime datatype terms carry `Sort::Uninterpreted`.
    /// This supplies the `declare-datatype` registry so the strict checker can
    /// semantically validate them against the actual constructor declarations
    /// instead of failing closed.
    ///
    /// It also supplies the complete authored premise scope. Strict mode uses
    /// that scope both to reject foreign `Assume` steps and to validate
    /// `ArrayExtensionality`: that clause is sound only for a witness the solver
    /// minted fresh, and "fresh" is a statement ABOUT the problem, so the
    /// checker verifies it against the problem's own symbols rather than
    /// trusting a name or a solver flag.
    pub(crate) fn check_proof_strict_with_datatypes(
        &self,
        proof: &Proof,
    ) -> Result<ProofQuality, ProofCheckError> {
        let decls = self.datatype_decls_for_strict_proof();
        let selectors = self.ctor_selector_decls_for_strict_proof();
        let problem = self.problem_assertions_for_strict_proof();
        ay_proof::check_proof_strict_with_context(
            proof,
            &self.ctx.terms,
            (!decls.is_empty()).then_some(decls.as_slice()),
            (!selectors.is_empty()).then_some(selectors.as_slice()),
            Some(problem.as_slice()),
        )
    }

    /// Strictly validate a proof's derivation while deliberately postponing
    /// authored-premise authorization.
    ///
    /// Proof-surgery passes use this as an atomic revert gate while they replace
    /// one derived lemma inside a larger proof. At that point the proof can still
    /// contain preprocessing assumptions which a later rewrite will derive from
    /// authored roots or demote to an explicit trust step. Treating those
    /// unrelated leaves as an authorization failure here would revert a valid
    /// local replacement and preserve its trust lemma.
    ///
    /// Every current `Assume` is supplied as an allowed premise solely for this
    /// structural check. This does not weaken the final boundary:
    /// [`Self::check_proof_strict_with_datatypes`] and the exported bundle still
    /// validate the finished proof against the independently captured authored
    /// scope. Including all assumes is also conservative for array witness
    /// freshness: it can only reject a witness that occurs in a premise.
    pub(crate) fn check_proof_strict_derivation_with_datatypes(
        &self,
        proof: &Proof,
    ) -> Result<ProofQuality, ProofCheckError> {
        let decls = self.datatype_decls_for_strict_proof();
        let selectors = self.ctor_selector_decls_for_strict_proof();
        let assumptions: Vec<TermId> = proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Assume(term) => Some(*term),
                _ => None,
            })
            .collect();
        ay_proof::check_proof_strict_with_context(
            proof,
            &self.ctx.terms,
            (!decls.is_empty()).then_some(decls.as_slice()),
            (!selectors.is_empty()).then_some(selectors.as_slice()),
            Some(assumptions.as_slice()),
        )
    }

    /// The complete authored premise scope for strict proof checking.
    ///
    /// Deliberately NOT `ctx.assertions`: at proof time that stack also carries
    /// the solver's own injected extensionality axioms, which mention every
    /// witness and would make all of them look non-fresh. The authored window
    /// (captured before in-place preprocessing) is preferred when present; the
    /// parsed-prefix and provenance-tracked problem assertions are unioned in.
    /// `check-sat-assuming` literals and structurally authenticated source terms
    /// rebuilt during proof repair are included because they can legitimately
    /// appear as `Assume` leaves. Solver-generated constraints are excluded.
    /// A SUPERSET is always safe here — extra terms can only make the freshness
    /// test stricter, never more permissive.
    pub(crate) fn problem_assertions_for_strict_proof(&self) -> Vec<TermId> {
        let mut problem = self.proof_export_scope_assertions();
        if let Some(authored) = self.self_check_authored_assertions.as_ref() {
            for &assertion in authored {
                if !problem.contains(&assertion) {
                    problem.push(assertion);
                }
            }
        }
        problem
    }

    /// Constructor→selector registry for strict proof validation:
    /// `(constructor_name, [selector_name in field order])` from the elaboration
    /// context. Like the distinctness registry, the field positions cannot be
    /// recovered from the `TermStore` (datatype terms carry `Sort::Uninterpreted`),
    /// so they are supplied here for `DatatypeSelectorProject` validation.
    pub(crate) fn ctor_selector_decls_for_strict_proof(&self) -> Vec<(String, Vec<String>)> {
        self.ctx
            .ctor_selectors_iter()
            .map(|(ctor, selectors)| (ctor.clone(), selectors.clone()))
            .collect()
    }

    /// Validate proof and collect quality metrics.
    ///
    /// In debug builds, runs the full proof checker (rejects invalid proofs via
    /// warning). In all builds, collects [`ProofQuality`] step-type counts for
    /// diagnostic reporting via `(get-info :all-statistics)`.
    pub(super) fn validate_and_measure_proof(&self, proof: &Proof) -> Option<ProofQuality> {
        let has_hole = proof.steps.iter().any(|s| {
            matches!(
                s,
                ProofStep::Step {
                    rule: AletheRule::Hole,
                    ..
                }
            )
        });
        if has_hole {
            return None;
        }

        // Use strict checker when enabled (#4420).
        let result = if self.strict_proofs_enabled() {
            self.check_proof_strict_with_datatypes(proof)
        } else {
            ay_proof::check_proof_with_quality(proof, &self.ctx.terms)
        };

        match result {
            Ok(quality) => {
                tracing::debug!(
                    %quality,
                    complete = quality.is_complete(),
                    "UNSAT proof quality"
                );
                if !quality.is_complete() {
                    tracing::warn!(
                        trust = quality.trust_count,
                        hole = quality.hole_count,
                        total = quality.total_steps,
                        "UNSAT proof has unverified fallback steps"
                    );
                }
                Some(quality)
            }
            Err(e) => {
                tracing::warn!(
                    error = %e,
                    steps = proof.len(),
                    "internal proof checker rejected UNSAT proof"
                );
                None
            }
        }
    }

    pub(crate) fn proof_derives_empty_clause(proof: &Proof) -> bool {
        proof.steps.iter().any(|step| match step {
            // An `array_ext_diff_intro` is a clause-free DEFINITION; its empty
            // `clause` field is not a derivation of `(cl)`.
            ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                ..
            } => false,
            ProofStep::Step { clause, .. } | ProofStep::Resolution { clause, .. } => {
                clause.is_empty()
            }
            _ => false,
        })
    }

    /// Check that the proof derives empty clause AND the resolution chain is
    /// valid (each ThResolution step's conclusion matches its premises).
    pub(super) fn proof_derives_valid_empty_clause(terms: &TermStore, proof: &Proof) -> bool {
        if !Self::proof_derives_empty_clause(proof) {
            return false;
        }
        // Quick check: run the partial checker. If it finds no errors, the
        // chain is valid.
        #[cfg(feature = "proof-checker")]
        {
            let (_, error) = check_proof_partial(proof, terms);
            error.is_none()
        }
        #[cfg(not(feature = "proof-checker"))]
        {
            let _ = terms;
            true
        }
    }

    #[cfg(feature = "proof-checker")]
    pub(super) fn run_internal_proof_check(&mut self, proof: &Proof) {
        // Strict mode (#4420): when enabled, reject trust and hole steps.
        // This gates on the SMT-LIB option `(set-option :check-proofs-strict true)`.
        if self.strict_proofs_enabled() {
            match self.check_proof_strict_with_datatypes(proof) {
                Ok(_quality) => {
                    let shape = Self::proof_shape_summary(proof);
                    self.proof_check_result = Some(PartialProofCheck {
                        checked_steps: shape.total_steps,
                        skipped_hole_steps: 0,
                        total_steps: shape.total_steps,
                    });
                    self.record_proof_check_stats(0, Self::proof_shape_summary(proof));
                }
                Err(error) => {
                    let shape = Self::proof_shape_summary(proof);
                    let checked = shape.checked_steps;
                    let skipped = shape.skipped_hole_steps;
                    let total = shape.total_steps;
                    self.proof_check_result = Some(shape.clone());
                    self.record_proof_check_stats(1, shape);
                    tracing::error!(
                        error = %error,
                        checked_steps = checked,
                        skipped_hole_steps = skipped,
                        total_steps = total,
                        "strict proof checker rejected UNSAT proof"
                    );
                }
            }
            return;
        }

        let (summary, error) = check_proof_partial(proof, &self.ctx.terms);
        self.proof_check_result = Some(summary.clone());
        if let Some(error) = error {
            let shape = Self::proof_shape_summary(proof);
            let checked = shape.checked_steps;
            let skipped = shape.skipped_hole_steps;
            let total = shape.total_steps;
            self.record_proof_check_stats(1, shape);

            tracing::error!(
                error = %error,
                checked_steps = checked,
                skipped_hole_steps = skipped,
                total_steps = total,
                "internal proof checker rejected UNSAT proof"
            );
        } else {
            self.record_proof_check_stats(0, summary);
        }
    }

    /// Whether the last UNSAT was backed by a refutation proof that AY's own
    /// internal checker fully verified: the checker reported no errors
    /// (`proof_check_ok`), the proof has at least one step, and no step is a
    /// trust/`Hole` placeholder (`skipped_hole_steps == 0`). This is the
    /// certification `--self-check` requires before emitting `unsat`.
    ///
    /// When the `proof-checker` feature is compiled out there is no internal
    /// checker to certify with, so this conservatively returns `false` (every
    /// UNSAT degrades to `unknown` under self-check).
    pub(in crate::executor) fn unsat_proof_self_certified(&self) -> bool {
        #[cfg(feature = "proof-checker")]
        {
            let Some(proof) = self.last_proof.as_ref() else {
                return false;
            };
            // Every step must be a real, checked derivation: no `Hole`
            // placeholders and no `Trust` steps (a Trust step means "believe the
            // solver, no derivation" — exactly what self-certification must
            // reject; e.g. the LIA `not-exists` residue wrong-UNSAT emits a
            // single Trust step). Assume steps are fine (problem hypotheses).
            //
            // A `TheoryLemma` whose `kind.is_trust()` (i.e. `Generic`) is ALSO
            // an untrusted step: the Alethe printer renders it as `:rule trust`
            // (alethe_printer.rs), so it is a certificate-free "believe the
            // solver" claim exactly like `Step{Trust}`. The original check
            // missed it, so `--self-check` emitted a bare `unsat` alongside a
            // carcara-INVALID `:rule trust` proof — a direct violation of the
            // "only emit what AY can verify itself" contract (#selfcert-leak).
            let has_untrusted_step = proof.steps.iter().any(|s| {
                matches!(
                    s,
                    ProofStep::Step {
                        rule: AletheRule::Hole,
                        ..
                    } | ProofStep::Step {
                        rule: AletheRule::Trust,
                        ..
                    }
                ) || matches!(
                    s,
                    ProofStep::TheoryLemma { kind, .. } if kind.is_trust()
                )
            });
            if has_untrusted_step {
                return false;
            }
            // Fail-closed re-validation of the ground string/regex lane. The
            // self-check gate consults the PARTIAL (non-strict) checker, so a
            // `StringGroundEval` lemma would otherwise be admitted on the
            // strength of the classifier alone. Re-run the checker's own
            // independent evaluator here: a lemma whose clause has no literal
            // the evaluator proves TRUE is not a tautology, and the UNSAT must
            // degrade to `unknown` rather than ship on a mislabelled step.
            let unvalidated_string_lemma = proof.steps.iter().any(|s| {
                matches!(
                    s,
                    ProofStep::TheoryLemma {
                        kind: ay_core::TheoryLemmaKind::StringGroundEval,
                        clause,
                        ..
                    } if !ay_proof::recognize_string_ground_eval(&self.ctx.terms, clause)
                )
            });
            if unvalidated_string_lemma {
                return false;
            }
            // Same fail-closed re-validation for the SYMBOLIC regex lane
            // (#regex-cert). `--self-check` consults the PARTIAL checker, so a
            // `RegexIntersectEmpty` lemma would otherwise ship on the strength
            // of the classifier alone. Re-run the checker's own independent
            // derivative-product emptiness decision here: a lemma whose clause
            // has no `str.in_re` group the checker proves EMPTY is not a
            // tautology, and the UNSAT must degrade to `unknown`.
            let unvalidated_regex_lemma = proof.steps.iter().any(|s| {
                matches!(
                    s,
                    ProofStep::TheoryLemma {
                        kind: ay_core::TheoryLemmaKind::RegexIntersectEmpty,
                        clause,
                        ..
                    } if !ay_proof::recognize_regex_intersect_empty(&self.ctx.terms, clause)
                )
            });
            if unvalidated_regex_lemma {
                return false;
            }
            // Same fail-closed re-validation for the str.len length-lemma lane
            // (#selfcert-strlen). `--self-check` consults the PARTIAL checker, so
            // a `StringLengthLemma` retagged from an injected length axiom would
            // otherwise ship on the strength of the emitter's classifier alone.
            // Re-run the checker's own independent structural re-derivation of the
            // exact identity: a lemma whose clause carries no universally-valid
            // str.len theorem is not a tautology, and the UNSAT must degrade to
            // `unknown` rather than ship on a mislabelled leaf.
            let unvalidated_str_len_lemma = proof.steps.iter().any(|s| {
                matches!(
                    s,
                    ProofStep::TheoryLemma {
                        kind: ay_core::TheoryLemmaKind::StringLengthLemma,
                        clause,
                        ..
                    } if !ay_proof::recognize_string_length_lemma(&self.ctx.terms, clause)
                )
            });
            if unvalidated_str_len_lemma {
                return false;
            }
            // Same fail-closed re-validation for the array extensionality lane
            // (#ext-diff-cert), and here it is the LOAD-BEARING check rather
            // than a belt-and-braces one: unlike every other array kind, the
            // Skolemized extensionality clause
            // `(= a b) ∨ ¬(= (select a k) (select b k))` is NOT a tautology —
            // it is a conservative extension, valid only because `k` is a fresh
            // witness bound to exactly this pair. The PARTIAL checker admits a
            // theory lemma on its recorded kind, so without this re-validation a
            // mere relabelling would be enough to ship a bare `unsat`. Re-run
            // the checker's own provenance decision (introduction present, bound
            // once, pair matches, symbol absent from the problem); anything it
            // cannot establish degrades the UNSAT to `unknown`.
            if !self.unsat_proof_extensionality_certified(proof) {
                return false;
            }
            // Leak-2: an `assume` on the empty-clause path whose term is not
            // backed by the problem's provenance (not an original asserted
            // formula, and not a quantifier instantiation tracing back to an
            // asserted `forall`) is a laundered free axiom — an external
            // checker accepts it blindly, so it is exactly as unverified as a
            // `trust` step. Reject it so `--self-check` degrades to `unknown`
            // instead of emitting a bare `unsat` alongside an uncheckable
            // proof (e.g. an injected `seq.len` identity assumed as `true`).
            if self.unsat_proof_terminal_foreign_assume() {
                return false;
            }
            // TIER-0 leak: a proof referencing sequence-theory content
            // (`Seq`-sorted terms) is not independently checkable — carcara
            // rejects the `Seq` sort, no firewall-Lean lemma covers sequences,
            // and there is no DRAT lane. A clean `la_generic`/`resolution`
            // refutation over `seq.nth` terms (zero hole/trust, no foreign
            // assume) would otherwise self-certify and ship a bare `unsat`
            // alongside a proof no external checker can confirm. Degrade to
            // `unknown` instead.
            if self.unsat_proof_references_uncheckable_seq_theory() {
                return false;
            }
            // The internal checker accepted it AND it genuinely derives the
            // empty clause (false) from the assumptions.
            self.proof_check_ok
                && self
                    .proof_check_result
                    .as_ref()
                    .is_some_and(|c| c.total_steps > 0)
                && Self::proof_derives_valid_empty_clause(&self.ctx.terms, proof)
        }
        #[cfg(not(feature = "proof-checker"))]
        {
            false
        }
    }

    #[cfg(feature = "proof-checker")]
    fn proof_shape_summary(proof: &Proof) -> PartialProofCheck {
        let total_steps = proof.steps.len() as u32;
        let skipped_hole_steps = proof
            .steps
            .iter()
            .filter(|step| {
                matches!(
                    step,
                    ProofStep::Step {
                        rule: AletheRule::Hole,
                        ..
                    }
                )
            })
            .count() as u32;

        PartialProofCheck {
            checked_steps: total_steps.saturating_sub(skipped_hole_steps),
            skipped_hole_steps,
            total_steps,
        }
    }

    #[cfg(feature = "proof-checker")]
    fn record_proof_check_stats(&mut self, failures: u64, summary: PartialProofCheck) {
        // Record whether the internal checker accepted the refutation with no
        // errors. `--self-check` consults this (plus hole-freeness) before it
        // will emit `unsat` rather than a sound `unknown`.
        self.proof_check_ok = failures == 0;
        self.last_statistics
            .set_int(PROOF_CHECKER_FAILURES_KEY, failures);
        self.last_statistics.set_int(
            PROOF_CHECKER_SKIPPED_HOLE_STEPS_KEY,
            u64::from(summary.skipped_hole_steps),
        );
        self.last_statistics.set_int(
            PROOF_CHECKER_CHECKED_STEPS_KEY,
            u64::from(summary.checked_steps),
        );
        self.last_statistics.set_int(
            PROOF_CHECKER_TOTAL_STEPS_KEY,
            u64::from(summary.total_steps),
        );
    }
}
