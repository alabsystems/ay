// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof term rewriting for surface-syntax preservation.
//!
//! AY internally canonicalizes some operators (e.g. `>=` → `<=` with swapped
//! operands) for hash-consing efficiency. Proof checkers like Carcara match
//! `assume` steps against the original problem file's assertions, so we must
//! rewrite canonical terms back to their surface syntax before export.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Proof, ProofStep, TermId};

use super::proof_surface_syntax::collect_surface_term_overrides;
use super::Executor;

impl Executor {
    /// Original problem assertions that still have source-syntax provenance.
    pub(crate) fn proof_problem_assertions(&self) -> Vec<TermId> {
        if let Some(provenance) = &self.proof_problem_assertion_provenance {
            return provenance.problem_assertions.clone();
        }
        self.proof_original_problem_assertions()
    }

    /// Original assertion stack aligned with `assertions_parsed()`.
    pub(crate) fn proof_original_problem_assertions(&self) -> Vec<TermId> {
        if let Some(provenance) = &self.proof_problem_assertion_provenance {
            return provenance.original_problem_assertions.clone();
        }
        let parsed_len = self.ctx.assertions_parsed().len();
        if parsed_len == 0 {
            self.ctx.assertions.clone()
        } else {
            let prefix_len = parsed_len.min(self.ctx.assertions.len());
            self.ctx.assertions[..prefix_len].to_vec()
        }
    }

    /// Build the demotion whitelist for proof export.
    ///
    /// When provenance is active (combined deferred-postprocessing routes),
    /// the whitelist is restricted to problem assertions and their De Morgan
    /// duals — temporary derived constraints (mod/div side conditions, array
    /// axioms) are excluded so they get demoted to `trust` (#6759).
    ///
    /// When provenance is inactive, the legacy #6365 behavior is preserved:
    /// all current `self.ctx.assertions` plus their duals are whitelisted.
    fn proof_exportable_assertions(&mut self, rewrites: &HashMap<TermId, TermId>) -> Vec<TermId> {
        let mut exportable: Vec<TermId> = self.proof_problem_assertions();
        for assertion in self.proof_original_problem_assertions() {
            if !exportable.contains(&assertion) {
                exportable.push(assertion);
            }
        }

        if self.proof_problem_assertion_provenance.is_none() {
            // Legacy path: union all current assertions (#6365).
            // FlattenAnd preprocessing can expand one parsed assertion into
            // multiple solver-visible assertions; these are still legitimate
            // problem assertions and must not be demoted.
            for &assertion in &self.ctx.assertions {
                if !exportable.contains(&assertion) {
                    exportable.push(assertion);
                }
            }
        }

        // Tseitin activation clauses for `and`-assertions use the De Morgan
        // dual form produced by normalize_positive_literal. Compute duals from
        // the exportable subset only — not from raw temporary assertions when
        // provenance is active (#6365 Phase 2, narrowed by #6759).
        let dual_source: Vec<TermId> = if self.proof_problem_assertion_provenance.is_some() {
            exportable.clone()
        } else {
            self.ctx.assertions.clone()
        };
        for assertion in dual_source {
            if let TermData::App(sym, args) = self.ctx.terms.get(assertion).clone() {
                if sym.name() == "and" {
                    let negated_args: Vec<TermId> = args
                        .into_iter()
                        .map(|arg| self.ctx.terms.mk_not(arg))
                        .collect();
                    let disjunction = self.ctx.terms.mk_or(negated_args);
                    let dual = self.ctx.terms.mk_not_raw(disjunction);
                    exportable.push(dual);
                }
            }
        }

        if let Some(assumptions) = &self.last_assumptions {
            for &assumption in assumptions {
                if !exportable.contains(&assumption) {
                    exportable.push(assumption);
                }
            }
        }

        if !rewrites.is_empty() {
            let mut cache = HashMap::default();
            let rewritten: Vec<TermId> = exportable
                .iter()
                .copied()
                .map(|a| Self::rewrite_term(&mut self.ctx.terms, a, rewrites, &mut cache))
                .collect();
            for assertion in rewritten {
                if !exportable.contains(&assertion) {
                    exportable.push(assertion);
                }
            }
        }

        exportable
    }

    /// Rewrite proof terms to use surface syntax for canonicalized operators,
    /// then run the ASSUME-AUTHORIZATION tail.
    ///
    /// Only the surface-override collection needs the parsed AST. Everything
    /// after it — `demote_auxiliary_non_problem_assumptions`,
    /// `derive_conjunct_assumptions_from_problem_roots`,
    /// `demote_non_problem_assumptions` and
    /// `rebuild_trust_leaf_proof_from_original_assertions` — decides whether
    /// the MANDATORY UNSAT certificate can be minted at all, and must run
    /// whether or not a parsed AST was retained.
    ///
    /// #retain-parsed-verdict-divergence. Retaining the parsed AST is a
    /// peak-RSS optimization the CLI turns OFF whenever no proof artifact can
    /// be emitted (`--no-proof`, `--z3-mode`, competition mode —
    /// `crates/ay/src/run.rs`), on the documented premise that "verdicts are
    /// unaffected; every consumer degrades gracefully on an empty prefix".
    /// That premise was false BECAUSE of this early return: skipping it also
    /// skipped the demotion pass, so an `assume` leaf left behind by an
    /// in-place preprocessing rewrite (e.g. the QF_ABV dense finite-array
    /// initializer rewrite) stayed a bare `assume` instead of becoming a
    /// `trust` step, and strict certification HARD-REJECTED the whole
    /// refutation with "assumes term outside the supplied problem obligation".
    /// Measured on this commit: six QF_ABV instances that z3, the library API
    /// and default CLI mode all decide `unsat` published `unknown` under
    /// `--z3-mode`/`--no-proof` — i.e. exactly the mode used for z3 parity.
    /// Moving the same `(set-option :produce-proofs true/false)` toggle from
    /// AFTER the assertions to BEFORE them (the only effect of which is to
    /// retain the parsed stack) flipped the verdict back to `unsat`.
    ///
    /// This grants no new authority: a demoted assume becomes a `trust` step
    /// that `mint_unsat_certificate` must still discharge INDEPENDENTLY (the
    /// forged-UNSAT fresh re-solve, full strict validation of every non-trust
    /// step, and per-clause confirmation) before the verdict may publish. It
    /// only makes the two CLI modes agree on the reference behaviour the
    /// library API and default mode already have.
    ///
    /// The overrides themselves still degrade to nothing without a parsed
    /// stack: both `override_pairs` arms zip against `parsed_assertions`, so
    /// an empty parsed stack yields no pairs and no term overrides.
    pub(super) fn apply_input_syntax_rewrites_to_proof(&mut self, proof: &mut Proof) {
        self.last_proof_term_overrides = None;
        if self.ctx.assertions.is_empty() {
            return;
        }

        let aux_assume_steps =
            Self::collect_assume_steps_with_aux_mod_div_vars(&self.ctx.terms, proof);
        let mut rewrites: HashMap<TermId, TermId> = HashMap::default();
        let mut term_overrides: HashMap<TermId, String> = HashMap::default();
        let problem_assertions = self.proof_problem_assertions();
        // Borrow, don't deep-clone: the parsed assertion ASTs are only read
        // while building `override_pairs` (which clones exactly the pairs it
        // keeps); the wholesale `.to_vec()` doubled that cost on every UNSAT
        // (#proof-tax: recursive `Term::clone` of the whole problem was the
        // single largest rewrite-pass leaf on the qg5 QF_UF family).
        let parsed_assertions: &[ay_frontend::command::Term] = self.ctx.assertions_parsed();
        // Collect (canonical, parsed) pairs first: override collection
        // re-elaborates surface subterms, which needs `&mut self.ctx`.
        let override_pairs: Vec<(TermId, ay_frontend::command::Term)> =
            if let Some(provenance) = &self.proof_problem_assertion_provenance {
                let original_problem_assertions = self.proof_original_problem_assertions();
                let parsed_by_original: HashMap<TermId, _> = original_problem_assertions
                    .iter()
                    .copied()
                    .zip(parsed_assertions.iter())
                    .collect();
                let mut pairs = Vec::new();
                for &canonical in &problem_assertions {
                    let Some(source_sets) = provenance.assertion_sources.get(&canonical) else {
                        continue;
                    };
                    for source_set in source_sets {
                        if let [source] = source_set.as_slice() {
                            if let Some(parsed) = parsed_by_original.get(source) {
                                pairs.push((canonical, (*parsed).clone()));
                            }
                        }
                    }
                }
                // Original assertions that appear in MULTI-source provenance
                // sets (e.g. a propagated theory atom sourced from a Boolean
                // definition `(= c atom)` plus the defining literal `c`) are
                // problem premises in their own right: the derivation pass can
                // re-introduce them as `assume` steps. Pair each with its own
                // parsed form so those assumes — and their surface subterms —
                // print with the problem file's syntax and carcara can match
                // them to the original premises.
                let mut paired: ay_core::kani_compat::DetHashSet<TermId> =
                    pairs.iter().map(|(c, _)| *c).collect();
                for source_sets in provenance.assertion_sources.values() {
                    for source_set in source_sets {
                        if source_set.len() < 2 {
                            continue;
                        }
                        for &source in source_set {
                            if paired.insert(source) {
                                if let Some(parsed) = parsed_by_original.get(&source) {
                                    pairs.push((source, (*parsed).clone()));
                                }
                            }
                        }
                    }
                }
                pairs
            } else {
                problem_assertions
                    .iter()
                    .zip(parsed_assertions.iter())
                    .map(|(&canonical, parsed)| (canonical, parsed.clone()))
                    .collect()
            };
        for (canonical, parsed) in &override_pairs {
            collect_surface_term_overrides(&mut self.ctx, *canonical, parsed, &mut term_overrides);
        }

        Self::infer_auxiliary_division_rewrites(&mut self.ctx.terms, proof, &mut rewrites);

        // #authored-aux-name-collision — this surface rewrite is COSMETIC (it
        // prints `div`/`mod` in the exported proof instead of the client's
        // quotient/remainder encoding), but it can move an `Assume` LEAF out of
        // the authored problem obligation, and an unauthorized assume is a hard
        // reject in the mandatory strict certification. A correct `unsat` then
        // publishes as `unknown`. Print fidelity must yield to the verdict.
        //
        // The trigger is that `as_aux_quotient_var` / `as_aux_remainder_var`
        // recognise the encoder's auxiliaries purely by variable NAME PREFIX
        // (`_mod_q`, `_div_q`, `_divmod_q` and the `_r` twins). AY's own
        // div/mod elimination never mints those names — only ay-chc's
        // `ChcExpr::eliminate_mod` does, and it declares them to the executor as
        // ordinary `(declare-const _mod_q_0 Int)`. So every variable this
        // heuristic ever matches belongs to the CLIENT, and the "side
        // conditions" it infers from are frequently DERIVED terms (here, the
        // post-substitution `(= (+ (* _mod_q_2 2) _mod_r_3) (+ (* _mod_q_0 2)
        // _mod_r_1 1))`) rather than authored ones — so filtering on "is this an
        // authored assertion" does not catch it. What is decisive is the effect:
        // if applying the rewrites would change an `Assume` leaf into a term the
        // obligation does not contain, drop the whole rewrite.
        //
        // Verified on the query
        // `adaptive::tests::test_try_synthesis_accepts_chccomp_extra_small_lia_safe_summaries`
        // issues: renaming ONLY `_mod_q_`/`_mod_r_` to `zzq`/`zzr` in the dumped
        // `.smt2` — semantically identical, and enough to make the heuristic miss
        // — flipped it from `unknown (self-check-rejected)` to `unsat`.
        if !rewrites.is_empty() {
            let obligation = self.problem_assertions_for_strict_proof();
            let mut cache: HashMap<TermId, TermId> = HashMap::default();
            let breaks_authorization = proof.steps.iter().any(|step| {
                let ProofStep::Assume(term) = step else {
                    return false;
                };
                let rewritten =
                    Self::rewrite_term(&mut self.ctx.terms, *term, &rewrites, &mut cache);
                rewritten != *term && !obligation.contains(&rewritten)
            });
            if breaks_authorization {
                rewrites.clear();
            }
        }

        if !rewrites.is_empty() {
            let step_count_before = proof.steps.len();
            Self::rewrite_proof_terms(&mut self.ctx.terms, proof, &rewrites);
            debug_assert_eq!(
                proof.steps.len(),
                step_count_before,
                "BUG: proof rewriting changed step count from {} to {}",
                step_count_before,
                proof.steps.len()
            );
            Self::fixup_resolution_conclusions(&self.ctx.terms, proof);
        }

        if !term_overrides.is_empty() {
            self.last_proof_term_overrides = Some(term_overrides);
        }
        let extended_assertions = self.proof_exportable_assertions(&rewrites);
        Self::demote_auxiliary_non_problem_assumptions(
            proof,
            &extended_assertions,
            &aux_assume_steps,
        );
        // Conjunct assumes introduced by top-level and-flattening are DERIVED
        // from their asserted conjunction (assume + and_pos + th_resolution)
        // before the demotion below would turn them into unverified `trust`
        // steps and fail-close the strict checker on the whole proof.
        Self::derive_conjunct_assumptions_from_problem_roots(
            &mut self.ctx.terms,
            proof,
            &extended_assertions,
        );
        Self::demote_non_problem_assumptions(proof, &extended_assertions);
        // Last resort for proofs the demotion left trust-bearing (substituted
        // input clauses whose link to the original assertions was lost in
        // preprocessing): re-prove the contradiction directly from the
        // ORIGINAL problem assertions with certified theory lemmas. No-op on
        // trust-free proofs; keeps the existing proof on any failure.
        self.rebuild_trust_leaf_proof_from_original_assertions(proof);
    }
}

#[cfg(test)]
#[path = "proof_rewrite_tests.rs"]
mod proof_rewrite_tests;
