// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof Tracking for SMT Solving
//!
//! This module provides proof generation during SMT solving. When enabled,
//! the solver collects proof steps that can be exported in Alethe format
//! for independent verification using tools like carcara.
//!
//! ## VerifierConsumer Integration
//!
//! Proof certificates are critical for VerifierConsumer (verified Rust compiler):
//! - Verification conditions are checked by AY
//! - Proof certificates allow independent verification of results
//! - Unsat proofs are especially important for proving safety properties
//!
//! ## Alethe Proof Format
//!
//! The proof tracker generates steps compatible with the Alethe format:
//! - `assume`: Input assertions from the SMT-LIB problem
//! - `step`: Inference steps with rules, premises, and conclusion clauses
//! - Theory lemmas are recorded with appropriate theory-specific rules
//!
//! ## Usage
//!
//! ```no_run
//! use ay_dpll::Executor;
//! use ay_frontend::parse;
//! use ay_proof::export_alethe;
//!
//! let input = r#"
//!     (set-option :produce-proofs true)
//!     (set-logic QF_UF)
//!     (declare-const a Bool)
//!     (assert a)
//!     (assert (not a))
//!     (check-sat)
//! "#;
//! let commands = parse(input).unwrap();
//! let mut exec = Executor::new();
//! let outputs = exec.execute_all(&commands).unwrap();
//! assert_eq!(outputs, vec!["unsat"]);
//!
//! if let Some(proof) = exec.last_proof() {
//!     let alethe = export_alethe(proof, exec.terms());
//!     println!("{}", alethe);
//! }
//! ```

use std::sync::Arc;

#[cfg(test)]
mod explicit_trust_census_tests;
#[cfg(test)]
mod tests;

pub(crate) mod checkpoint_budget;

#[cfg(test)]
#[path = "checkpoint_budget_tests.rs"]
mod checkpoint_budget_tests;
mod lemma_dedup;
mod vacuous_collapse;

use lemma_dedup::{LemmaDedupMap, LemmaKey};

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{
    AletheRule, FarkasAnnotation, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore,
    TheoryLemmaKind, TheoryLit,
};

/// Opaque snapshot for a speculative proof-tracking window.
///
/// Proof steps and the tracker's deduplication/scope metadata form one ledger:
/// rolling back only `Proof::steps` would leave `ProofId`s that can alias later
/// steps. Keep the snapshot private so callers can only restore the coherent
/// step/map/scope ledger through [`ProofTracker::rollback_to`]. A ledger
/// replacement is detected and reported because the moved proof may have
/// escaped to another artifact.
#[derive(Debug)]
pub(crate) struct ProofTrackerCheckpoint {
    steps: Vec<ProofStep>,
    ledger_identity: Arc<()>,
    ledger_epoch: u64,
    assumption_map: HashMap<TermId, ProofId>,
    lemma_map: LemmaDedupMap,
    named_steps: HashMap<String, ProofId>,
    scope_stack: Vec<usize>,
    scope_assumption_maps: Vec<HashMap<TermId, ProofId>>,
    scope_lemma_maps: Vec<LemmaDedupMap>,
    scope_named_steps: Vec<HashMap<String, ProofId>>,
    enabled: bool,
    theory_name: String,
}

/// Proof tracker for collecting SMT proof steps during solving
///
/// The tracker collects:
/// 1. Assumptions from input assertions
/// 2. Theory lemmas from theory solver conflicts
/// 3. Resolution steps from SAT solver (when available)
///
/// ## Incremental scoping
///
/// Push/pop scope the accumulated proof steps. On `pop()`, all proof steps
/// added since the matching `push()` are removed, along with their
/// deduplication entries. This prevents stale theory lemmas from appearing
/// in proofs after a scope retraction (#4534).
#[derive(Debug)]
pub(crate) struct ProofTracker {
    /// The accumulated proof
    proof: Proof,
    /// Mapping from assertion term IDs to their proof step IDs
    assumption_map: HashMap<TermId, ProofId>,
    /// Hash-first mapping from theory lemma content to proof step IDs (#A4)
    lemma_map: LemmaDedupMap,
    /// Whether proof tracking is enabled
    enabled: bool,
    /// Theory name for the current solving context
    theory_name: String,
    /// Scope stack for incremental push/pop (stores proof step watermarks)
    scope_stack: Vec<usize>,
    /// Exact map snapshots paired with `scope_stack`. A scoped insertion can
    /// alias an older `ProofId` without adding a step, so an ID cutoff alone
    /// cannot identify everything that push/pop must remove.
    scope_assumption_maps: Vec<HashMap<TermId, ProofId>>,
    scope_lemma_maps: Vec<LemmaDedupMap>,
    scope_named_steps: Vec<HashMap<String, ProofId>>,
    /// Changes whenever the proof ledger is moved/replaced. Ordinary
    /// truncation is exactly reversible because checkpoints own the complete
    /// retained step/map/scope prefix; a moved proof may have escaped and is
    /// therefore reported rather than reconstructed.
    // `ProofTracker` deliberately remains non-Clone: duplicating this Arc into
    // two live trackers would make unrelated ledgers pass the identity check.
    ledger_identity: Arc<()>,
    ledger_epoch: u64,
}

impl Default for ProofTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofTracker {
    /// Create a new proof tracker (disabled by default)
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            proof: Proof::new(),
            assumption_map: HashMap::default(),
            lemma_map: LemmaDedupMap::default(),
            enabled: false,
            theory_name: "UNKNOWN".to_string(),
            scope_stack: Vec::new(),
            scope_assumption_maps: Vec::new(),
            scope_lemma_maps: Vec::new(),
            scope_named_steps: Vec::new(),
            ledger_identity: Arc::new(()),
            ledger_epoch: 0,
        }
    }

    /// Enable proof tracking
    pub(crate) fn enable(&mut self) {
        self.enabled = true;
    }

    /// Disable proof tracking
    pub(crate) fn disable(&mut self) {
        self.enabled = false;
    }

    /// Check if proof tracking is enabled
    #[must_use]
    pub(crate) fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Set the theory name for subsequent theory lemmas
    pub(crate) fn set_theory(&mut self, theory: impl Into<String>) {
        self.theory_name = theory.into();
    }

    fn advance_ledger_epoch(&mut self) {
        self.ledger_epoch = self
            .ledger_epoch
            .checked_add(1)
            .expect("proof tracker ledger epoch exhausted");
    }

    fn replace_ledger_identity(&mut self) {
        self.ledger_identity = Arc::new(());
        self.advance_ledger_epoch();
    }

    fn clear_scope_ledger_snapshots(&mut self) {
        self.scope_stack.fill(0);
        for map in &mut self.scope_assumption_maps {
            map.clear();
        }
        for map in &mut self.scope_lemma_maps {
            map.clear();
        }
        for map in &mut self.scope_named_steps {
            map.clear();
        }
    }

    /// Record an assumption (input assertion)
    ///
    /// Returns the proof step ID for this assumption, or None if tracking is disabled.
    pub(crate) fn add_assumption(&mut self, term: TermId, name: Option<String>) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }

        // Check if we already have this assumption
        if let Some(&id) = self.assumption_map.get(&term) {
            return Some(id);
        }

        // A preprocessing producer may already have certified this exact unit
        // from authored roots (Skolemization, arithmetic normalization, packed
        // theory clause). Reuse that derivation; never add a second, stronger
        // `Assume` for the solver-visible replacement.
        if let Some(id) = self.lemma_map.get(TheoryLemmaKind::Generic, &[term], None) {
            self.assumption_map.insert(term, id);
            return Some(id);
        }

        let id = self.proof.add_assume(term, name);
        self.assumption_map.insert(term, id);
        Some(id)
    }

    /// Record a bare `Generic` theory lemma — an EXPLICIT TRUST admission
    /// (#trust->0 C6 API ratchet; formerly `add_theory_lemma`).
    ///
    /// The clause is the disjunction of literals that the theory solver derived.
    /// Returns the proof step ID for this lemma, or None if tracking is disabled.
    ///
    /// `Generic` is the only trust kind (`is_trust()`), so every step recorded
    /// here can enter a published proof only through the deferred-trust
    /// discharge lane — it is never strict-checkable on its own. The name makes
    /// that cost visible at the call site: a NEW caller must either supply a
    /// typed kind (`add_theory_lemma_with_kind`,
    /// `add_theory_lemma_with_farkas_and_kind`, or the `theory_inference`
    /// classifier funnel) or name the trust by writing this method — and every
    /// call site is inventoried by the census test
    /// (`proof_tracker/explicit_trust_census_tests.rs`), so a new site fails
    /// the build until it is vetted there. Behavior is byte-identical to the
    /// old `add_theory_lemma`.
    #[doc(hidden)]
    pub(crate) fn add_explicit_trust_lemma(&mut self, clause: Vec<TermId>) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }

        // Check if we already have this lemma (hash-first: no allocation on
        // the dedup hit path, #A4).
        if let Some(id) = self.lemma_map.get(TheoryLemmaKind::Generic, &clause, None) {
            return Some(id);
        }

        let key = LemmaKey::new(TheoryLemmaKind::Generic, &clause, None);
        let id = self.proof.add_theory_lemma(&self.theory_name, clause);
        self.lemma_map.insert(key, id);
        Some(id)
    }

    /// Record a decomposed combined-theory conflict (#combined-theory-decompose).
    ///
    /// `core` is a single-theory sub-lemma with a strict-checkable `kind`, and
    /// `full` is the complete blocking clause with `core` as a PREFIX. Emits the
    /// core under its real kind and then a `weakening` step up to `full`, so the
    /// caller's downstream consumers still see the clause they expect while the
    /// justification is checkable instead of `Generic`/trust.
    ///
    /// Both halves are validated by the strict checker: the core by its kind's
    /// own validator, and the weakening by `validate_weakening`, which requires
    /// exactly the prefix relationship the caller must establish.
    pub(crate) fn add_theory_lemma_weakened(
        &mut self,
        core: Vec<TermId>,
        kind: TheoryLemmaKind,
        full: Vec<TermId>,
    ) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }
        debug_assert!(
            full.len() >= core.len() && full[..core.len()] == core[..],
            "BUG: weakened theory lemma requires the core to be a prefix of the full clause"
        );
        if full.len() < core.len() || full[..core.len()] != core[..] {
            return self.add_explicit_trust_lemma(full);
        }
        let core_id = self.add_theory_lemma_with_kind(core, kind)?;
        Some(
            self.proof
                .add_rule_step(AletheRule::Weakening, full, vec![core_id], Vec::new()),
        )
    }

    /// Record a theory lemma (conflict clause) with a specified Alethe rule kind.
    pub(crate) fn add_theory_lemma_with_kind(
        &mut self,
        clause: Vec<TermId>,
        kind: TheoryLemmaKind,
    ) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }

        // `LiaGeneric`/`LraFarkas` require a certificate at export time. This
        // method has no Farkas or LIA evidence to attach, so record honest
        // trust and let later reconstruction promote it if possible (#8866).
        let kind = if matches!(
            kind,
            TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas
        ) {
            TheoryLemmaKind::Generic
        } else {
            kind
        };
        if let Some(id) = self.lemma_map.get(kind, &clause, None) {
            return Some(id);
        }

        let key = LemmaKey::new(kind, &clause, None);
        let generic_unit_term = (clause.len() == 1).then(|| clause[0]);
        let id = self
            .proof
            .add_theory_lemma_with_kind(&self.theory_name, clause, kind);
        self.lemma_map.insert(key, id);
        // Solver-visible packed axioms are registered later through
        // `add_assumption(term)`. Index an already certified singleton under
        // that generic unit lookup too, so registration reuses the theorem
        // instead of adding a stronger free `Assume` for the same term.
        if let Some(term) = generic_unit_term {
            // Preserve an older certified singleton at an outer scope. If an
            // inner specialized lemma shadowed this alias, `pop()` could remove
            // the inner id but could not reconstruct the overwritten mapping,
            // orphaning the still-live outer proof step from deduplication.
            self.lemma_map
                .or_insert(LemmaKey::new(TheoryLemmaKind::Generic, &[term], None), id);
        }
        Some(id)
    }

    /// Record an arithmetic theory lemma with Farkas coefficients and explicit kind.
    pub(crate) fn add_theory_lemma_with_farkas_and_kind(
        &mut self,
        clause: Vec<TermId>,
        farkas: FarkasAnnotation,
        kind: TheoryLemmaKind,
    ) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }
        debug_assert!(
            farkas.coefficients.len() == clause.len(),
            "BUG: Farkas coefficient count ({}) != clause length ({})",
            farkas.coefficients.len(),
            clause.len()
        );

        if let Some(id) = self.lemma_map.get(kind, &clause, Some(&farkas)) {
            return Some(id);
        }

        let key = LemmaKey::new(kind, &clause, Some(&farkas));
        let id = self.proof.add_theory_lemma_with_farkas_and_kind(
            &self.theory_name,
            clause,
            farkas,
            kind,
        );
        self.lemma_map.insert(key, id);
        Some(id)
    }

    /// Record a certified flat arithmetic clause and derive its asserted
    /// packed `(or ...)` unit with exact Boolean tautologies.
    pub(crate) fn add_packed_farkas_lemma(
        &mut self,
        terms: &mut TermStore,
        or_term: TermId,
        clause: Vec<TermId>,
        farkas: FarkasAnnotation,
        kind: TheoryLemmaKind,
    ) -> Option<ProofId> {
        if !self.enabled || clause.len() < 2 {
            return None;
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(or_term) else {
            return None;
        };
        if name != "or" || args != &clause {
            return None;
        }
        let mut current_id =
            self.add_theory_lemma_with_farkas_and_kind(clause.clone(), farkas, kind)?;
        let mut current_clause = clause;
        for literal in current_clause.clone() {
            let complement = match terms.get(literal) {
                TermData::Not(inner) => *inner,
                _ => terms.mk_not_raw(literal),
            };
            let or_neg = self.proof.add_rule_step(
                AletheRule::OrNeg,
                vec![or_term, complement],
                Vec::new(),
                vec![or_term],
            );
            let position = current_clause.iter().position(|&item| item == literal)?;
            let _ = current_clause.remove(position);
            current_clause.push(or_term);
            current_id =
                self.proof
                    .add_resolution(current_clause.clone(), literal, current_id, or_neg);
        }
        let packed = self.proof.add_rule_step(
            AletheRule::Contraction,
            vec![or_term],
            vec![current_id],
            Vec::new(),
        );
        self.lemma_map.insert(
            LemmaKey::new(TheoryLemmaKind::Generic, &[or_term], None),
            packed,
        );
        Some(packed)
    }

    /// Record Alethe's exact arithmetic antisymmetry split and its Boolean
    /// decomposition as one reusable flat clause.
    ///
    /// `or_term` must be `(or (= a b) (not (<= a b)) (not (<= b a)))`, and
    /// `clause` must be those three disjuncts.  The producer constructs that
    /// rigid shape; `ay-proof` independently re-validates it in strict mode.
    /// Keeping both steps in the tracker lets SAT-trace reconstruction reuse
    /// the flat clause directly, instead of treating the injected tautology as
    /// an input `Assume`.
    pub(crate) fn add_la_disequality_lemma(
        &mut self,
        or_term: TermId,
        clause: Vec<TermId>,
    ) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }

        if let Some(id) = self.lemma_map.get(TheoryLemmaKind::Generic, &clause, None) {
            return Some(id);
        }

        let key = LemmaKey::new(TheoryLemmaKind::Generic, &clause, None);
        let split = self.proof.add_rule_step(
            AletheRule::LaDisequality,
            vec![or_term],
            Vec::new(),
            Vec::new(),
        );
        let flat = self
            .proof
            .add_rule_step(AletheRule::Or, clause, vec![split], Vec::new());
        self.lemma_map.insert(key, flat);
        Some(flat)
    }

    /// Derive the exact NNF assertion created from a skolemizer-recorded
    /// negative, single-binder `forall`.
    ///
    /// This method is deliberately narrow: it accepts only
    /// `not(forall x. antecedent => consequent)` where the internal implication
    /// is the canonical `or` (often flattened by De Morgan), and
    /// `skolemized_body` is exactly the conjunction of every disjunct's Boolean
    /// complement (flattening a complemented conjunction). The
    /// witness/source/instance triple is
    /// supplied by the actual Skolemizer, never reconstructed from a name.
    ///
    /// The proof is: authored source Assume; certified `sko_forall` equality;
    /// Boolean equivalence/resolution to `not(instance)`; one exact `or_neg`
    /// elimination per implication disjunct; `and_pos` projections; and
    /// `and_neg` introduction of the solver-visible NNF conjunction.
    pub(crate) fn add_single_forall_skolemized_assertion(
        &mut self,
        terms: &mut TermStore,
        original_not_forall: TermId,
        quantified: TermId,
        instance: TermId,
        witness: TermId,
        skolemized_body: TermId,
    ) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }

        let TermData::Not(source) = terms.get(original_not_forall) else {
            return None;
        };
        if *source != quantified {
            return None;
        }
        let TermData::Forall(bindings, _, _) = terms.get(quantified) else {
            return None;
        };
        if bindings.len() != 1
            || !matches!(terms.get(witness), TermData::Var(name, _)
                if terms.is_skolem_symbol(name))
        {
            return None;
        }

        let TermData::App(Symbol::Named(or_name), disjuncts) = terms.get(instance).clone() else {
            return None;
        };
        if or_name != "or" || disjuncts.len() < 2 {
            return None;
        }

        // Boolean-normalized complement: AY represents `not(not a)` as `a`.
        // The strict checker validates this exact involution and the printer
        // restores an explicit `not_not` bridge for Alethe.
        fn complement(terms: &mut TermStore, term: TermId) -> TermId {
            match terms.get(term) {
                TermData::Not(inner) => *inner,
                _ => terms.mk_not_raw(term),
            }
        }
        let mut disjunct_complements = Vec::with_capacity(disjuncts.len());
        let mut final_units = Vec::with_capacity(disjuncts.len());
        for &disjunct in &disjuncts {
            let disjunct_complement = complement(terms, disjunct);
            // The Skolemizer keeps ITE conditions opaque while pushing the
            // negative polarity into both branches:
            //
            //   (not (ite c t e))  ==>  (ite c (not t) (not e)).
            //
            // Preserve that exact source/target pair here.  Restrict the
            // bridge to an unsimplified Boolean ITE with the same condition
            // and exact branch complements; every other rewrite fails closed.
            let nnf_complement = match terms.get(disjunct).clone() {
                TermData::Ite(cond, then_branch, else_branch) => {
                    let not_then = complement(terms, then_branch);
                    let not_else = complement(terms, else_branch);
                    let target = terms.mk_ite(cond, not_then, not_else);
                    match terms.get(target) {
                        TermData::Ite(target_cond, target_then, target_else)
                            if *target_cond == cond
                                && *target_then == not_then
                                && *target_else == not_else =>
                        {
                            target
                        }
                        _ => return None,
                    }
                }
                _ => disjunct_complement,
            };
            disjunct_complements.push((disjunct_complement, nnf_complement));
            match terms.get(nnf_complement) {
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    final_units.extend(args.iter().copied());
                }
                _ => final_units.push(nnf_complement),
            }
        }
        final_units.sort_unstable();
        final_units.dedup();
        if terms.mk_and(final_units.clone()) != skolemized_body {
            return None;
        }
        let TermData::App(Symbol::Named(final_name), final_args) =
            terms.get(skolemized_body).clone()
        else {
            return None;
        };
        if final_name != "and" || final_args != final_units {
            return None;
        }

        let source_id = self.add_assumption(original_not_forall, None)?;
        // Do not use `mk_eq`: Boolean equality canonicalization may swap sides,
        // while sko_forall's source side is load-bearing.
        let equality = terms.mk_app(Symbol::named("="), [quantified, instance], Sort::Bool);
        let skolem_id = self.proof.add_rule_step(
            AletheRule::Skolem,
            vec![equality],
            Vec::new(),
            vec![witness],
        );
        let not_equality = terms.mk_not_raw(equality);
        let not_instance = terms.mk_not_raw(instance);
        let equiv_id = self.proof.add_rule_step(
            AletheRule::EquivPos1,
            vec![not_equality, quantified, not_instance],
            Vec::new(),
            Vec::new(),
        );
        let quant_or_not_instance = self.proof.add_resolution(
            vec![quantified, not_instance],
            equality,
            skolem_id,
            equiv_id,
        );
        let not_instance_id = self.proof.add_resolution(
            vec![not_instance],
            quantified,
            source_id,
            quant_or_not_instance,
        );

        // Derive the exact complement of each implication disjunct from
        // `not(instance)`. This is operand-order independent (unlike treating
        // the canonical, TermId-sorted `or` as a positional implication).
        let mut unit_ids: HashMap<TermId, ProofId> = HashMap::default();
        for (disjunct_complement, nnf_complement) in disjunct_complements {
            let or_neg = self.proof.add_rule_step(
                AletheRule::OrNeg,
                vec![instance, disjunct_complement],
                Vec::new(),
                vec![instance],
            );
            let unit = self.proof.add_resolution(
                vec![disjunct_complement],
                instance,
                not_instance_id,
                or_neg,
            );
            unit_ids.insert(disjunct_complement, unit);

            // Strictly derive the Skolemizer's NNF ITE complement from the
            // raw `(not (ite ...))` unit.  The four Boolean rules are checked
            // independently by ay-proof; the three resolutions leave exactly
            // the target ITE as a unit.
            let normalized_unit = if nnf_complement != disjunct_complement {
                let TermData::Not(source_ite) = terms.get(disjunct_complement) else {
                    return None;
                };
                let TermData::Ite(cond, then_branch, else_branch) = terms.get(*source_ite).clone()
                else {
                    return None;
                };
                let not_cond = complement(terms, cond);
                let not_then = complement(terms, then_branch);
                let not_else = complement(terms, else_branch);
                let not_not_then = terms.mk_not_raw(not_then);
                let not_not_else = terms.mk_not_raw(not_else);
                if !matches!(
                    terms.get(nnf_complement),
                    TermData::Ite(target_cond, target_then, target_else)
                        if *target_cond == cond
                            && *target_then == not_then
                            && *target_else == not_else
                ) {
                    return None;
                }

                let source_else = self.proof.add_rule_step(
                    AletheRule::NotIte1,
                    vec![cond, not_else],
                    vec![unit],
                    Vec::new(),
                );
                let source_then = self.proof.add_rule_step(
                    AletheRule::NotIte2,
                    vec![not_cond, not_then],
                    vec![unit],
                    Vec::new(),
                );
                let target_else = self.proof.add_rule_step(
                    AletheRule::IteNeg1,
                    vec![nnf_complement, cond, not_not_else],
                    Vec::new(),
                    Vec::new(),
                );
                let target_then = self.proof.add_rule_step(
                    AletheRule::IteNeg2,
                    vec![nnf_complement, not_cond, not_not_then],
                    Vec::new(),
                    Vec::new(),
                );
                let target_or_cond = self.proof.add_resolution(
                    vec![nnf_complement, cond],
                    not_else,
                    source_else,
                    target_else,
                );
                let target_or_not_cond = self.proof.add_resolution(
                    vec![nnf_complement, not_cond],
                    not_then,
                    source_then,
                    target_then,
                );
                self.proof.add_resolution(
                    vec![nnf_complement],
                    cond,
                    target_or_cond,
                    target_or_not_cond,
                )
            } else {
                unit
            };
            unit_ids.insert(nnf_complement, normalized_unit);

            if let TermData::App(Symbol::Named(name), nested) = terms.get(nnf_complement).clone() {
                if name == "and" {
                    for (index, arg) in nested.into_iter().enumerate() {
                        let not_conjunction = terms.mk_not_raw(nnf_complement);
                        let projection = self.proof.add_rule_step(
                            AletheRule::AndPos(index as u32),
                            vec![not_conjunction, arg],
                            Vec::new(),
                            vec![nnf_complement],
                        );
                        let projected = self.proof.add_resolution(
                            vec![arg],
                            nnf_complement,
                            normalized_unit,
                            projection,
                        );
                        unit_ids.insert(arg, projected);
                    }
                }
            }
        }

        let mut intro_clause = Vec::with_capacity(final_args.len() + 1);
        intro_clause.push(skolemized_body);
        for &arg in &final_args {
            intro_clause.push(complement(terms, arg));
        }
        let mut current_id = self.proof.add_rule_step(
            AletheRule::AndNeg,
            intro_clause.clone(),
            Vec::new(),
            vec![skolemized_body],
        );
        let mut current_clause = intro_clause;
        for &arg in &final_args {
            let unit = *unit_ids.get(&arg)?;
            let arg_complement = complement(terms, arg);
            let position = current_clause
                .iter()
                .position(|&lit| lit == arg_complement)?;
            let _ = current_clause.remove(position);
            current_id = self
                .proof
                .add_resolution(current_clause.clone(), arg, current_id, unit);
        }
        if current_clause != [skolemized_body] {
            return None;
        }

        // The solve pipeline flattens the certified NNF conjunction before
        // proof-context registration. Index every exact derived conjunct so
        // `add_assumption(arg)` reuses its Skolem derivation instead of
        // manufacturing an ambient problem Assume for a preprocessor-created
        // unit. Only units already obtained above by resolution from the
        // authenticated `not(forall)` source are admitted.
        for &arg in &final_args {
            let unit = *unit_ids.get(&arg)?;
            self.lemma_map
                .or_insert(LemmaKey::new(TheoryLemmaKind::Generic, &[arg], None), unit);
        }
        self.lemma_map.insert(
            LemmaKey::new(TheoryLemmaKind::Generic, &[skolemized_body], None),
            current_id,
        );
        Some(current_id)
    }

    pub(crate) fn add_forall_instantiated_assertion(
        &mut self,
        terms: &mut TermStore,
        quantified: TermId,
        values: &[TermId],
        instance: TermId,
    ) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }
        let TermData::Forall(bindings, body, _) = terms.get(quantified).clone() else {
            return None;
        };
        if bindings.is_empty() || bindings.len() != values.len() {
            return None;
        }
        let mut substitution = HashMap::default();
        for ((name, sort), &value) in bindings.iter().zip(values) {
            if terms.sort(value) != sort {
                return None;
            }
            substitution.insert(name.clone(), value);
        }
        if crate::ematching::subst_vars_exact_qf(terms, body, &substitution)? != instance {
            return None;
        }

        let source_id = self.add_assumption(quantified, None)?;
        let not_quantified = terms.mk_not_raw(quantified);
        let implication = terms.mk_app(Symbol::named("or"), [not_quantified, instance], Sort::Bool);
        let forall_inst = self.proof.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            Vec::new(),
            values.to_vec(),
        );
        let clausified = self.proof.add_rule_step(
            AletheRule::Or,
            vec![not_quantified, instance],
            vec![forall_inst],
            Vec::new(),
        );
        let unit = self
            .proof
            .add_resolution(vec![instance], quantified, clausified, source_id);
        self.lemma_map.or_insert(
            LemmaKey::new(TheoryLemmaKind::Generic, &[instance], None),
            unit,
        );

        // If the exact instance is itself arithmetically impossible, close the
        // refutation here before downstream ground preprocessing can fold it to
        // the unauthored constant `false`.  The shared independent Farkas
        // verifier is the authority: unsupported/nonlinear instances simply
        // skip this optimization and keep the derived unit above.
        let complement = match terms.get(instance) {
            TermData::Not(inner) => *inner,
            _ => terms.mk_not_raw(instance),
        };
        let conflict_lit = match terms.get(complement) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(complement, false),
        };
        let farkas = FarkasAnnotation::from_ints(&[1]);
        let closed_by_farkas = if ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            terms,
            &[conflict_lit],
            &farkas,
        )
        .is_ok()
        {
            if let Some(negated_unit) = self.add_theory_lemma_with_farkas_and_kind(
                vec![complement],
                farkas,
                TheoryLemmaKind::LraFarkas,
            ) {
                self.proof
                    .add_resolution(Vec::new(), instance, unit, negated_unit);
                true
            } else {
                false
            }
        } else {
            false
        };
        if !closed_by_farkas && ay_proof::recognize_ground_evaluate(terms, complement) {
            // Alethe's `evaluate` concludes an equality to a concrete value,
            // not the evaluated Boolean literal directly.  Derive the literal
            // from `(= complement true)` with the primitive equivalence and
            // true rules so the internal checker and Carcara see the same
            // certificate shape.
            let truth = terms.true_term();
            let evaluation = terms.mk_app(Symbol::named("="), [complement, truth], Sort::Bool);
            let evaluated = self.proof.add_rule_step(
                AletheRule::Evaluate,
                vec![evaluation],
                Vec::new(),
                Vec::new(),
            );
            let not_evaluation = terms.mk_not_raw(evaluation);
            let not_truth = terms.mk_not_raw(truth);
            let equivalence = self.proof.add_rule_step(
                AletheRule::EquivPos1,
                vec![not_evaluation, complement, not_truth],
                Vec::new(),
                Vec::new(),
            );
            let truth_unit =
                self.proof
                    .add_rule_step(AletheRule::True, vec![truth], Vec::new(), Vec::new());
            let implication = self.proof.add_resolution(
                vec![not_evaluation, complement],
                truth,
                equivalence,
                truth_unit,
            );
            let negated_unit =
                self.proof
                    .add_resolution(vec![complement], evaluation, evaluated, implication);
            self.proof
                .add_resolution(Vec::new(), instance, unit, negated_unit);
        }
        Some(unit)
    }

    /// Derive an E-matching instance of a directly authored `forall` after the
    /// NNF pass has normalized arithmetic negations in its body.
    ///
    /// `normalized_quantified` is only provenance: it never becomes an
    /// assumption. The authored quantifier is instantiated structurally,
    /// preserving every raw connective, and every changed ground disjunct must
    /// then pass the independent Farkas checker as an exact implication before
    /// the solver-visible normalized `or` is reconstructed. This deliberately
    /// supports only a flat, nonempty disjunction with a one-to-one disjunct
    /// mapping; all broader Boolean or quantified rewrites fail closed.
    pub(crate) fn add_normalized_forall_instantiated_assertion(
        &mut self,
        terms: &mut TermStore,
        quantified: TermId,
        normalized_quantified: TermId,
        values: &[TermId],
        instance: TermId,
    ) -> Option<ProofId> {
        if !self.enabled || quantified == normalized_quantified {
            return None;
        }
        let TermData::Forall(bindings, body, triggers) = terms.get(quantified).clone() else {
            return None;
        };
        let TermData::Forall(normalized_bindings, normalized_body, normalized_triggers) =
            terms.get(normalized_quantified).clone()
        else {
            return None;
        };
        if bindings.is_empty()
            || bindings.len() != values.len()
            || bindings != normalized_bindings
            || triggers != normalized_triggers
        {
            return None;
        }

        let mut substitution = HashMap::default();
        for ((name, sort), &value) in bindings.iter().zip(values) {
            if terms.sort(value) != sort {
                return None;
            }
            substitution.insert(name.clone(), value);
        }
        if crate::ematching::subst_vars_exact_qf(terms, normalized_body, &substitution)? != instance
        {
            return None;
        }

        let raw_instance = crate::ematching::subst_vars_exact_qf(terms, body, &substitution)?;
        let TermData::App(Symbol::Named(raw_name), raw_args) = terms.get(raw_instance).clone()
        else {
            return None;
        };
        let TermData::App(Symbol::Named(target_name), target_args) = terms.get(instance).clone()
        else {
            return None;
        };
        if raw_name != "or"
            || target_name != "or"
            || raw_args.len() != target_args.len()
            || raw_args.is_empty()
        {
            return None;
        }

        fn complement(terms: &mut TermStore, term: TermId) -> TermId {
            match terms.get(term) {
                TermData::Not(inner) => *inner,
                _ => terms.mk_not_raw(term),
            }
        }
        fn valid_farkas_clause(terms: &TermStore, clause: &[TermId]) -> Option<FarkasAnnotation> {
            let annotation = FarkasAnnotation::from_ints(&vec![1; clause.len()]);
            let conflict: Vec<TheoryLit> = clause
                .iter()
                .map(|&literal| match terms.get(literal) {
                    TermData::Not(inner) => TheoryLit::new(*inner, true),
                    _ => TheoryLit::new(literal, false),
                })
                .collect();
            ay_core::proof_validation::verify_farkas_conflict_lits_linear(
                terms,
                &conflict,
                &annotation,
            )
            .is_ok()
            .then_some(annotation)
        }

        #[derive(Clone)]
        struct RewritePlan {
            source: TermId,
            target: TermId,
            clause: Vec<TermId>,
            farkas: FarkasAnnotation,
        }

        // Match every normalized disjunct to exactly one authored disjunct.
        // Exact terms need no theory authority; every changed pair must itself
        // be a checked two-literal arithmetic tautology.
        let mut used = vec![false; raw_args.len()];
        let mut target_sources = Vec::with_capacity(target_args.len());
        let mut rewrites = Vec::new();
        for &target in &target_args {
            if let Some((index, &source)) = raw_args
                .iter()
                .enumerate()
                .find(|(index, source)| !used[*index] && **source == target)
            {
                used[index] = true;
                target_sources.push((target, source));
                continue;
            }
            let mut selected = None;
            for (index, &source) in raw_args.iter().enumerate() {
                if used[index] {
                    continue;
                }
                let not_source = complement(terms, source);
                let clause = vec![not_source, target];
                if let Some(farkas) = valid_farkas_clause(terms, &clause) {
                    selected = Some((
                        index,
                        RewritePlan {
                            source,
                            target,
                            clause,
                            farkas,
                        },
                    ));
                    break;
                }
            }
            let (index, plan) = selected?;
            used[index] = true;
            target_sources.push((target, plan.source));
            rewrites.push(plan);
        }
        if used.iter().any(|used| !*used) {
            return None;
        }

        let source_id = self.add_assumption(quantified, None)?;
        let not_quantified = terms.mk_not_raw(quantified);
        let implication = terms.mk_app(
            Symbol::named("or"),
            [not_quantified, raw_instance],
            Sort::Bool,
        );
        let forall_inst = self.proof.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            Vec::new(),
            values.to_vec(),
        );
        let implication_clause = self.proof.add_rule_step(
            AletheRule::Or,
            vec![not_quantified, raw_instance],
            vec![forall_inst],
            Vec::new(),
        );
        let raw_unit = self.proof.add_resolution(
            vec![raw_instance],
            quantified,
            implication_clause,
            source_id,
        );
        let mut current_clause = raw_args;
        let mut current_id = self.proof.add_rule_step(
            AletheRule::Or,
            current_clause.clone(),
            vec![raw_unit],
            Vec::new(),
        );

        for (target, source) in target_sources {
            if target == source {
                continue;
            }
            let plan = rewrites
                .iter()
                .find(|plan| plan.source == source && plan.target == target)?;
            let lemma = self.add_theory_lemma_with_farkas_and_kind(
                plan.clause.clone(),
                plan.farkas.clone(),
                TheoryLemmaKind::LraFarkas,
            )?;
            let position = current_clause
                .iter()
                .position(|&literal| literal == source)?;
            let _ = current_clause.remove(position);
            if !current_clause.contains(&target) {
                current_clause.push(target);
            }
            current_id =
                self.proof
                    .add_resolution(current_clause.clone(), source, current_id, lemma);
        }
        let mut expected = target_args.clone();
        expected.sort_unstable();
        expected.dedup();
        let mut actual = current_clause.clone();
        actual.sort_unstable();
        actual.dedup();
        if actual != expected {
            return None;
        }

        // Repack the checked flat normalized clause into the exact
        // solver-visible `(or ...)` unit.
        for &target in &target_args {
            let not_target = complement(terms, target);
            let intro = self.proof.add_rule_step(
                AletheRule::OrNeg,
                vec![instance, not_target],
                Vec::new(),
                vec![instance],
            );
            let position = current_clause
                .iter()
                .position(|&literal| literal == target)?;
            let _ = current_clause.remove(position);
            if !current_clause.contains(&instance) {
                current_clause.push(instance);
            }
            current_id =
                self.proof
                    .add_resolution(current_clause.clone(), target, current_id, intro);
        }
        if current_clause != [instance] {
            return None;
        }
        self.lemma_map.or_insert(
            LemmaKey::new(TheoryLemmaKind::Generic, &[instance], None),
            current_id,
        );
        Some(current_id)
    }

    /// Derive one exact ground-integer normalization rewrite from an already
    /// certified source conjunction.
    ///
    /// Every changed conjunct is admitted only when the independent shared
    /// Farkas checker validates either `source => target` directly or
    /// `source ∧ authored_equality => target`. Unchanged conjuncts are reused;
    /// the rewritten conjunction is then introduced with `and_neg` and
    /// resolution. Any unsupported shape fails closed before proof emission.
    pub(crate) fn add_certified_int_rewrite_assertion(
        &mut self,
        terms: &mut TermStore,
        source: TermId,
        target: TermId,
        authored_equalities: &[TermId],
    ) -> Option<ProofId> {
        if !self.enabled || source == target {
            return None;
        }
        let source_id = self
            .lemma_map
            .get(TheoryLemmaKind::Generic, &[source], None)?;
        let TermData::App(Symbol::Named(source_name), source_args) = terms.get(source).clone()
        else {
            return None;
        };
        let TermData::App(Symbol::Named(target_name), target_args) = terms.get(target).clone()
        else {
            return None;
        };
        if source_name != "and"
            || target_name != "and"
            || source_args.len() != target_args.len()
            || source_args.is_empty()
        {
            return None;
        }

        fn complement(terms: &mut TermStore, term: TermId) -> TermId {
            match terms.get(term) {
                TermData::Not(inner) => *inner,
                _ => terms.mk_not_raw(term),
            }
        }
        fn valid_farkas_clause(terms: &TermStore, clause: &[TermId]) -> Option<FarkasAnnotation> {
            let annotation = FarkasAnnotation::from_ints(&vec![1; clause.len()]);
            let conflict: Vec<TheoryLit> = clause
                .iter()
                .map(|&literal| match terms.get(literal) {
                    TermData::Not(inner) => TheoryLit::new(*inner, true),
                    _ => TheoryLit::new(literal, false),
                })
                .collect();
            ay_core::proof_validation::verify_farkas_conflict_lits_linear(
                terms,
                &conflict,
                &annotation,
            )
            .is_ok()
            .then_some(annotation)
        }

        #[derive(Clone)]
        struct RewritePlan {
            source: TermId,
            target: TermId,
            support: Option<TermId>,
            clause: Vec<TermId>,
            farkas: FarkasAnnotation,
        }

        let mut used = vec![false; source_args.len()];
        let mut target_sources = Vec::with_capacity(target_args.len());
        let mut rewrites = Vec::new();
        for &target_arg in &target_args {
            if let Some((index, &source_arg)) = source_args
                .iter()
                .enumerate()
                .find(|(index, source_arg)| !used[*index] && **source_arg == target_arg)
            {
                used[index] = true;
                target_sources.push((target_arg, source_arg));
                continue;
            }

            let mut selected = None;
            for (index, &source_arg) in source_args.iter().enumerate() {
                if used[index] {
                    continue;
                }
                let not_source = complement(terms, source_arg);
                let direct = vec![not_source, target_arg];
                if let Some(farkas) = valid_farkas_clause(terms, &direct) {
                    selected = Some((
                        index,
                        RewritePlan {
                            source: source_arg,
                            target: target_arg,
                            support: None,
                            clause: direct,
                            farkas,
                        },
                    ));
                    break;
                }
                for &support in authored_equalities {
                    let not_support = complement(terms, support);
                    let supported = vec![not_source, not_support, target_arg];
                    if let Some(farkas) = valid_farkas_clause(terms, &supported) {
                        selected = Some((
                            index,
                            RewritePlan {
                                source: source_arg,
                                target: target_arg,
                                support: Some(support),
                                clause: supported,
                                farkas,
                            },
                        ));
                        break;
                    }
                }
                if selected.is_some() {
                    break;
                }
            }
            let (index, plan) = selected?;
            used[index] = true;
            target_sources.push((target_arg, plan.source));
            rewrites.push(plan);
        }
        if used.iter().any(|used| !*used) || rewrites.is_empty() {
            return None;
        }

        let mut source_units: HashMap<TermId, ProofId> = HashMap::default();
        for (index, &source_arg) in source_args.iter().enumerate() {
            let not_source = terms.mk_not_raw(source);
            let projection = self.proof.add_rule_step(
                AletheRule::AndPos(index as u32),
                vec![not_source, source_arg],
                Vec::new(),
                vec![source],
            );
            let unit = self
                .proof
                .add_resolution(vec![source_arg], source, source_id, projection);
            source_units.insert(source_arg, unit);
        }

        let mut target_units: HashMap<TermId, ProofId> = HashMap::default();
        for (target_arg, source_arg) in target_sources {
            if target_arg == source_arg {
                target_units.insert(target_arg, *source_units.get(&source_arg)?);
                continue;
            }
            let plan = rewrites
                .iter()
                .find(|plan| plan.source == source_arg && plan.target == target_arg)?;
            let lemma = self.add_theory_lemma_with_farkas_and_kind(
                plan.clause.clone(),
                plan.farkas.clone(),
                TheoryLemmaKind::LraFarkas,
            )?;
            let mut clause_after_source = plan.clause.clone();
            let source_complement = complement(terms, source_arg);
            let position = clause_after_source
                .iter()
                .position(|&literal| literal == source_complement)?;
            let _ = clause_after_source.remove(position);
            let mut unit = self.proof.add_resolution(
                clause_after_source.clone(),
                source_arg,
                *source_units.get(&source_arg)?,
                lemma,
            );
            if let Some(support) = plan.support {
                let support_id = self.add_assumption(support, None)?;
                let support_complement = complement(terms, support);
                let position = clause_after_source
                    .iter()
                    .position(|&literal| literal == support_complement)?;
                let _ = clause_after_source.remove(position);
                unit = self.proof.add_resolution(
                    clause_after_source.clone(),
                    support,
                    support_id,
                    unit,
                );
            }
            if clause_after_source != [target_arg] {
                return None;
            }
            target_units.insert(target_arg, unit);
        }

        let mut intro_clause = Vec::with_capacity(target_args.len() + 1);
        intro_clause.push(target);
        for &target_arg in &target_args {
            intro_clause.push(complement(terms, target_arg));
        }
        let mut current_id = self.proof.add_rule_step(
            AletheRule::AndNeg,
            intro_clause.clone(),
            Vec::new(),
            vec![target],
        );
        let mut current_clause = intro_clause;
        for &target_arg in &target_args {
            let target_complement = complement(terms, target_arg);
            let position = current_clause
                .iter()
                .position(|&literal| literal == target_complement)?;
            let _ = current_clause.remove(position);
            current_id = self.proof.add_resolution(
                current_clause.clone(),
                target_arg,
                current_id,
                *target_units.get(&target_arg)?,
            );
        }
        if current_clause != [target] {
            return None;
        }
        // As above, ground preprocessing flattens the rewritten conjunction.
        // Preserve the already-checked per-unit derivations across that
        // boundary so no rewritten atom is later introduced as a free Assume.
        for &target_arg in &target_args {
            let unit = *target_units.get(&target_arg)?;
            self.lemma_map.or_insert(
                LemmaKey::new(TheoryLemmaKind::Generic, &[target_arg], None),
                unit,
            );
        }
        self.lemma_map.insert(
            LemmaKey::new(TheoryLemmaKind::Generic, &[target], None),
            current_id,
        );
        Some(current_id)
    }

    /// Take ownership of the accumulated proof and start a coherent new ledger.
    ///
    /// Deduplication maps contain `ProofId`s into `self.proof`.  Retaining them
    /// after moving that proof out leaves dangling IDs: a later solve can
    /// "reuse" a step that exists only in the previously returned proof.  Clear
    /// those maps and zero scope watermarks exactly as for a new proof session.
    pub(crate) fn take_proof(&mut self) -> Proof {
        let proof = std::mem::take(&mut self.proof);
        self.assumption_map.clear();
        self.lemma_map.clear();
        self.clear_scope_ledger_snapshots();
        self.replace_ledger_identity();
        proof
    }

    /// Get the number of proof steps
    #[must_use]
    pub(crate) fn num_steps(&self) -> usize {
        self.proof.len()
    }

    /// Whether a producer has already closed an explicit proof dependency
    /// cone. This is only a cheap prefilter: callers must still run the strict
    /// authored-scope checker before treating the derivation as verdict
    /// authority.
    #[must_use]
    pub(crate) fn has_empty_clause_derivation(&self) -> bool {
        self.proof.steps.iter().any(|step| match step {
            ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. } => {
                clause.is_empty()
            }
            _ => false,
        })
    }

    /// Reset proof content for a new solving session without clearing scope state.
    ///
    /// Used between check-sat calls in incremental mode. Unlike `reset()` (from
    /// `IncrementalSubsystem`), this preserves the scope_stack so that push/pop
    /// incremental scoping remains balanced.
    pub(crate) fn reset_session(&mut self) {
        self.proof = Proof::new();
        self.assumption_map.clear();
        self.lemma_map.clear();
        self.replace_ledger_identity();
        // Scope stack preserved — push/pop balance maintained across check-sat calls.
        // Update watermarks to point into the now-empty proof.
        self.clear_scope_ledger_snapshots();
        // Keep enabled state and theory name
    }
}

impl crate::incremental_state::IncrementalSubsystem for ProofTracker {
    /// Save a scope checkpoint. All proof steps added after this point
    /// will be removed by the matching `pop()`.
    fn push(&mut self) {
        self.scope_stack.push(self.proof.steps.len());
        self.scope_assumption_maps.push(self.assumption_map.clone());
        self.scope_lemma_maps.push(self.lemma_map.clone());
        self.scope_named_steps.push(self.proof.named_steps.clone());
    }

    /// Restore to the last `push()` checkpoint: remove all proof steps,
    /// assumptions, and lemma dedup entries added since then.
    /// Returns false if no matching push exists.
    fn pop(&mut self) -> bool {
        if let Some(watermark) = self.scope_stack.pop() {
            let assumption_map = self.scope_assumption_maps.pop().unwrap_or_default();
            let lemma_map = self.scope_lemma_maps.pop().unwrap_or_default();
            let named_steps = self.scope_named_steps.pop().unwrap_or_default();
            self.proof.steps.truncate(watermark);
            self.assumption_map = assumption_map;
            self.lemma_map = lemma_map;
            self.proof.named_steps = named_steps;
            true
        } else {
            debug_assert!(self.scope_assumption_maps.is_empty());
            debug_assert!(self.scope_lemma_maps.is_empty());
            debug_assert!(self.scope_named_steps.is_empty());
            false
        }
    }

    /// Reset the tracker for a new solving session
    fn reset(&mut self) {
        self.proof = Proof::new();
        self.assumption_map.clear();
        self.lemma_map.clear();
        self.scope_stack.clear();
        self.scope_assumption_maps.clear();
        self.scope_lemma_maps.clear();
        self.scope_named_steps.clear();
        self.replace_ledger_identity();
        // Keep enabled state and theory name
    }
}

impl ProofTracker {
    /// #detour-snapshot-extend: discard the most recent
    /// [`IncrementalSubsystem::push`](crate::incremental_state::IncrementalSubsystem::push)
    /// watermark WITHOUT truncating.
    ///
    /// The UFLIA speculative detour extension brackets its bounded
    /// continuation with a tracker `push()`. If the speculation FAILS the
    /// matching `pop()` removes every proof step / assumption / lemma-dedup
    /// entry the continuation added (so a later phase can never chain
    /// through steps whose terms were rolled back with the term-store
    /// snapshot). If the speculation DECIDES, its steps are part of the
    /// accepted trajectory and must be KEPT — this drops only the watermark,
    /// rebalancing the scope stack. Returns `false` if no watermark exists
    /// (callers treat that as a balanced no-op; the extension always pairs
    /// one `push()` with exactly one `pop()`-or-commit).
    pub(crate) fn commit_speculative_scope(&mut self) -> bool {
        let committed = self.scope_stack.pop().is_some();
        if committed {
            let _ = self.scope_assumption_maps.pop();
            let _ = self.scope_lemma_maps.pop();
            let _ = self.scope_named_steps.pop();
        }
        committed
    }
}
