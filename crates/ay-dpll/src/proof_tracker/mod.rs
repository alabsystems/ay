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

#[cfg(test)]
mod tests;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{
    AletheRule, FarkasAnnotation, Proof, ProofId, Sort, Symbol, TermId, TermStore, TheoryLemmaKind,
    TheoryLit,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct LemmaKey {
    kind: TheoryLemmaKind,
    clause: Vec<TermId>,
    farkas: Option<Vec<(i64, i64)>>,
}

impl LemmaKey {
    fn new(kind: TheoryLemmaKind, clause: &[TermId], farkas: Option<&FarkasAnnotation>) -> Self {
        Self {
            kind,
            clause: clause.to_vec(),
            farkas: farkas.map(|f| {
                f.coefficients
                    .iter()
                    .map(|c| {
                        let mut numer = *c.numer();
                        let mut denom = *c.denom();
                        if denom < 0 {
                            numer = -numer;
                            denom = -denom;
                        }
                        (numer, denom)
                    })
                    .collect()
            }),
        }
    }
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
#[derive(Debug, Default)]
pub(crate) struct ProofTracker {
    /// The accumulated proof
    proof: Proof,
    /// Mapping from assertion term IDs to their proof step IDs
    assumption_map: HashMap<TermId, ProofId>,
    /// Mapping from theory lemma content to proof step IDs
    lemma_map: HashMap<LemmaKey, ProofId>,
    /// Whether proof tracking is enabled
    enabled: bool,
    /// Theory name for the current solving context
    theory_name: String,
    /// Scope stack for incremental push/pop (stores proof step watermarks)
    scope_stack: Vec<usize>,
}

impl ProofTracker {
    /// Create a new proof tracker (disabled by default)
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            proof: Proof::new(),
            assumption_map: HashMap::default(),
            lemma_map: HashMap::default(),
            enabled: false,
            theory_name: "UNKNOWN".to_string(),
            scope_stack: Vec::new(),
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
        let derived_key = LemmaKey::new(TheoryLemmaKind::Generic, &[term], None);
        if let Some(&id) = self.lemma_map.get(&derived_key) {
            self.assumption_map.insert(term, id);
            return Some(id);
        }

        let id = self.proof.add_assume(term, name);
        self.assumption_map.insert(term, id);
        Some(id)
    }

    /// Record a theory lemma (conflict clause from theory solver)
    ///
    /// The clause is the disjunction of literals that the theory solver derived.
    /// Returns the proof step ID for this lemma, or None if tracking is disabled.
    pub(crate) fn add_theory_lemma(&mut self, clause: Vec<TermId>) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }

        let key = LemmaKey::new(TheoryLemmaKind::Generic, &clause, None);

        // Check if we already have this lemma
        if let Some(&id) = self.lemma_map.get(&key) {
            return Some(id);
        }

        let id = self.proof.add_theory_lemma(&self.theory_name, clause);
        self.lemma_map.insert(key, id);
        Some(id)
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
        let key = LemmaKey::new(kind, &clause, None);
        if let Some(&id) = self.lemma_map.get(&key) {
            return Some(id);
        }

        let id = self
            .proof
            .add_theory_lemma_with_kind(&self.theory_name, clause, kind);
        self.lemma_map.insert(key, id);
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

        let key = LemmaKey::new(kind, &clause, Some(&farkas));
        if let Some(&id) = self.lemma_map.get(&key) {
            return Some(id);
        }

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

        let key = LemmaKey::new(TheoryLemmaKind::Generic, &clause, None);
        if let Some(&id) = self.lemma_map.get(&key) {
            return Some(id);
        }

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
            disjunct_complements.push((disjunct, disjunct_complement));
            match terms.get(disjunct_complement) {
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    final_units.extend(args.iter().copied());
                }
                _ => final_units.push(disjunct_complement),
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
        for (_disjunct, disjunct_complement) in disjunct_complements {
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
            if let TermData::App(Symbol::Named(name), nested) =
                terms.get(disjunct_complement).clone()
            {
                if name == "and" {
                    for (index, arg) in nested.into_iter().enumerate() {
                        let not_conjunction = terms.mk_not_raw(disjunct_complement);
                        let projection = self.proof.add_rule_step(
                            AletheRule::AndPos(index as u32),
                            vec![not_conjunction, arg],
                            Vec::new(),
                            vec![disjunct_complement],
                        );
                        let projected = self.proof.add_resolution(
                            vec![arg],
                            disjunct_complement,
                            unit,
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

        self.lemma_map.insert(
            LemmaKey::new(TheoryLemmaKind::Generic, &[skolemized_body], None),
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
        let source_key = LemmaKey::new(TheoryLemmaKind::Generic, &[source], None);
        let source_id = *self.lemma_map.get(&source_key)?;
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
            ay_core::proof_validation::verify_farkas_conflict_lits_full(
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
        self.lemma_map.insert(
            LemmaKey::new(TheoryLemmaKind::Generic, &[target], None),
            current_id,
        );
        Some(current_id)
    }

    /// Take ownership of the accumulated proof
    pub(crate) fn take_proof(&mut self) -> Proof {
        std::mem::take(&mut self.proof)
    }

    /// Get the number of proof steps
    #[must_use]
    pub(crate) fn num_steps(&self) -> usize {
        self.proof.len()
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
        // Scope stack preserved — push/pop balance maintained across check-sat calls.
        // Update watermarks to point into the now-empty proof.
        self.scope_stack.fill(0);
        // Keep enabled state and theory name
    }
}

impl crate::incremental_state::IncrementalSubsystem for ProofTracker {
    /// Save a scope checkpoint. All proof steps added after this point
    /// will be removed by the matching `pop()`.
    fn push(&mut self) {
        self.scope_stack.push(self.proof.steps.len());
    }

    /// Restore to the last `push()` checkpoint: remove all proof steps,
    /// assumptions, and lemma dedup entries added since then.
    /// Returns false if no matching push exists.
    fn pop(&mut self) -> bool {
        if let Some(watermark) = self.scope_stack.pop() {
            self.proof.steps.truncate(watermark);
            // Remove map entries whose ProofId points beyond the watermark
            let cutoff = watermark as u32;
            self.assumption_map.retain(|_, id| id.0 < cutoff);
            self.lemma_map.retain(|_, id| id.0 < cutoff);
            self.proof.named_steps.retain(|_, id| id.0 < cutoff);
            true
        } else {
            false
        }
    }

    /// Reset the tracker for a new solving session
    fn reset(&mut self) {
        self.proof = Proof::new();
        self.assumption_map.clear();
        self.lemma_map.clear();
        self.scope_stack.clear();
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
        self.scope_stack.pop().is_some()
    }
}
