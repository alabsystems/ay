// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier processing pipeline for check-sat-internal.
//!
//! Orchestrates E-matching (multi-round with chaining), CEGQI (counterexample-guided
//! quantifier instantiation), promote-unsat optimization, CEGQI result mapping,
//! arithmetic refinement, and logic-category dispatch.
//!
//! Submodules:
//! - `preprocess`: finite-domain expansion, Skolemization, E-matching rounds,
//!   instance filtering, promote-unsat, CEGQI setup, assertion flattening.
//! - `result_mapping`: CEGQI/E-matching result interpretation and assertion restore.
//! - `cegqi_refinement`: multi-round arithmetic refinement and neighbor enumeration.
//! - `dispatch`: logic-category re-solve dispatch and interleaved E-matching.

mod cegqi_refinement;
mod dispatch;
mod entailed_consts;
pub(crate) mod family_classifier;
mod preprocess;
// Untrusted projection proposal plus independent semantic/source checking.
// This module cannot emit SAT: its opaque result must still be consumed with
// an authored-query permit at the sealed SAT authority boundary.
pub(in crate::executor) mod projection_candidate;
pub(in crate::executor) mod result_mapping;

use ay_core::{Sort, TermData, TermId, TermStore};

pub(in crate::executor) use cegqi_refinement::unsupported_arith_mentions_ce_var;
pub(in crate::executor) use family_classifier::write_family_class_statistics;
pub(in crate::executor) use result_mapping::CegqiUfRecompletionGrant;

use super::{Executor, QuantExpansionRecord};
use crate::cegqi::CegqiInstantiator;
use crate::ematching::{collect_quantifiers, contains_quantifier};
use crate::quantifier_manager::QuantifierManager;

/// Sorts whose values MBQI cannot synthesize and where partial E-matching
/// provides no soundness guarantee for universal quantifiers.
///
/// When a `forall` binds a variable of such a sort, the only sound ways to
/// discharge it are:
///
///   * finite-domain expansion (only applies to Bool / small BV / bounded Int)
///   * CEGQI arithmetic refinement (only applies to Int/Real binders)
///   * interleaved E-matching that drives the formula to UNSAT
///
/// If none of those apply, any SAT produced after stripping the quantifier is
/// unsound — the ground solver may satisfy a narrow set of E-matched instances
/// while missing semantically required ones (Z3 #6303 / ay #8729).
///
/// Matches the "unsupported" sorts in
/// [`super::super::mbqi::Executor::synthesize_mbqi_candidates`] — Array, FP,
/// Seq, Datatype, RegLan.
fn is_mbqi_unsafe_binder_sort(sort: &Sort) -> bool {
    matches!(
        sort,
        Sort::Array(_)
            | Sort::FloatingPoint(_, _)
            | Sort::Seq(_)
            | Sort::RegLan
            | Sort::Datatype(_)
    )
}

/// Return `true` if the term is a `forall` whose binders include any sort
/// MBQI cannot soundly synthesize (see `is_mbqi_unsafe_binder_sort`).
///
/// Existentials are excluded: positive-polarity existentials are Skolemized
/// to fresh constants before quantifier preprocessing, and any remaining
/// exists under negation behaves like a forall after negation-normal form.
fn forall_has_unsafe_binder(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Forall(vars, body, _) => {
            vars.iter().any(|(_, s)| is_mbqi_unsafe_binder_sort(s))
                || forall_indexes_array_at_binder(terms, vars, *body)
        }
        _ => false,
    }
}

/// Return `true` if `index` is, or structurally contains, a use of one of the
/// `bound` variable names.
///
/// Name-based and intentionally scope-insensitive: a shadowing inner binder of
/// the same name can only make this over-approximate, and over-flagging an
/// MBQI-unsafe `forall` costs completeness (a `Sat` degrades to `Unknown`),
/// never soundness.
fn index_mentions_bound_var(terms: &TermStore, index: TermId, bound: &[String]) -> bool {
    use ay_core::kani_compat::DetHashSet as HashSet;
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack = vec![index];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(name, _) if bound.iter().any(|b| b == name) => return true,
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*body);
            }
            _ => {}
        }
    }
    false
}

/// Return `true` if `body` reads or writes an array (`select` / `store`) at an
/// index that depends on one of `vars` (this `forall`'s binders).
///
/// Such a `forall` constrains an array's contents across its entire (infinite)
/// index domain. E-matching only instantiates indices that already occur ground
/// in the problem, and MBQI synthesis enumerates only ground index terms, so the
/// witness index forced by an array *disequality* elsewhere
/// (`a ≠ b` ⇒ ∃k. a[k] ≠ b[k]) is never instantiated. A ground `Sat` can
/// therefore violate the quantifier at that missing witness — array
/// extensionality (the ay AUFLIA / Z3 #6303 / ay #8729 family). The binder's own
/// sort is typically `Int`, so [`is_mbqi_unsafe_binder_sort`] does not catch this
/// shape; what makes MBQI unsound here is that the binder *indexes* an array.
/// Treat as MBQI-unsafe so the [`result_mapping`] soundness gate degrades the
/// ground `Sat` to `Unknown` (never to a wrong `sat`/`unsat`).
fn forall_indexes_array_at_binder(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
) -> bool {
    use ay_core::kani_compat::DetHashSet as HashSet;
    let bound: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack = vec![body];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        // `(select A i)` — args = [array, index]; `(store A i v)` — args = [array, index, value].
        if let Some(args) = app_args(terms, t, "select") {
            if args.len() == 2 && index_mentions_bound_var(terms, args[1], &bound) {
                return true;
            }
        }
        if let Some(args) = app_args(terms, t, "store") {
            if args.len() == 3 && index_mentions_bound_var(terms, args[1], &bound) {
                return true;
            }
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Let(bindings, b) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            _ => {}
        }
    }
    false
}

/// Walk `term` and return `true` if any sub-formula is a `forall` with an
/// MBQI-unsafe binder. Uses a small visited set to avoid traversing shared
/// subterms (hash-consed assertions DAG).
pub(super) fn contains_forall_with_unsafe_binder(terms: &TermStore, term: TermId) -> bool {
    use ay_core::kani_compat::DetHashSet as HashSet;
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        if forall_has_unsafe_binder(terms, t) {
            return true;
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*body);
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => {}
        }
    }
    false
}

fn assertions_have_direct_boolean_conflict(terms: &TermStore, assertions: &[TermId]) -> bool {
    use ay_core::kani_compat::DetHashSet as HashSet;

    let false_term = terms.false_term();
    let mut positives = HashSet::default();
    let mut negatives = HashSet::default();

    for &assertion in assertions {
        if assertion == false_term {
            return true;
        }
        if let TermData::Not(inner) = terms.get(assertion) {
            if positives.contains(inner) {
                return true;
            }
            negatives.insert(*inner);
        } else {
            if negatives.contains(&assertion) {
                return true;
            }
            positives.insert(assertion);
        }
    }

    false
}

/// Exact preprocessing snapshot retained when canonical finite-domain
/// expansion removes every quantifier before E-matching starts.
///
/// The records are producer provenance, not SAT authority. Result mapping must
/// still replay the canonical expander, prove complete coverage of the authored
/// quantified roots, validate the retained model against `expanded_assertions`,
/// and bind any grant to that exact model.
pub(in crate::executor) struct ExactFiniteExpansionEvidence {
    pub(super) expanded_assertions: Box<[TermId]>,
    pub(super) records: Box<[QuantExpansionRecord]>,
}

/// Result of quantifier preprocessing: flags consumed by `map_quantifier_result`.
pub(in crate::executor) struct QuantifierProcessingResult {
    /// Whether any quantifiers had no E-matching instantiations.
    pub has_uninstantiated_quantifiers: bool,
    /// Whether E-matching hit its round or per-round budget.
    pub reached_instantiation_limit: bool,
    /// Whether deferred instantiations remain.
    pub has_deferred: bool,
    /// Whether CEGQI handled at least one forall quantifier.
    pub cegqi_has_forall: bool,
    /// Whether CEGQI handled at least one exists quantifier.
    pub cegqi_has_exists: bool,
    /// Whether E-matching added any new ground instantiations.
    pub ematching_added_instantiations: bool,
    /// Assertion snapshot after finite-domain expansion and Skolemization but
    /// before stripping quantified formulas. Interleaved refinement should use
    /// this preprocessed view instead of reintroducing the original shapes.
    pub refinement_assertions: Option<Vec<TermId>>,
    /// CE lemma TermIds added by CEGQI, tracked by ID for position-independent
    /// filtering. Refinement rounds push ground instantiations after CE lemmas,
    /// so positional slicing from the end is incorrect (#5975 offset bug).
    pub cegqi_ce_lemma_ids: Vec<TermId>,
    /// Per-universal CE-conjunct groups (#cegqi-per-universal): for each
    /// CEGQI-handled quantifier, the surviving AND-conjuncts of ITS CE lemma —
    /// the sound unit for the disambiguation SAT flip's refutation.
    pub cegqi_ce_lemma_groups: Vec<(TermId, Vec<TermId>)>,
    /// Whether any quantifiers are completely unhandled (neither E-matching nor CEGQI).
    pub has_completely_unhandled_quantifiers: bool,
    /// Quantifiers not handled by either E-matching or CEGQI (#5971).
    /// Passed to MBQI for model-based counterexample checking.
    pub unhandled_quantifiers: Vec<TermId>,
    /// Whether E-matching processed any exists quantifiers (#3593).
    /// When true, UNSAT results are unreliable because E-matching adds exists
    /// instances as conjunctive assertions (all must hold), but exists semantics
    /// require a disjunction (at least one must hold).
    pub ematching_has_exists: bool,
    /// Number of E-matching rounds completed (#8614).
    pub ematching_rounds_completed: u64,
    /// Number of quantifier instances created by E-matching (#8614).
    pub ematching_instances_created: u64,
    /// Original assertions snapshot (before E-matching modifications).
    /// `Some` when quantifiers were present; used to restore assertions after solving.
    pub original_assertions: Option<Vec<TermId>>,
    /// Canonical finite-expansion provenance for the early fully-ground exit.
    /// Kept separate from `original_assertions`: restoration state alone is
    /// never evidence that an expansion was exact or exhaustive.
    pub exact_finite_expansion: Option<ExactFiniteExpansionEvidence>,
    /// CEGQI state for refinement: (quantifier_id, instantiator) pairs.
    /// Used by `map_quantifier_result` to compute model-based instantiations
    /// when the CE lemma yields SAT (counterexample found).
    pub cegqi_state: Vec<(TermId, CegqiInstantiator)>,
    /// Any original assertion contains a `forall` whose binder sort MBQI
    /// cannot synthesize (Array, FP, Seq, RegLan). SAT results for such
    /// problems are unsound unless CEGQI refinement already forced UNSAT,
    /// because the ground solver only sees a finite set of E-matched
    /// instances of an infinite-domain quantifier (ay #8729, Z3 #6303).
    pub has_unsafe_partial_quantifiers: bool,
    /// True when every collected universal quantifier is a syntactic
    /// UF-completion candidate.
    ///
    /// This is only a refinement hint. It is not SAT authority: the classifier
    /// does not construct one shared interpretation for all accepted atoms, and
    /// E-matching having produced an instance is not domain coverage.
    pub quantifiers_supported_by_uf_completion: bool,
}

impl QuantifierProcessingResult {
    /// Create a no-op result for the case when no quantifiers are present.
    pub(super) fn no_quantifiers() -> Self {
        Self {
            has_uninstantiated_quantifiers: false,
            reached_instantiation_limit: false,
            has_deferred: false,
            cegqi_has_forall: false,
            cegqi_has_exists: false,
            ematching_added_instantiations: false,
            refinement_assertions: None,
            cegqi_ce_lemma_ids: Vec::new(),
            cegqi_ce_lemma_groups: Vec::new(),
            has_completely_unhandled_quantifiers: false,
            unhandled_quantifiers: Vec::new(),
            ematching_has_exists: false,
            ematching_rounds_completed: 0,
            ematching_instances_created: 0,
            original_assertions: None,
            exact_finite_expansion: None,
            cegqi_state: Vec::new(),
            has_unsafe_partial_quantifiers: false,
            quantifiers_supported_by_uf_completion: false,
        }
    }

    /// Preserve the exact before/after expansion relation when preprocessing
    /// has made the solve entirely ground. Returning `no_quantifiers()` here
    /// used to discard both the authored roots and their authenticated
    /// `QuantExpansionRecord`s, so restoration could only fail closed after a
    /// valid ground SAT.
    fn fully_expanded(
        original_assertions: Vec<TermId>,
        expanded_assertions: Vec<TermId>,
        records: Vec<QuantExpansionRecord>,
    ) -> Self {
        let exact_finite_expansion = (!records.is_empty()).then(|| ExactFiniteExpansionEvidence {
            expanded_assertions: expanded_assertions.clone().into_boxed_slice(),
            records: records.into_boxed_slice(),
        });
        let mut result = Self::no_quantifiers();
        result.refinement_assertions = Some(expanded_assertions);
        result.original_assertions = Some(original_assertions);
        result.exact_finite_expansion = exact_finite_expansion;
        result
    }
}

impl Executor {
    /// Return `true` if any assertion contains a `forall` whose binder ranges
    /// over a user-declared datatype.
    ///
    /// SOUNDNESS (#enum-forall): `declare-datatype E ((R) (S))` surfaces `E` as
    /// `Sort::Uninterpreted("E")`, so the syntactic
    /// [`is_mbqi_unsafe_binder_sort`] check (which matches `Sort::Datatype(_)`)
    /// never fires for it. But MBQI cannot synthesize datatype-sorted witnesses
    /// (`synthesize_mbqi_candidates` produces no candidates for datatypes), and
    /// finite-domain expansion does not enumerate constructors, so stripping the
    /// `forall` and accepting the ground SAT is unsound — e.g.
    /// `(forall (c E) (= c R))` over `E = {R, S}` is UNSAT (`S != R` by
    /// constructor distinctness) and `(forall (p P) (= (f p) 0))` over a struct
    /// `P` is UNSAT (some `p` has `(f p) != 0`), yet both were reported `sat`.
    /// Flag such a `forall` as MBQI-unsafe so the [`result_mapping`] soundness
    /// gate degrades the ground SAT to `unknown`.
    fn assertions_have_forall_over_datatype(&self) -> bool {
        self.ctx
            .assertions
            .iter()
            .any(|&a| self.forall_binds_datatype(a))
    }

    /// Walk `term` and return `true` if any `forall` binds a variable whose sort
    /// is a user-declared datatype (per [`Self::binder_sort_is_datatype`]).
    fn forall_binds_datatype(&self, term: TermId) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let terms = &self.ctx.terms;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match terms.get(t) {
                TermData::Forall(vars, body, _) => {
                    if vars.iter().any(|(_, s)| self.binder_sort_is_datatype(s)) {
                        return true;
                    }
                    stack.push(*body);
                }
                TermData::Exists(_, body, _) => stack.push(*body),
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => {}
            }
        }
        false
    }

    /// Run quantifier preprocessing: E-matching, CEGQI, promote-unsat, assertion filtering.
    ///
    /// Returns a [`QuantifierProcessingResult`] with flags for result mapping and the
    /// original assertion snapshot for restoration after solving.
    ///
    /// This modifies `self.ctx.assertions` in place: E-matching instantiations are added,
    /// CEGQI CE lemmas are appended, and quantified formulas are stripped. The original
    /// assertions are saved in the result for post-solve restoration.
    pub(in crate::executor) fn process_quantifiers(&mut self) -> QuantifierProcessingResult {
        // Reset the per-check-sat conflict-verification support set. It is
        // rebuilt below from THIS solve's e-matching so a stale root from a
        // prior check-sat (whose source Forall may since have been popped, or
        // whose instance was retracted by restore_assertions) can never be
        // threaded — preserving the "true in every model of the CURRENT problem"
        // invariant. Empty when no unconditional-Forall instances are produced.
        self.active_support_axioms.clear();
        // The conflict-verification verdict memo (#4535) is keyed against the
        // support set — rebuild of the support set invalidates it.
        self.conflict_semantic_verify_memo.clear();
        // The propagation-verification memo (#verify-memo) does not read the
        // support set, but clearing on the same boundary keeps one lifecycle
        // contract for both verify-lane memos (conservative, never unsound).
        self.prop_semantic_verify_memo.clear();

        // 1. Early exit if no quantifiers present.
        // contains_quantifier uses memoization (visited set) to avoid
        // exponential re-traversal on DAG-structured terms.
        let has_quantifiers = self
            .ctx
            .assertions
            .iter()
            .any(|&a| contains_quantifier(&self.ctx.terms, a));
        if !has_quantifiers {
            return QuantifierProcessingResult::no_quantifiers();
        }

        // Freeze proof authority before ANY semantic preprocessing. The
        // post-merge snapshot below is only solver-state restoration data;
        // merged binder towers, finite-domain expansions, Skolem bodies, and
        // every later replacement must be derived rather than whitelisted as
        // authored Assumes.
        if self.produce_proofs_enabled() {
            let authored_assertions = self.ctx.assertions.clone();
            self.install_proof_source_provenance(&authored_assertions);
        }

        // (#choose-synth-watermark) Fix the ORIGINAL-problem term boundary before
        // ANY witness synthesis (Skolemization, add_diagonal, MBQI/CEGQI model
        // values) runs below. Idempotent, so on the first quantifier-bearing solve
        // it records exactly the pre-synthesis term count; every later `mk_*` (an
        // invented witness like `f2(-1,0)` over an LIA model value) gets a strictly
        // greater id. Only the `no_mbqi` Hilbert-`choose` E-match guard consults it,
        // to refuse discharging the choose existential from a synthesized witness.
        self.ctx.terms.set_synthesis_watermark();

        // 1b. (#p2-nested-forall) Merge directly nested same-polarity binder
        // towers (`∀x.∀y.B ⇒ ∀x,y.B`, alpha-renamed) BEFORE the
        // original_assertions snapshot, so every downstream snapshot /
        // CE-lemma / support-axiom artifact sees one consistent flattened
        // term. Detect-before-mint: byte-identical no-op on non-tower inputs.
        self.merge_adjacent_universals();

        // 2. Snapshot assertions for post-solve restoration (#2844).
        let original_assertions = Some(self.ctx.assertions.clone());

        // Detect universal quantifiers whose binders include sorts MBQI
        // cannot synthesize (Array, FP, Seq, RegLan). These require either
        // finite-domain expansion, CEGQI arithmetic refinement, or E-matching
        // driving UNSAT to be handled soundly. The check runs on the original
        // assertion set (before finite-domain expansion / Skolemization) so it
        // captures the original `forall` shapes (ay #8729 / Z3 #6303).
        let has_unsafe_partial_quantifiers = self
            .ctx
            .assertions
            .iter()
            .any(|&a| contains_forall_with_unsafe_binder(&self.ctx.terms, a))
            || self.assertions_have_forall_over_datatype();

        // 3. Finite-domain expansion + Skolemization. Re-check for remaining quantifiers.
        self.expand_finite_domains();
        self.skolemize_existentials();

        // (#forall-goal-boundary) Tighten GROUND integer strict bounds `(< s t)` to
        // the equivalent non-strict `(<= s (- t 1))`. Runs AFTER Skolemization, so a
        // negated forall-GOAL `(not (forall i. (and (<= 0 i) (< i (+ len 1))) P))` —
        // whose discharge skolemizes the existential witness `k` with the ground
        // boundary atom `(< k (+ len 1))` — now carries `(<= k len)` instead. That
        // non-strict upper bound lets the LIA solver EXPORT the implied equality
        // `k = len` to the congruence closure on the boundary branch (`k >= len`),
        // closing the new-element case of the per-element invariant
        // `forall i. i < db.len() ==> entailed(db[i])` maintained across a push (the
        // boundary index `k == len` reads the just-appended element). Without it,
        // the rational-style strict bound `k < len+1` admits `k ∈ [len, len+1)` and
        // never pins `k = len`, leaving the goal Unknown/Sat.
        //
        // SOUNDNESS: `(< s t) ≡ (<= s (t-1))` is an exact equivalence over the
        // integers (true under both polarities), so the model set is unchanged — a
        // valid (unsat) goal stays unsat and an invalid one stays sat; it can never
        // manufacture a false equality nor a false UNSAT. It only NORMALIZES an
        // atom so the existing (sound) non-strict implied-equality export fires.
        // ADDITIVE / minimal blast radius: it does NOT descend into surviving
        // `forall`/`exists` bodies, so trigger selection and E-matching of the
        // assumed invariant are byte-identical; only ground atoms (incl. the
        // skolemized goal bound) are touched. Gated to the quantifier path
        // (`process_quantifiers` only runs when quantifiers are present).
        self.tighten_ground_int_strict_bounds();

        // (F6 bv2nat/int2bv bridge) Propagate asserted ground CONSTANT pins across
        // the BV<->Int boundary: fold `int2bv`/`bv2nat` over now-constant args,
        // collapse pure-Int goal disjuncts, and materialize the entailed
        // `bv2nat(x)=n ⇒ x=int2bv_w(n)` inversion pins. Reduces a fixed-length
        // seq-concat / frame obligation whose lengths are threaded through the
        // bridge to the pure array/BV shape the decision procedure refutes (probe
        // M1/M1d). Sound (asserted-equality substitution + entailed tautologies),
        // gated to bridge-bearing problems, and — like the strict-bound tightening
        // above — never descends into surviving quantifier bodies, so triggers and
        // e-matching stay byte-identical.
        self.propagate_bridge_ground_values();

        // (#quant-diagonal) Add diagonal (all-bound-vars-equal) instances of multi-var
        // same-sort universals, so the EPR/UF self-pair refutation (Class B false-SAT,
        // e.g. `(X0:=d, X1:=d)`) is not missed by trigger-only e-matching. Cheap
        // (k per forall, not k^n).
        //
        // (#p2-diag-position) SOUNDNESS: candidates come from the polarity-aware
        // `collect_entailed_foralls` — ONLY universals entailed as NNF conjuncts
        // of an assertion (top-level / under `and` / negated exists / negated
        // implication premises). The previous collector (`collect_quantifiers`)
        // flattened through `or`/`ite` WITHOUT polarity and surfaced foralls that
        // are mere disjuncts; conjoining their diagonal instances manufactured
        // ground conflicts and produced wrong `unsat` on trivially-SAT formulas
        // (`(or c (forall x y. p x y)) ∧ ¬p(0,0)` — probes a12/t1–t3/u2/x4;
        // widened by merge_adjacent_universals turning 1-var towers under
        // or/ite into multi-var diagonal victims). An instance of an ENTAILED
        // universal is a consequence in every model, so this pass now only ever
        // adds consequences — it can refute, never wrongly refute.
        let diag_snapshot = self.ctx.assertions.clone();
        let mut diag_quants: Vec<TermId> = Vec::new();
        for &a in &diag_snapshot {
            preprocess::collect_entailed_foralls(&mut self.ctx.terms, a, true, &mut diag_quants);
        }
        self.add_diagonal_forall_instances(&diag_quants);

        let still_has_quantifiers = self
            .ctx
            .assertions
            .iter()
            .any(|&a| contains_quantifier(&self.ctx.terms, a));
        if !still_has_quantifiers {
            // Finite-domain expansion / Skolemization already fully eliminated
            // all quantifiers. Preserve the exact before/after relation and its
            // producer records: the mapper may consume them only after an
            // independent canonical replay and an exact-model validation.
            if let Some(original_assertions) = original_assertions {
                return QuantifierProcessingResult::fully_expanded(
                    original_assertions,
                    self.ctx.assertions.clone(),
                    self.quant_expansion_records.clone(),
                );
            }
            // Defensive fail-closed fallback for an impossible state: without
            // the authored snapshot the ground replacement must not be treated
            // as public restoration or SAT evidence.
            return QuantifierProcessingResult::no_quantifiers();
        }
        // #read-congruence-quantified-scope (#7956 tseitin regression): the
        // instantiation pipeline is engaged for this check-sat call — the
        // ground solve and every interleaved/classification re-solve that
        // follows runs over E-matched instances. Ground combiners built while
        // this is set disable the store-carrying read-congruence index-pair
        // obligations (see `TheoryCombiner::set_read_congruence_pairs_enabled`);
        // re-armed to `false` per call in `install_timeout_deadline_for_call`.
        self.quantifier_pipeline_engaged = true;
        // Recompute unsafe-binder flag over the post-expansion assertions so
        // finite-domain expansion and Skolemization that eliminated a
        // previously-unsafe quantifier are reflected.
        let has_unsafe_partial_quantifiers = has_unsafe_partial_quantifiers
            && (self
                .ctx
                .assertions
                .iter()
                .any(|&a| contains_forall_with_unsafe_binder(&self.ctx.terms, a))
                || self.assertions_have_forall_over_datatype());
        let refinement_assertions = Some(self.ctx.assertions.clone());

        // 4. E-matching rounds.
        self.set_active_solve_phase("quantifier-ematching", "ematching");
        let mut ematching = self.run_ematching_rounds();

        // 4b. (#recdt) Fold datatype selector-over-constructor applications in the
        //     E-matched instances. `instantiate_body` builds instances by raw
        //     substitution and — unlike the elaborator, which folds
        //     `sel_i(C(t..)) -> t_i` on user-written terms — leaves a
        //     recursive-datatype defining-axiom instance at a constructor term
        //     (`sum(tl(Cons(a,r)))`) with its selector-over-constructor UNREDUCED.
        //     The combined DT+LIA iterative-deepening final-check then unrolls the
        //     recursive selector frontier one level deeper each round and diverges,
        //     even though the reduced instance (`sum(r)`) discharges the goal
        //     immediately. Applying the same exact, semantics-preserving fold here
        //     yields the parser's ground shape, which the DT+LIA solver decides in
        //     milliseconds. Fold BOTH the instantiation list and the sound
        //     conflict-verification support subset with the same rewrite so the
        //     support-axiom tags continue to reference terms actually asserted.
        self.reduce_dt_selectors_in_ematching(&mut ematching);

        // Proof-producing solves must assert the same raw structural instance
        // that the strict `forall_inst` checker reconstructs.  Keep the search
        // result, support roots, and provenance records term-identical before
        // registration or assertion filtering observes them.
        self.materialize_exact_ematching_instances(
            &mut ematching.instantiations,
            &mut ematching.unconditional_forall_roots,
            &mut ematching.unconditional_forall_instantiations,
        );

        // 5. Add E-matching instances (duplicate + model-satisfied filtering).
        //    Records the sound support-axiom subset into `active_support_axioms`.
        //    For MBQI-unsafe partial quantifiers (e.g. an array-indexing frame
        //    invariant) the presolve model that Phase C filters against is not a
        //    model of the quantified problem, so a "satisfied" instance can hinge
        //    on a defaulted, not-yet-constrained ground term; dropping it loses a
        //    genuine constraint and turns a decided verdict into `Unknown`
        //    (#stale-presolve-frame-skip). Suppress that skip for such problems —
        //    adding every sound E-matched instance can only recover completeness.
        self.register_ematching_proof_provenance(&ematching.unconditional_forall_instantiations);
        let ematching_added = self.add_ematching_instances(
            ematching.instantiations,
            &ematching.unconditional_forall_roots,
            has_unsafe_partial_quantifiers,
        );
        // 5b. #entailed-bound-expansion. A `forall` whose Int binder is guarded by
        //     a ground TERM — `(< i (seq_len vec))` — reads as UNBOUNDED to
        //     `expand_finite_domains`, which only accepts a literal bound, so it
        //     falls through to lazy instantiation and the term set grows without
        //     bound. Often the problem ENTAILS the bound: here `seq_len vec = 1`
        //     (= len(concat(singleton(v), seq_empty)) = 1 + 0), which makes the
        //     quantifier a ONE-element conjunction.
        //
        //     The bound is DERIVED, never solved for and never read off a model:
        //     `derive_entailed_int_consts` is unit propagation + congruence closure
        //     + LIA constant folding over the quantifier-free consequences. It takes
        //     `&TermStore`, so it is STRUCTURALLY INCAPABLE of minting a term — the
        //     whole reason it cannot perturb the solve. (A nested Executor solve
        //     here is poison: measured pushing the ext_eq push/pop SAT check
        //     4.3s -> 33.7s and the tseitin fixture to a timeout.)
        //
        //     It runs HERE, after `add_ematching_instances`, because the derivation
        //     genuinely needs one instance: the ground assertions ALONE do not entail
        //     the bound (measured: SAT with the bound negated), but they do once the
        //     concat-length axiom's instance at the already-ground
        //     `(seq_concat (seq_singleton v) seq_empty)` is present.
        //
        //     ORDER IS LOAD-BEARING. Steps 1-2 are strictly READ-ONLY. The soundness
        //     GATE is evaluated LAST, because `snapshot_has_nonconjunctive_forall`
        //     -> `collect_quantifiers` takes `&mut TermStore` and MINTS the NNF-dual
        //     quantifier terms (measured: 5), shifting every later TermId. Calling it
        //     eagerly perturbs problems that never fire — measured taking tseitin
        //     14.7s -> 90s TIMEOUT and pp 4.4s -> 10-12s even though `unlocks` was
        //     false for both. Deferring it behind `unlocks` keeps every non-firing
        //     problem byte-identical to baseline.
        {
            let snap = self.ctx.assertions.clone();
            // 1. Derive entailed constants (read-only, solve-free).
            let consts = entailed_consts::derive_entailed_int_consts(&self.ctx.terms, &snap);
            // 2. Would any of them actually unlock a bounded-Int forall? (read-only)
            let unlocks = !consts.is_empty()
                && crate::skolemize::derived_bound_unlocks_expansion(
                    &self.ctx.terms,
                    &snap,
                    &consts,
                );
            if unlocks {
                // 3. SOUNDNESS GATE (mints terms; reached only when we will act).
                //    THIS IS THE LOAD-BEARING SOUNDNESS CHECK — not the deriver.
                //    `derive_entailed_int_consts` walks the POST-E-MATCHING
                //    assertions, which contain instances of quantifiers; an
                //    instance of a `forall` in a DISJUNCTIVE obligation is NOT a
                //    consequence, so the deriver CAN and DOES emit non-entailed
                //    constants (adversarial review measured `(or r (forall j.
                //    f(j)=9))` producing `n=9` on a SAT problem). Rewriting with
                //    such a constant is a false UNSAT. We block that here: act ONLY
                //    when every ORIGINAL `forall` is in a (unit-aware) conjunctive
                //    position, so every instance IS a consequence (universal
                //    instantiation) and the derived constants are genuinely
                //    entailed. Removing this gate reintroduces the false UNSAT —
                //    verified by disabling it (the SAT case above then goes UNSAT).
                let orig = original_assertions.clone().unwrap_or_default();
                if !self.snapshot_has_nonconjunctive_forall_probe(&orig) {
                    // The derived table is live for EXACTLY this one expansion call.
                    // Its RAII owner restores the predecessor on return or unwind. It
                    // must never be visible to a nested sub-solve: those run on a
                    // SUBSET of the assertions, which need not entail these constants,
                    // so folding them in there would not be equals-for-equals.
                    let _derived_scope = crate::skolemize::scoped_derived_consts(consts);
                    self.expand_finite_domains();
                }
            }
        }

        // 6. Promote-unsat: promote conflict-producing deferred instantiations.
        self.set_active_solve_phase("quantifier-promote-deferred", "deferred-instantiation");
        let _promoted = self.promote_deferred_conflicts();

        // 7. Check remaining deferred state.
        let deferred_exists = self
            .quantifier_manager
            .as_ref()
            .is_some_and(QuantifierManager::has_deferred);

        // 8. Collect the remaining quantifiers.
        let mut quantifiers: Vec<TermId> = Vec::new();
        for assertion in self.ctx.assertions.clone() {
            collect_quantifiers(&mut self.ctx.terms, assertion, &mut quantifiers);
        }
        quantifiers.sort_unstable_by_key(|term| term.index());
        quantifiers.dedup();

        let forall_quantifiers: Vec<TermId> = quantifiers
            .iter()
            .copied()
            .filter(|&q| matches!(self.ctx.terms.get(q), TermData::Forall(..)))
            .collect();
        let refinement_assertions_slice = refinement_assertions
            .as_ref()
            .map_or(&[][..], Vec::as_slice);
        let ground_assertions: Vec<TermId> = refinement_assertions_slice
            .iter()
            .copied()
            .filter(|&a| !contains_quantifier(&self.ctx.terms, a))
            .collect();
        let ground_assertions_supported_by_uf_completion = ground_assertions
            .iter()
            .copied()
            .all(|a| self.quantifier_consumer_ground_assertion_supported_by_completion(a));
        let ground_assertions_consistent =
            !assertions_have_direct_boolean_conflict(&self.ctx.terms, &ground_assertions)
                && !self.assertions_have_simple_int_contradiction(&ground_assertions);
        let forall_quantifiers_supported_by_uf_completion = forall_quantifiers
            .iter()
            .copied()
            .all(|q| self.quantifier_supported_by_uf_completion(q));
        let quantifiers_supported_by_uf_completion = !forall_quantifiers.is_empty()
            && ground_assertions_supported_by_uf_completion
            && ground_assertions_consistent
            && forall_quantifiers_supported_by_uf_completion;
        if std::env::var_os("AY_DEBUG_CERT").is_some() {
            eprintln!(
                "CERT: nforall={} ground_ok={} consistent={} forall_ok={} candidate={}",
                forall_quantifiers.len(),
                ground_assertions_supported_by_uf_completion,
                ground_assertions_consistent,
                forall_quantifiers_supported_by_uf_completion,
                quantifiers_supported_by_uf_completion,
            );
        }
        // 9. CEGQI setup for unhandled quantifiers + FlattenAnd + strip quantifiers.
        self.set_active_solve_phase("quantifier-cegqi-setup", "cegqi");
        let cegqi = self.setup_cegqi_for_unhandled(
            &quantifiers,
            ematching.has_uninstantiated,
            &ematching.uninstantiated_quantifiers,
        );

        // 10. Post-CEGQI E-matching pass (#7979): enumerative instantiation and
        // CEGQI may have introduced new ground terms (e.g., f(6)) that trigger
        // patterns in quantifiers that had no matches in step 4. Run one more
        // E-matching round over the current assertions (which now include
        // enumerative instances) combined with the original quantifiers.
        //
        // At this point, quantifiers have been stripped from self.ctx.assertions
        // by flatten_and_strip_quantifiers in step 9. We re-add them from the
        // refinement snapshot for this E-matching pass, then add any new
        // instances to the stripped assertion set.
        //
        // Guard: only run the extra round when CEGQI or enumerative
        // instantiation actually added new ground terms AND there are still
        // uninstantiated quantifiers that might benefit. When CEGQI didn't
        // handle any quantifiers, no new ground terms were produced, so the
        // post-CEGQI E-matching round would be redundant — and can cause
        // severe slowdowns (17x on verification-consumer produces/reflexivity pattern).
        let cegqi_produced_new_terms = cegqi.cegqi_has_forall || cegqi.cegqi_has_exists;
        let (post_cegqi_added, post_cegqi_ematching) =
            if ematching.has_uninstantiated && cegqi_produced_new_terms {
                self.set_active_solve_phase("quantifier-post-cegqi-ematching", "ematching");
                self.run_post_cegqi_ematching(
                    &refinement_assertions,
                    &ematching.uninstantiated_quantifiers,
                    &cegqi.cegqi_ce_lemma_ids,
                )
            } else {
                (false, None)
            };
        let ematching_added = ematching_added || post_cegqi_added;
        // Track actual E-matching provenance rather than inferring it from
        // `quantifiers - uninstantiated_quantifiers`. `collect_quantifiers`
        // performs NNF conversion and may mint a logically equivalent
        // quantifier with a fresh TermId on each collection; comparing those
        // independently collected IDs falsely classified untouched Exists as
        // instantiated (#satgate-vacuous-binder). The direct per-round source
        // set also covers the post-CEGQI pass, which the old inference omitted.
        let ematching_has_exists = ematching
            .instantiated_quantifiers
            .iter()
            .chain(
                post_cegqi_ematching
                    .iter()
                    .flat_map(|summary| summary.instantiated_quantifiers.iter()),
            )
            .any(|&q| matches!(self.ctx.terms.get(q), TermData::Exists(..)));
        // Post-CEGQI E-matching may have resolved previously-uninstantiated quantifiers.
        let has_uninstantiated = post_cegqi_ematching
            .as_ref()
            .map_or(ematching.has_uninstantiated, |e| e.has_uninstantiated);
        let reached_limit = ematching.reached_limit
            || post_cegqi_ematching
                .as_ref()
                .is_some_and(|e| e.reached_limit);

        // Accumulate E-matching statistics across main + post-CEGQI rounds (#8614).
        let ematching_rounds_completed = ematching.rounds_completed
            + post_cegqi_ematching
                .as_ref()
                .map_or(0, |e| e.rounds_completed);
        let ematching_instances_created = ematching.instances_created
            + post_cegqi_ematching
                .as_ref()
                .map_or(0, |e| e.instances_created);

        QuantifierProcessingResult {
            has_uninstantiated_quantifiers: has_uninstantiated,
            reached_instantiation_limit: reached_limit,
            has_deferred: deferred_exists,
            cegqi_has_forall: cegqi.cegqi_has_forall,
            cegqi_has_exists: cegqi.cegqi_has_exists,
            ematching_added_instantiations: ematching_added,
            refinement_assertions,
            cegqi_ce_lemma_ids: cegqi.cegqi_ce_lemma_ids,
            cegqi_ce_lemma_groups: cegqi.cegqi_ce_lemma_groups,
            has_completely_unhandled_quantifiers: cegqi.has_completely_unhandled_quantifiers,
            unhandled_quantifiers: cegqi.unhandled_quantifiers,
            ematching_has_exists,
            ematching_rounds_completed,
            ematching_instances_created,
            original_assertions,
            exact_finite_expansion: None,
            cegqi_state: cegqi.cegqi_state,
            has_unsafe_partial_quantifiers,
            // Candidate only: result mapping may use this to schedule sound
            // refutation probes, never to grant SAT or bypass model validation.
            // The accepted atoms need not admit one shared interpretation (for
            // example `f(x)=0 /\ x=f(x)`), and a first E-match is not coverage.
            quantifiers_supported_by_uf_completion,
        }
    }
}

fn app_args<'a>(terms: &'a TermStore, term: TermId, name: &str) -> Option<&'a [TermId]> {
    match terms.get(term) {
        TermData::App(sym, args) if sym.name() == name => Some(args.as_slice()),
        _ => None,
    }
}

/// A sort whose interpretation is FIXED and fully determined by the theory
/// (`Bool`, `Int`, `Real`, `BitVec`). A closed universal over such sorts is
/// model-independent: deciding `∃ x. ¬body` over the (unique) standard domain
/// soundly decides whether the universal is false. Sorts whose domain the model
/// may choose — `Uninterpreted` (cardinality unconstrained), `Datatype`,
/// `Array`, `Seq`, `String`, `RegLan`, `FloatingPoint` — are NOT fixed for this
/// precheck and are excluded.
fn is_fixed_interpretation_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_))
}

/// Return `Some((vars, body))` when `term` is a `Forall` whose `body` is a
/// CLOSED, quantifier-free formula: it has no nested quantifiers and every free
/// symbol it references is one of the forall's own binders.
///
/// "Closed" here means model-INDEPENDENT: the universal's truth value does not
/// depend on any free constant, uninterpreted function/predicate, array, or
/// outer-bound variable. A declared 0-arity constant such as `(declare-fun x ()
/// Int)` is interned as a `TermData::Var` (see `Solver::declare_const`), exactly
/// like a bound variable, so the closedness test is simply: every `Var` name in
/// the body is one of `vars`, AND the body applies no named uninterpreted
/// symbol (any `App(Named(f), ..)` whose `f` is not a built-in operator would be
/// a free function/predicate/array symbol). Built-in arithmetic / Boolean
/// operators are allowed.
///
/// CRITICAL: every binder sort must have a FIXED, fully-determined
/// interpretation (`Bool` / `Int` / `Real` / `BitVec`). Only then is "the
/// skolemized negation is SAT" equivalent to "the existential is true in the one
/// standard model" equivalent to "the universal is false". For an UNINTERPRETED
/// sort `U` the model is free to choose the domain (and its cardinality), so a
/// ground SAT for `(not (= u v))` only witnesses ONE interpretation (|U| >= 2),
/// not validity of the existential across all interpretations — `∀u v:U. u=v`
/// is genuinely SAT (interpret U as a singleton). Datatype / Array / Seq /
/// String / RegLan / FP binders are likewise excluded: their skolemized-negation
/// SAT is not a sound refutation of the universal here.
///
/// Such a universal is either valid (do nothing) or unconditionally false
/// (`(check-sat)` is UNSAT regardless of the rest of the problem) — see
/// `Executor::closed_universal_validity_precheck`.
fn closed_quantifier_free_forall_parts(
    terms: &TermStore,
    term: TermId,
) -> Option<(Vec<(String, Sort)>, TermId)> {
    closed_quantifier_free_forall_parts_with_operators(terms, term, is_builtin_operator)
}

/// Return the closed scalar universals on which a concrete literal tuple may
/// be checked without assigning any model-dependent symbol.
///
/// This is intentionally a different class from
/// [`closed_quantifier_free_forall_parts`].  The latter asks whether a
/// skolemized negation is model-independent and must therefore exclude
/// under-specified division-by-zero operators.  Here a verdict is authorized
/// only by one *fully evaluated* ground tuple (and zero-divisor evaluations
/// remain `Unknown`), so `div`/`mod`/`rem`, the fixed Int/Real conversion
/// operators, and fixed-width BV comparisons are safe to admit. Free
/// declarations remain excluded.
pub(in crate::executor) fn closed_quantifier_free_forall_literal_parts(
    terms: &TermStore,
    term: TermId,
) -> Option<(Vec<(String, Sort)>, TermId)> {
    let parts = closed_quantifier_free_forall_parts_with_operators(
        terms,
        term,
        is_literal_witness_operator,
    )?;
    parts
        .0
        .iter()
        .all(|(_, sort)| matches!(sort, Sort::Int | Sort::Real | Sort::BitVec(_)))
        .then_some(parts)
}

fn closed_quantifier_free_forall_parts_with_operators(
    terms: &TermStore,
    term: TermId,
    operator_allowed: impl Fn(&str) -> bool,
) -> Option<(Vec<(String, Sort)>, TermId)> {
    let (vars, body) = match terms.get(term) {
        TermData::Forall(vars, body, _) => (vars.clone(), *body),
        _ => return None,
    };
    // Body must be quantifier-free.
    if contains_quantifier(terms, body) {
        return None;
    }
    // Every binder must have a fixed-interpretation sort (see doc comment).
    if !vars.iter().all(|(_, s)| is_fixed_interpretation_sort(s)) {
        return None;
    }
    let closed = {
        let bound: ay_core::kani_compat::DetHashSet<&str> =
            vars.iter().map(|(n, _)| n.as_str()).collect();
        body_is_closed_and_uf_free(terms, body, &bound, operator_allowed)
    };
    if closed {
        Some((vars, body))
    } else {
        None
    }
}

/// Walk `body` and return `true` iff every `Var` it references is in `bound`
/// (no free constants / outer-bound variables) and it applies no free symbol
/// (no uninterpreted function/predicate, array op, or BV indexed op). Only
/// built-in arithmetic/Boolean/equality operators (`is_builtin_operator`,
/// classified by name) are permitted.
fn body_is_closed_and_uf_free(
    terms: &TermStore,
    body: TermId,
    bound: &ay_core::kani_compat::DetHashSet<&str>,
    operator_allowed: impl Fn(&str) -> bool,
) -> bool {
    use ay_core::kani_compat::DetHashSet as HashSet;
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack = vec![body];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(name, _) => {
                if !bound.contains(name.as_str()) {
                    return false;
                }
            }
            TermData::Const(_) => {}
            TermData::App(sym, args) => {
                // An application of anything other than a built-in
                // arithmetic/Boolean/equality operator is a free symbol
                // (uninterpreted function / predicate, array `select`/`store`,
                // BV indexed op, etc.). Only built-ins keep the universal
                // model-independent. `Indexed` symbols (e.g. BV extract) are
                // never built-ins for this precheck and disqualify here.
                if !operator_allowed(sym.name()) {
                    return false;
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Let(bindings, b) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            // Any nested quantifier was already excluded by the caller.
            _ => return false,
        }
    }
    true
}

/// Built-in TOTAL arithmetic / Boolean / equality operators whose presence keeps
/// a universal model-independent. Anything not on this list that appears as an
/// application is treated as a free / model-dependent symbol, so the universal
/// is conservatively NOT classified as closed (the precheck simply skips it —
/// never an unsoundness, only a missed refutation).
///
/// `div` / `mod` are DELIBERATELY EXCLUDED: SMT-LIB leaves division/modulo by
/// zero under-specified (a fixed-but-arbitrary per-model value), so a closed
/// universal whose body applies them is NOT model-independent — a ground SAT for
/// its negation could rest on one div-by-zero interpretation and wrongly refute
/// a universal that holds under another. Excluding them keeps the precheck sound
/// (it just never fires on such bodies). Likewise `to_int` / `to_real` /
/// `is_int` / `divisible` and all theory-specific ops are absent.
fn is_builtin_operator(name: &str) -> bool {
    matches!(
        name,
        "and"
            | "or"
            | "not"
            | "=>"
            | "xor"
            | "="
            | "distinct"
            | "ite"
            | "+"
            | "-"
            | "*"
            | "abs"
            | "<"
            | "<="
            | ">"
            | ">="
            | "true"
            | "false"
    )
}

/// Operators accepted by the exact-literal witness lane.  Every non-total
/// operation below remains fail-closed at an undefined literal (notably a zero
/// divisor); the lane never infers anything from `Unknown`.
pub(in crate::executor) fn is_literal_witness_operator(name: &str) -> bool {
    is_builtin_operator(name)
        || matches!(
            name,
            "/" | "div"
                | "mod"
                | "rem"
                | "to_real"
                | "to_int"
                | "is_int"
                | "bvult"
                | "bvule"
                | "bvugt"
                | "bvuge"
                | "bvslt"
                | "bvsle"
                | "bvsgt"
                | "bvsge"
        )
}

/// Collect AND-conjuncts of a term transitively (#5991).
///
/// If `term` is `(and A B)`, recursively collects conjuncts `A`, `B` (and
/// their sub-conjuncts if they are also ANDs). Non-AND terms produce no output.
/// Used to expand CE lemma IDs after AND-flattening so that disambiguation
/// correctly filters out flattened CE lemma components.
pub(in crate::executor) fn collect_and_conjuncts(
    terms: &TermStore,
    term: TermId,
    out: &mut Vec<TermId>,
) {
    if let TermData::App(ay_core::Symbol::Named(ref name), args) = terms.get(term) {
        if name == "and" {
            for &arg in args {
                out.push(arg);
                collect_and_conjuncts(terms, arg, out);
            }
        }
    }
}

/// Maximum split depth for [`collect_entailed_conjuncts`]. Beyond it the term
/// is emitted whole — still entailed, just not split further.
const MAX_ENTAILED_SPLIT_DEPTH: usize = 64;

/// The conjunct-splitting shape of a term, computed under an IMMUTABLE borrow
/// of the term store so the caller can then build negations mutably.
enum EntailedSplit {
    /// `(and a b …)` — every argument is entailed.
    And(Vec<TermId>),
    /// `(not (or a b …))` — every `(not a_i)` is entailed.
    NotOr(Vec<TermId>),
    /// `(not (=> a b))` — both `a` and `(not b)` are entailed.
    NotImplies(TermId, TermId),
    /// `(not (not a))` — `a` is entailed.
    DoubleNegation(TermId),
    /// Nothing to split: the term itself is the only conjunct.
    Leaf,
}

fn classify_entailed_split(terms: &TermStore, term: TermId) -> EntailedSplit {
    if let TermData::App(ay_core::Symbol::Named(ref name), args) = terms.get(term) {
        if name == "and" {
            return EntailedSplit::And(args.clone());
        }
    }
    let TermData::Not(inner) = terms.get(term) else {
        return EntailedSplit::Leaf;
    };
    match terms.get(*inner) {
        TermData::App(ay_core::Symbol::Named(ref name), args) if name == "or" => {
            EntailedSplit::NotOr(args.clone())
        }
        // `mk_implies` rewrites `=>` to `(or (not a) b)` at construction, so an
        // App("=>") normally never reaches here. It is still handled because
        // raw-interning paths (see `TermStore::subst`, which maps "=>"/"implies"
        // back through `mk_implies`) prove such nodes can exist.
        TermData::App(ay_core::Symbol::Named(ref name), args)
            if (name == "=>" || name == "implies") && args.len() == 2 =>
        {
            EntailedSplit::NotImplies(args[0], args[1])
        }
        TermData::Not(double) => EntailedSplit::DoubleNegation(*double),
        _ => EntailedSplit::Leaf,
    }
}

/// NNF-aware top-level conjunct extraction (#nested-array-residue-rescue).
///
/// SOUNDNESS — the ONE property every caller depends on: every term written to
/// `out` is a LOGICAL CONSEQUENCE of `term`. Each rule applied below is
/// entailment-preserving,
///
/// ```text
///   (and a b)      |= a      and |= b
///   (not (or a b)) |= (not a) and |= (not b)
///   (not (=> a b)) |= a      and |= (not b)
///   (not (not a))  |= a
/// ```
///
/// and every other shape is emitted WHOLE (a leaf), which is trivially entailed
/// by itself. Consequently `term |= (and out…)`, and — the part that matters —
/// the same holds for any SUBSET of `out`, because dropping conjuncts only
/// weakens the conjunction. A caller may therefore refute a filtered subset and
/// conclude that the original term is unsatisfiable.
///
/// The store is borrowed mutably because the `or` / `=>` rules must BUILD the
/// negated component. `mk_not` normalizes what it builds (double negation, De
/// Morgan, Boolean-ITE push-down); those are logical EQUIVALENCES, so they
/// preserve the entailment above.
///
/// Distinct from [`collect_and_conjuncts`], which only descends `and` and
/// serves CE-lemma disambiguation; that one is deliberately left untouched.
pub(in crate::executor) fn collect_entailed_conjuncts(
    terms: &mut TermStore,
    term: TermId,
    depth: usize,
    limit: usize,
    out: &mut Vec<TermId>,
) {
    // Emitting the unsplit term is always sound (it entails itself), so both
    // budget guards degrade to "less splitting", never to a wrong conjunct.
    if depth >= MAX_ENTAILED_SPLIT_DEPTH || out.len() >= limit {
        out.push(term);
        return;
    }
    match classify_entailed_split(terms, term) {
        EntailedSplit::And(args) => {
            for arg in args {
                collect_entailed_conjuncts(terms, arg, depth + 1, limit, out);
            }
        }
        EntailedSplit::NotOr(args) => {
            for arg in args {
                let negated = terms.mk_not(arg);
                collect_entailed_conjuncts(terms, negated, depth + 1, limit, out);
            }
        }
        EntailedSplit::NotImplies(lhs, rhs) => {
            collect_entailed_conjuncts(terms, lhs, depth + 1, limit, out);
            let negated = terms.mk_not(rhs);
            collect_entailed_conjuncts(terms, negated, depth + 1, limit, out);
        }
        EntailedSplit::DoubleNegation(inner) => {
            collect_entailed_conjuncts(terms, inner, depth + 1, limit, out);
        }
        EntailedSplit::Leaf => out.push(term),
    }
}
