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
mod model_completion;
mod preprocess;
mod result_mapping;

use ay_core::{Constant, Sort, TermData, TermId, TermStore};
use num_bigint::BigInt;

pub(in crate::executor) use cegqi_refinement::unsupported_arith_mentions_ce_var;
pub(in crate::executor) use family_classifier::write_family_class_statistics;

use super::Executor;
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
            (vars.iter().any(|(_, s)| is_mbqi_unsafe_binder_sort(s))
                || forall_indexes_array_at_binder(terms, vars, *body))
                && !model_completion::is_quantifier_consumer_seq_model_completion_quantifier(
                    terms, term,
                )
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
    /// True for the narrow QuantifierConsumer opaque-Seq axiom bundle where skipped
    /// quantifiers are a definitional library over otherwise-ground AUFLIA
    /// constraints. This is a positive certificate used to bypass the broad
    /// unsafe-partial and skipped-quantifier gates without weakening them for
    /// arbitrary Seq-binder formulas.
    pub quantifier_consumer_opaque_seq_sat_certificate: bool,
    /// True when every remaining universal quantifier with an MBQI-unsafe
    /// binder sort is a definition/axiom family that the UF-completion
    /// soundness gate can discharge. This is narrower than the QuantifierConsumer opaque
    /// Seq certificate because mixed QuantifierConsumer library bundles can include
    /// both Seq definitions and non-Seq UF definitions.
    pub unsafe_quantifiers_supported_by_uf_completion: bool,
    /// True when every collected universal quantifier is a definition/axiom
    /// family that UF completion can discharge. Used to recover SAT when
    /// E-matching creates ground mixed-collection instances that the lower
    /// theory route cannot solve, but the original quantified library facts
    /// are syntactically completion-safe.
    pub quantifiers_supported_by_uf_completion: bool,
    /// Like `quantifiers_supported_by_uf_completion` but with the ground
    /// assertions checked under MODEL-BACKED (evaluability-only) semantics:
    /// pure-arithmetic ground atoms are allowed because a genuine solver model
    /// establishes their truth directly. ONLY sound to consult when the lower
    /// result is a genuine `Sat` (or a validated model exists) — never for
    /// promoting a lower `Unknown` (#quantifier_consumer-arith wrong-SAT).
    pub quantifiers_supported_by_uf_completion_given_sat: bool,
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
            cegqi_state: Vec::new(),
            has_unsafe_partial_quantifiers: false,
            quantifier_consumer_opaque_seq_sat_certificate: false,
            unsafe_quantifiers_supported_by_uf_completion: false,
            quantifiers_supported_by_uf_completion: false,
            quantifiers_supported_by_uf_completion_given_sat: false,
        }
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
            self.install_quantifier_proof_source_provenance(&authored_assertions);
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
            // all quantifiers — the ground result is complete.
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

        // 5. Add E-matching instances (duplicate + model-satisfied filtering).
        //    Records the sound support-axiom subset into `active_support_axioms`.
        //    For MBQI-unsafe partial quantifiers (e.g. an array-indexing frame
        //    invariant) the presolve model that Phase C filters against is not a
        //    model of the quantified problem, so a "satisfied" instance can hinge
        //    on a defaulted, not-yet-constrained ground term; dropping it loses a
        //    genuine constraint and turns a decided verdict into `Unknown`
        //    (#stale-presolve-frame-skip). Suppress that skip for such problems —
        //    adding every sound E-matched instance can only recover completeness.
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
                    // The derived table is live for EXACTLY this one expansion call
                    // and cleared immediately. It must never be visible to a nested
                    // sub-solve: those run on a SUBSET of the assertions, which need
                    // not entail these constants, so folding them in there would not
                    // be equals-for-equals.
                    crate::skolemize::set_derived_consts(consts);
                    self.expand_finite_domains();
                    crate::skolemize::set_derived_consts(Default::default());
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

        // 8. Collect quantifiers and track exists E-matching processing (#3593).
        let mut quantifiers: Vec<TermId> = Vec::new();
        for assertion in self.ctx.assertions.clone() {
            collect_quantifiers(&mut self.ctx.terms, assertion, &mut quantifiers);
        }
        quantifiers.sort_unstable_by_key(|term| term.index());
        quantifiers.dedup();

        let ematching_has_exists = quantifiers.iter().any(|&q| {
            matches!(self.ctx.terms.get(q), TermData::Exists(..))
                && !ematching.uninstantiated_quantifiers.contains(&q)
        });

        let unsafe_quantifiers: Vec<TermId> = quantifiers
            .iter()
            .copied()
            .filter(|&q| forall_has_unsafe_binder(&self.ctx.terms, q))
            .collect();
        let unsafe_quantifiers_supported_by_uf_completion = !unsafe_quantifiers.is_empty()
            && unsafe_quantifiers
                .iter()
                .copied()
                .all(|q| self.quantifier_supported_by_uf_completion(q));
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
                "CERT: nforall={} unsafe={} unsafe_ok={} ground_ok={} consistent={} forall_ok={} strict={}",
                forall_quantifiers.len(),
                unsafe_quantifiers.len(),
                unsafe_quantifiers_supported_by_uf_completion,
                ground_assertions_supported_by_uf_completion,
                ground_assertions_consistent,
                forall_quantifiers_supported_by_uf_completion,
                quantifiers_supported_by_uf_completion,
            );
        }
        // MODEL-BACKED variant (#quantifier_consumer-arith completeness): the same
        // certificate with ground assertions checked for evaluability only.
        // Consulted downstream ONLY when the lower result is a genuine `Sat`
        // (or the model was validated), where pure-arithmetic ground atoms are
        // already established by the model itself. In exchange for relaxing
        // the ground-atom freedom gate, the FORALL side is much stricter than
        // `quantifier_supported_by_uf_completion`: every forall must be a
        // POINTWISE-MATERIALIZABLE UF definition (`forall v⃗. f(v⃗) = rhs`,
        // non-recursive, interpreted-pure rhs, distinct-bound-var head), so
        // that `f := λv⃗. eval(rhs)` extends the model without disturbing any
        // other symbol. Full e-matching instantiation coverage is required
        // separately at the construction site below: it guarantees the ground
        // model already agrees with each definition at every ground
        // application, so the materialization preserves the validated ground
        // assertions (rejects the recursive popcount fixpoint shape, #8969).
        let ground_assertions_supported_given_model = ground_assertions.iter().copied().all(|a| {
            self.quantifier_consumer_ground_assertion_supported_by_completion_ext(a, true)
        });
        // FRAGMENT SCOPE (#8969 popcount wrong-SAT): the "genuine Sat" premise
        // of the model-backed leg only holds where the ground solve is
        // DECISION-COMPLETE and the model fully evaluable. In QF_UFBV (all
        // subterms Bool/BitVec) a ground `Sat` carries a total bit-level model
        // with no unevaluable atoms; the same holds for LINEAR Int + EUF, so
        // the fragment is `term_in_bv_bool_euf_lia_fragment` (rank-9 step 3:
        // Bool / BitVec / Int sorts, linear evaluable operators only — a
        // strict superset of the previous BV/Bool gate). A UFLIA ground core
        // with `div`/`mod`/`*` (popcount SWAR) can return a "Sat" whose model
        // validation silently falls back on atoms it cannot evaluate —
        // trusting the certificate there fabricates a counterexample to
        // correct code — so those operators stay excluded.
        //
        // DEFINITION SHAPES (rank-9 step 3): each forall must be a pointwise-
        // materializable UF definition, now including GUARDED definitions
        // `forall v⃗. guard(v⃗) => f(v⃗) = rhs` with interpreted-pure, f-free
        // guard and rhs (see `pointwise_materializable_uf_definition_head`).
        // The materialization argument is per SYMBOL, so the defined heads
        // must be PAIRWISE DISTINCT: two definitions of the same symbol can
        // clash at a point no ground application covers (`v>=0 => f(v)=1` and
        // `v<=0 => f(v)=2` clash at 0 while a ground core touching only f(5)
        // stays satisfiable) — accepting both would mint a wrong SAT.
        let mut given_sat_definition_heads: Vec<String> =
            Vec::with_capacity(forall_quantifiers.len());
        let given_sat_definitions_ok = !forall_quantifiers.is_empty()
            && forall_quantifiers.iter().copied().all(|q| {
                let Some(head) = self.pointwise_materializable_uf_definition_head(q) else {
                    return false;
                };
                given_sat_definition_heads.push(head);
                match self.ctx.terms.get(q) {
                    TermData::Forall(_, body, _) => self.term_in_bv_bool_euf_lia_fragment(*body),
                    _ => false,
                }
            })
            && {
                given_sat_definition_heads.sort_unstable();
                given_sat_definition_heads
                    .windows(2)
                    .all(|pair| pair[0] != pair[1])
            };
        // NOTE (#2774 arm REMOVED — wrong-SAT): ae06cec3b5 OR-ed a
        // left-inverse/identity certificate into this flag. Its "genuine
        // ground Sat over a decision-complete core" premise was UNENFORCED:
        // `ground_assertions_consistent` is a syntactic probe, and admitting
        // uninterpreted-sorted equalities between distinct UF applications
        // (`term_in_bv_bool_euf_lia_fragment_ext(_, true)`) let the ground
        // solve treat them as FREE — missing the quantifier-derived
        // congruence consequences. Counterexample (answered wrong `sat`;
        // genuinely UNSAT by congruence through Unbox):
        //   forall x. Unbox(Box x) = x  :pattern (Box x)
        //   (distinct a b)  (= (Box a) (Box b))
        // The sound replacement is the upstream #2774 left-inverse SAT
        // certificate (`mbqi_sat_validated_left_inverse_axioms`): it EXHIBITS
        // a total materialized model and RE-EVALUATES every original ground
        // assertion under it, so a non-injectivity fact re-evaluates false
        // and the certificate declines. Do not re-add a shape-only arm here.
        let quantifiers_supported_by_uf_completion_given_sat = given_sat_definitions_ok
            && ground_assertions_supported_given_model
            && ground_assertions_consistent
            && ground_assertions
                .iter()
                .copied()
                .all(|a| self.term_in_bv_bool_euf_lia_fragment(a));
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
                )
            } else {
                (false, None)
            };
        let ematching_added = ematching_added || post_cegqi_added;
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

        let quantifier_consumer_opaque_seq_sat_certificate =
            original_assertions.as_ref().is_some_and(|orig| {
                has_quantifier_consumer_opaque_seq_sat_certificate(
                    &self.ctx.terms,
                    orig,
                    &self.ctx.assertions,
                )
            });
        if std::env::var_os("AY_DEBUG_CERT").is_some() {
            eprintln!(
                "CERT2: quantifier_consumer_opaque={quantifier_consumer_opaque_seq_sat_certificate} uninst={has_uninstantiated} limit={reached_limit}"
            );
        }

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
            cegqi_state: cegqi.cegqi_state,
            has_unsafe_partial_quantifiers,
            quantifier_consumer_opaque_seq_sat_certificate,
            unsafe_quantifiers_supported_by_uf_completion,
            quantifiers_supported_by_uf_completion,
            // Coverage conditions for the model-backed leg (see the flag's
            // computation above): every quantifier fully instantiated by
            // E-matching within budget (the ground model therefore agrees
            // with each pointwise-materializable definition at every ground
            // application) and no existential (materialization supplies no
            // witnesses).
            quantifiers_supported_by_uf_completion_given_sat:
                quantifiers_supported_by_uf_completion_given_sat
                    && !has_uninstantiated
                    && !reached_limit
                    // A deferred (cost-capped, not-yet-asserted) instantiation
                    // is a coverage gap even when its quantifier produced
                    // other instances: the ground model was never forced to
                    // agree with the definition at that point, so the
                    // materialization premise fails. Conservative tightening
                    // (rank-9 step 3).
                    && !deferred_exists
                    && !quantifiers
                        .iter()
                        .any(|&q| matches!(self.ctx.terms.get(q), TermData::Exists(..))),
        }
    }
}

fn has_quantifier_consumer_opaque_seq_sat_certificate(
    terms: &TermStore,
    original_assertions: &[TermId],
    ground_assertions: &[TermId],
) -> bool {
    let mut saw_quantifier_consumer_axiom = false;
    for &assertion in original_assertions {
        if contains_quantifier(terms, assertion) {
            if !is_quantifier_consumer_opaque_seq_axiom(terms, assertion) {
                return false;
            }
            saw_quantifier_consumer_axiom = true;
        } else if !is_quantifier_consumer_opaque_seq_ground_fragment(terms, assertion) {
            return false;
        }
    }

    saw_quantifier_consumer_axiom
        && quantifier_consumer_seq_len_ground_terms_have_nonneg_instances(
            terms,
            original_assertions,
            ground_assertions,
        )
}

fn is_quantifier_consumer_opaque_seq_axiom(terms: &TermStore, assertion: TermId) -> bool {
    let TermData::Forall(vars, body, _) = terms.get(assertion) else {
        return false;
    };

    match vars.as_slice() {
        [(s, sort)] if is_seq_int_sort(sort) => {
            is_quantifier_consumer_seq_len_nonnegative_axiom(terms, *body, s)
                || is_quantifier_consumer_seq_concat_left_identity_axiom(terms, *body, s)
                || is_quantifier_consumer_seq_concat_right_identity_axiom(terms, *body, s)
        }
        [(v, Sort::Int)] => is_quantifier_consumer_seq_empty_contains_axiom(terms, *body, v),
        [(s, sort_s), (i, Sort::Int)] if is_seq_int_sort(sort_s) => {
            is_quantifier_consumer_seq_select_bridge_axiom(terms, *body, s, i)
                || is_quantifier_consumer_seq_get_in_bounds_axiom(terms, *body, s, i)
                || is_quantifier_consumer_seq_get_out_of_bounds_axiom(terms, *body, s, i)
                || is_quantifier_consumer_seq_push_front_definition_axiom(terms, *body, s, i)
                || is_quantifier_consumer_seq_push_back_definition_axiom(terms, *body, s, i)
        }
        [(lhs, lhs_sort), (rhs, rhs_sort)]
            if is_seq_int_sort(lhs_sort) && is_seq_int_sort(rhs_sort) =>
        {
            is_quantifier_consumer_seq_concat_len_axiom(terms, *body, lhs, rhs)
        }
        [(s, s_sort), (v, Sort::Int), (x, Sort::Int)] if is_seq_int_sort(s_sort) => {
            is_quantifier_consumer_seq_contains_push_back_axiom(terms, *body, s, v, x)
        }
        [(s1, s1_sort), (s2, s2_sort), (i, Sort::Int)]
            if is_seq_int_sort(s1_sort) && is_seq_int_sort(s2_sort) =>
        {
            is_quantifier_consumer_seq_concat_left_index_axiom(terms, *body, s1, s2, i)
                || is_quantifier_consumer_seq_concat_right_index_axiom(terms, *body, s1, s2, i)
        }
        [(s1, s1_sort), (s2, s2_sort), (s3, s3_sort)]
            if is_seq_int_sort(s1_sort) && is_seq_int_sort(s2_sort) && is_seq_int_sort(s3_sort) =>
        {
            is_quantifier_consumer_seq_concat_assoc_axiom(terms, *body, s1, s2, s3)
        }
        _ => false,
    }
}

fn is_quantifier_consumer_opaque_seq_ground_fragment(terms: &TermStore, assertion: TermId) -> bool {
    let mut stack = vec![assertion];
    while let Some(term) = stack.pop() {
        match terms.get(term) {
            TermData::Forall(..) | TermData::Exists(..) => return false,
            TermData::Var(name, _) if is_blocked_quantifier_consumer_seq_ground_symbol(name) => {
                return false;
            }
            TermData::App(sym, args) => {
                if is_blocked_quantifier_consumer_seq_ground_symbol(sym.name()) {
                    return false;
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Const(_) => {}
            _ => {}
        }
    }
    true
}

fn is_blocked_quantifier_consumer_seq_ground_symbol(name: &str) -> bool {
    name.starts_with("seq.")
        || matches!(
            name,
            "logic_None"
                | "logic_Some"
                | "seq_concat"
                | "seq_contains"
                | "seq_get"
                | "seq_index_logic"
                | "seq_push_back"
                | "seq_push_front"
                | "seq_reverse"
                | "seq_set"
                | "seq_singleton"
                | "seq_subsequence"
                | "seq_sum"
        )
}

fn quantifier_consumer_seq_len_ground_terms_have_nonneg_instances(
    terms: &TermStore,
    original_assertions: &[TermId],
    ground_assertions: &[TermId],
) -> bool {
    let mut seq_len_terms = Vec::new();
    for &assertion in original_assertions {
        if !contains_quantifier(terms, assertion) {
            collect_seq_len_terms(terms, assertion, &mut seq_len_terms);
        }
    }
    seq_len_terms.sort_unstable_by_key(|t| t.0);
    seq_len_terms.dedup();

    seq_len_terms.into_iter().all(|len_term| {
        ground_assertions
            .iter()
            .copied()
            .any(|assertion| contains_le_zero_term(terms, assertion, len_term))
    })
}

fn collect_seq_len_terms(terms: &TermStore, term: TermId, out: &mut Vec<TermId>) {
    match terms.get(term) {
        TermData::App(sym, args) => {
            if sym.name() == "seq_len" && args.len() == 1 {
                out.push(term);
            }
            for &arg in args {
                collect_seq_len_terms(terms, arg, out);
            }
        }
        TermData::Not(inner) => collect_seq_len_terms(terms, *inner, out),
        TermData::Ite(c, t, e) => {
            collect_seq_len_terms(terms, *c, out);
            collect_seq_len_terms(terms, *t, out);
            collect_seq_len_terms(terms, *e, out);
        }
        TermData::Let(bindings, body) => {
            for (_, value) in bindings {
                collect_seq_len_terms(terms, *value, out);
            }
            collect_seq_len_terms(terms, *body, out);
        }
        TermData::Forall(..) | TermData::Exists(..) | TermData::Const(_) | TermData::Var(_, _) => {}
        _ => {}
    }
}

fn contains_le_zero_term(terms: &TermStore, term: TermId, target: TermId) -> bool {
    if is_le_zero_term(terms, term, target) {
        return true;
    }
    match terms.get(term) {
        TermData::App(sym, args) if sym.name() == "and" => args
            .iter()
            .copied()
            .any(|arg| contains_le_zero_term(terms, arg, target)),
        _ => false,
    }
}

fn is_le_zero_term(terms: &TermStore, term: TermId, target: TermId) -> bool {
    app_args(terms, term, "<=")
        .is_some_and(|args| args.len() == 2 && is_int_const(terms, args[0], 0) && args[1] == target)
        // An equality pinning the term to a nonnegative constant is a strictly
        // stronger nonneg instance than `(<= 0 t)` — the verification-consumer preamble
        // states `(= 0 (seq_len seq_empty))` rather than a bound.
        || app_args(terms, term, "=").is_some_and(|args| {
            args.len() == 2
                && ((args[1] == target && is_nonneg_int_const(terms, args[0]))
                    || (args[0] == target && is_nonneg_int_const(terms, args[1])))
        })
}

fn is_nonneg_int_const(terms: &TermStore, term: TermId) -> bool {
    matches!(
        terms.get(term),
        TermData::Const(Constant::Int(n)) if n.sign() != num_bigint::Sign::Minus
    )
}

fn is_seq_int_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Seq(elem) if elem.as_ref() == &Sort::Int)
}

fn app_args<'a>(terms: &'a TermStore, term: TermId, name: &str) -> Option<&'a [TermId]> {
    match terms.get(term) {
        TermData::App(sym, args) if sym.name() == name => Some(args.as_slice()),
        _ => None,
    }
}

fn is_var_named(terms: &TermStore, term: TermId, name: &str) -> bool {
    matches!(terms.get(term), TermData::Var(n, _) if n == name)
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
        body_is_closed_and_uf_free(terms, body, &bound)
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
                if !is_builtin_operator(sym.name()) {
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

fn is_seq_empty(terms: &TermStore, term: TermId) -> bool {
    is_var_named(terms, term, "seq_empty")
}

fn is_int_const(terms: &TermStore, term: TermId, value: i64) -> bool {
    matches!(
        terms.get(term),
        TermData::Const(Constant::Int(n)) if n == &BigInt::from(value)
    )
}

fn is_not<P>(terms: &TermStore, term: TermId, pred: P) -> bool
where
    P: Fn(TermId) -> bool,
{
    matches!(terms.get(term), TermData::Not(inner) if pred(*inner))
}

fn is_eq_between<P, Q>(terms: &TermStore, term: TermId, left: P, right: Q) -> bool
where
    P: Fn(TermId) -> bool,
    Q: Fn(TermId) -> bool,
{
    app_args(terms, term, "=").is_some_and(|args| {
        args.len() == 2 && ((left(args[0]) && right(args[1])) || (left(args[1]) && right(args[0])))
    })
}

fn is_or_with3<P, Q, R>(terms: &TermStore, term: TermId, p: P, q: Q, r: R) -> bool
where
    P: Fn(TermId) -> bool,
    Q: Fn(TermId) -> bool,
    R: Fn(TermId) -> bool,
{
    app_args(terms, term, "or").is_some_and(|args| {
        args.len() == 3
            && args.iter().copied().any(&p)
            && args.iter().copied().any(&q)
            && args.iter().copied().any(&r)
    })
}

fn is_or_with2<P, Q>(terms: &TermStore, term: TermId, p: P, q: Q) -> bool
where
    P: Fn(TermId) -> bool,
    Q: Fn(TermId) -> bool,
{
    app_args(terms, term, "or").is_some_and(|args| {
        args.len() == 2 && args.iter().copied().any(&p) && args.iter().copied().any(&q)
    })
}

fn is_and_with2<P, Q>(terms: &TermStore, term: TermId, p: P, q: Q) -> bool
where
    P: Fn(TermId) -> bool,
    Q: Fn(TermId) -> bool,
{
    app_args(terms, term, "and").is_some_and(|args| {
        args.len() == 2 && args.iter().copied().any(&p) && args.iter().copied().any(&q)
    })
}

fn is_plus_of2<P, Q>(terms: &TermStore, term: TermId, p: P, q: Q) -> bool
where
    P: Fn(TermId) -> bool,
    Q: Fn(TermId) -> bool,
{
    app_args(terms, term, "+").is_some_and(|args| {
        args.len() == 2 && args.iter().copied().any(&p) && args.iter().copied().any(&q)
    })
}

fn is_le_zero_var(terms: &TermStore, term: TermId, var: &str) -> bool {
    app_args(terms, term, "<=").is_some_and(|args| {
        args.len() == 2 && is_int_const(terms, args[0], 0) && is_var_named(terms, args[1], var)
    })
}

fn is_le_seq_len_var(terms: &TermStore, term: TermId, seq: &str, var: &str) -> bool {
    app_args(terms, term, "<=").is_some_and(|args| {
        args.len() == 2
            && is_seq_len_of_var(terms, args[0], seq)
            && is_var_named(terms, args[1], var)
    })
}

fn is_lt_var_zero(terms: &TermStore, term: TermId, var: &str) -> bool {
    app_args(terms, term, "<").is_some_and(|args| {
        args.len() == 2 && is_var_named(terms, args[0], var) && is_int_const(terms, args[1], 0)
    })
}

fn is_lt_var_seq_len(terms: &TermStore, term: TermId, var: &str, seq: &str) -> bool {
    app_args(terms, term, "<").is_some_and(|args| {
        args.len() == 2
            && is_var_named(terms, args[0], var)
            && is_seq_len_of_var(terms, args[1], seq)
    })
}

fn is_seq_len_of_var(terms: &TermStore, term: TermId, seq: &str) -> bool {
    app_args(terms, term, "seq_len")
        .is_some_and(|args| args.len() == 1 && is_var_named(terms, args[0], seq))
}

fn is_seq_offset_of_var(terms: &TermStore, term: TermId, seq: &str) -> bool {
    app_args(terms, term, "seq_offset")
        .is_some_and(|args| args.len() == 1 && is_var_named(terms, args[0], seq))
}

fn is_seq_array_of_var(terms: &TermStore, term: TermId, seq: &str) -> bool {
    app_args(terms, term, "seq_array")
        .is_some_and(|args| args.len() == 1 && is_var_named(terms, args[0], seq))
}

fn is_seq_index_logic(terms: &TermStore, term: TermId, seq: &str, idx: &str) -> bool {
    app_args(terms, term, "seq_index_logic").is_some_and(|args| {
        args.len() == 2 && is_var_named(terms, args[0], seq) && is_var_named(terms, args[1], idx)
    })
}

fn is_seq_index_logic_concat(
    terms: &TermStore,
    term: TermId,
    s1: &str,
    s2: &str,
    idx: &str,
) -> bool {
    app_args(terms, term, "seq_index_logic").is_some_and(|args| {
        args.len() == 2
            && is_seq_concat_vars(terms, args[0], s1, s2)
            && is_var_named(terms, args[1], idx)
    })
}

fn is_seq_index_logic_concat_offset(
    terms: &TermStore,
    term: TermId,
    s1: &str,
    s2: &str,
    idx: &str,
) -> bool {
    app_args(terms, term, "seq_index_logic").is_some_and(|args| {
        args.len() == 2
            && is_seq_concat_vars(terms, args[0], s1, s2)
            && is_plus_of2(
                terms,
                args[1],
                |t| is_seq_len_of_var(terms, t, s1),
                |t| is_var_named(terms, t, idx),
            )
    })
}

fn is_seq_get(terms: &TermStore, term: TermId, seq: &str, idx: &str) -> bool {
    app_args(terms, term, "seq_get").is_some_and(|args| {
        args.len() == 2 && is_var_named(terms, args[0], seq) && is_var_named(terms, args[1], idx)
    })
}

fn is_seq_contains_var(terms: &TermStore, term: TermId, seq: &str, value: &str) -> bool {
    app_args(terms, term, "seq_contains").is_some_and(|args| {
        args.len() == 2 && is_var_named(terms, args[0], seq) && is_var_named(terms, args[1], value)
    })
}

fn is_seq_contains_empty(terms: &TermStore, term: TermId, value: &str) -> bool {
    app_args(terms, term, "seq_contains").is_some_and(|args| {
        args.len() == 2 && is_seq_empty(terms, args[0]) && is_var_named(terms, args[1], value)
    })
}

fn is_seq_contains_push_back(
    terms: &TermStore,
    term: TermId,
    seq: &str,
    pushed: &str,
    value: &str,
) -> bool {
    app_args(terms, term, "seq_contains").is_some_and(|args| {
        args.len() == 2
            && is_seq_push_back(terms, args[0], seq, pushed)
            && is_var_named(terms, args[1], value)
    })
}

fn is_seq_push_back(terms: &TermStore, term: TermId, seq: &str, value: &str) -> bool {
    app_args(terms, term, "seq_push_back").is_some_and(|args| {
        args.len() == 2 && is_var_named(terms, args[0], seq) && is_var_named(terms, args[1], value)
    })
}

fn is_seq_push_front(terms: &TermStore, term: TermId, seq: &str, value: &str) -> bool {
    app_args(terms, term, "seq_push_front").is_some_and(|args| {
        args.len() == 2 && is_var_named(terms, args[0], seq) && is_var_named(terms, args[1], value)
    })
}

fn is_seq_singleton_var(terms: &TermStore, term: TermId, value: &str) -> bool {
    app_args(terms, term, "seq_singleton")
        .is_some_and(|args| args.len() == 1 && is_var_named(terms, args[0], value))
}

fn is_seq_concat_vars(terms: &TermStore, term: TermId, lhs: &str, rhs: &str) -> bool {
    app_args(terms, term, "seq_concat").is_some_and(|args| {
        args.len() == 2 && is_var_named(terms, args[0], lhs) && is_var_named(terms, args[1], rhs)
    })
}

fn is_seq_concat_empty_left(terms: &TermStore, term: TermId, seq: &str) -> bool {
    app_args(terms, term, "seq_concat").is_some_and(|args| {
        args.len() == 2 && is_seq_empty(terms, args[0]) && is_var_named(terms, args[1], seq)
    })
}

fn is_seq_concat_empty_right(terms: &TermStore, term: TermId, seq: &str) -> bool {
    app_args(terms, term, "seq_concat").is_some_and(|args| {
        args.len() == 2 && is_var_named(terms, args[0], seq) && is_seq_empty(terms, args[1])
    })
}

fn is_seq_concat_singleton_left(terms: &TermStore, term: TermId, value: &str, seq: &str) -> bool {
    app_args(terms, term, "seq_concat").is_some_and(|args| {
        args.len() == 2
            && is_seq_singleton_var(terms, args[0], value)
            && is_var_named(terms, args[1], seq)
    })
}

fn is_seq_concat_singleton_right(terms: &TermStore, term: TermId, seq: &str, value: &str) -> bool {
    app_args(terms, term, "seq_concat").is_some_and(|args| {
        args.len() == 2
            && is_var_named(terms, args[0], seq)
            && is_seq_singleton_var(terms, args[1], value)
    })
}

fn is_logic_some_index(terms: &TermStore, term: TermId, seq: &str, idx: &str) -> bool {
    app_args(terms, term, "logic_Some")
        .is_some_and(|args| args.len() == 1 && is_seq_index_logic(terms, args[0], seq, idx))
}

fn is_logic_none(terms: &TermStore, term: TermId) -> bool {
    app_args(terms, term, "logic_None").is_some_and(<[TermId]>::is_empty)
        || is_var_named(terms, term, "logic_None")
}

fn is_quantifier_consumer_seq_select_bridge_axiom(
    terms: &TermStore,
    body: TermId,
    seq: &str,
    idx: &str,
) -> bool {
    is_eq_between(
        terms,
        body,
        |t| {
            app_args(terms, t, "select").is_some_and(|args| {
                args.len() == 2
                    && is_seq_array_of_var(terms, args[0], seq)
                    && is_plus_of2(
                        terms,
                        args[1],
                        |u| is_seq_offset_of_var(terms, u, seq),
                        |u| is_var_named(terms, u, idx),
                    )
            })
        },
        |t| is_seq_index_logic(terms, t, seq, idx),
    )
}

fn is_quantifier_consumer_seq_len_nonnegative_axiom(
    terms: &TermStore,
    body: TermId,
    seq: &str,
) -> bool {
    app_args(terms, body, "<=").is_some_and(|args| {
        args.len() == 2 && is_int_const(terms, args[0], 0) && is_seq_len_of_var(terms, args[1], seq)
    })
}

fn is_quantifier_consumer_seq_get_in_bounds_axiom(
    terms: &TermStore,
    body: TermId,
    seq: &str,
    idx: &str,
) -> bool {
    is_or_with3(
        terms,
        body,
        |t| {
            is_eq_between(
                terms,
                t,
                |u| is_seq_get(terms, u, seq, idx),
                |u| is_logic_some_index(terms, u, seq, idx),
            )
        },
        // Accept BOTH syntactic forms of the same guard (#seq-inbounds-normalized):
        // the raw `(not (<= 0 i))` / `(not (< i (seq_len s)))` and the
        // NOT-eliminated normalized `(< i 0)` / `(<= (seq_len s) i)` the term
        // store actually holds. The normalized recognizers already exist and the
        // sibling out-of-bounds axiom uses them; matching only the raw form made
        // this axiom unrecognizable, which alone falsified the whole opaque-Seq
        // certificate (it requires EVERY quantified assertion to match). Purely
        // syntactic completion — semantically identical, widens nothing.
        |t| is_not(terms, t, |u| is_le_zero_var(terms, u, idx)) || is_lt_var_zero(terms, t, idx),
        |t| {
            is_not(terms, t, |u| is_lt_var_seq_len(terms, u, idx, seq))
                || is_le_seq_len_var(terms, t, seq, idx)
        },
    )
}

fn is_quantifier_consumer_seq_get_out_of_bounds_axiom(
    terms: &TermStore,
    body: TermId,
    seq: &str,
    idx: &str,
) -> bool {
    is_or_with2(
        terms,
        body,
        |t| {
            is_eq_between(
                terms,
                t,
                |u| is_seq_get(terms, u, seq, idx),
                |u| is_logic_none(terms, u),
            )
        },
        |t| {
            // Both syntactic forms, mirroring the in-bounds axiom
            // (#seq-inbounds-normalized): the store's NOT-elimination turns
            // `(not (< i 0))` into `(<= 0 i)` and `(not (<= (seq_len s) i))`
            // into `(< i (seq_len s))`.
            is_and_with2(
                terms,
                t,
                |u| {
                    is_not(terms, u, |v| is_lt_var_zero(terms, v, idx))
                        || is_le_zero_var(terms, u, idx)
                },
                |u| {
                    is_not(terms, u, |v| is_le_seq_len_var(terms, v, seq, idx))
                        || is_lt_var_seq_len(terms, u, idx, seq)
                },
            )
        },
    )
}

fn is_quantifier_consumer_seq_empty_contains_axiom(
    terms: &TermStore,
    body: TermId,
    value: &str,
) -> bool {
    is_not(terms, body, |t| is_seq_contains_empty(terms, t, value))
}

fn is_quantifier_consumer_seq_contains_push_back_axiom(
    terms: &TermStore,
    body: TermId,
    seq: &str,
    pushed: &str,
    value: &str,
) -> bool {
    is_eq_between(
        terms,
        body,
        |t| is_seq_contains_push_back(terms, t, seq, pushed, value),
        |t| {
            is_or_with2(
                terms,
                t,
                |u| {
                    is_eq_between(
                        terms,
                        u,
                        |v| is_var_named(terms, v, pushed),
                        |v| is_var_named(terms, v, value),
                    )
                },
                |u| is_seq_contains_var(terms, u, seq, value),
            )
        },
    )
}

fn is_quantifier_consumer_seq_concat_len_axiom(
    terms: &TermStore,
    body: TermId,
    lhs: &str,
    rhs: &str,
) -> bool {
    is_eq_between(
        terms,
        body,
        |t| {
            app_args(terms, t, "seq_len")
                .is_some_and(|args| args.len() == 1 && is_seq_concat_vars(terms, args[0], lhs, rhs))
        },
        |t| {
            is_plus_of2(
                terms,
                t,
                |u| is_seq_len_of_var(terms, u, lhs),
                |u| is_seq_len_of_var(terms, u, rhs),
            )
        },
    )
}

fn is_quantifier_consumer_seq_concat_left_index_axiom(
    terms: &TermStore,
    body: TermId,
    lhs: &str,
    rhs: &str,
    idx: &str,
) -> bool {
    is_or_with3(
        terms,
        body,
        |t| {
            is_eq_between(
                terms,
                t,
                |u| is_seq_index_logic_concat(terms, u, lhs, rhs, idx),
                |u| is_seq_index_logic(terms, u, lhs, idx),
            )
        },
        // Both syntactic forms (#seq-inbounds-normalized).
        |t| is_not(terms, t, |u| is_le_zero_var(terms, u, idx)) || is_lt_var_zero(terms, t, idx),
        |t| {
            is_not(terms, t, |u| is_lt_var_seq_len(terms, u, idx, lhs))
                || is_le_seq_len_var(terms, t, lhs, idx)
        },
    )
}

fn is_quantifier_consumer_seq_concat_right_index_axiom(
    terms: &TermStore,
    body: TermId,
    lhs: &str,
    rhs: &str,
    idx: &str,
) -> bool {
    is_or_with3(
        terms,
        body,
        |t| {
            is_eq_between(
                terms,
                t,
                |u| is_seq_index_logic_concat_offset(terms, u, lhs, rhs, idx),
                |u| is_seq_index_logic(terms, u, rhs, idx),
            )
        },
        // Both syntactic forms (#seq-inbounds-normalized).
        |t| is_not(terms, t, |u| is_le_zero_var(terms, u, idx)) || is_lt_var_zero(terms, t, idx),
        |t| {
            is_not(terms, t, |u| is_lt_var_seq_len(terms, u, idx, rhs))
                || is_le_seq_len_var(terms, t, rhs, idx)
        },
    )
}

fn is_quantifier_consumer_seq_concat_assoc_axiom(
    terms: &TermStore,
    body: TermId,
    s1: &str,
    s2: &str,
    s3: &str,
) -> bool {
    is_eq_between(
        terms,
        body,
        |t| {
            app_args(terms, t, "seq_concat").is_some_and(|args| {
                args.len() == 2
                    && is_seq_concat_vars(terms, args[0], s1, s2)
                    && is_var_named(terms, args[1], s3)
            })
        },
        |t| {
            app_args(terms, t, "seq_concat").is_some_and(|args| {
                args.len() == 2
                    && is_var_named(terms, args[0], s1)
                    && is_seq_concat_vars(terms, args[1], s2, s3)
            })
        },
    )
}

fn is_quantifier_consumer_seq_concat_left_identity_axiom(
    terms: &TermStore,
    body: TermId,
    seq: &str,
) -> bool {
    is_eq_between(
        terms,
        body,
        |t| is_var_named(terms, t, seq),
        |t| is_seq_concat_empty_left(terms, t, seq),
    )
}

fn is_quantifier_consumer_seq_concat_right_identity_axiom(
    terms: &TermStore,
    body: TermId,
    seq: &str,
) -> bool {
    is_eq_between(
        terms,
        body,
        |t| is_var_named(terms, t, seq),
        |t| is_seq_concat_empty_right(terms, t, seq),
    )
}

fn is_quantifier_consumer_seq_push_front_definition_axiom(
    terms: &TermStore,
    body: TermId,
    seq: &str,
    value: &str,
) -> bool {
    is_eq_between(
        terms,
        body,
        |t| is_seq_push_front(terms, t, seq, value),
        |t| is_seq_concat_singleton_left(terms, t, value, seq),
    )
}

fn is_quantifier_consumer_seq_push_back_definition_axiom(
    terms: &TermStore,
    body: TermId,
    seq: &str,
    value: &str,
) -> bool {
    is_eq_between(
        terms,
        body,
        |t| is_seq_push_back(terms, t, seq, value),
        |t| is_seq_concat_singleton_right(terms, t, seq, value),
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
