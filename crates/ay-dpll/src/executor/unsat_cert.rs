// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mandatory UNSAT certification at the public verdict boundary.
//!
//! Inner solver lanes return a provisional [`SolveResult::Unsat`].  A public
//! caller may observe that verdict only after either the finished proof has
//! passed the strict checker against the exact authored assertion/assumption
//! query epoch, or a separately sealed exact semantic checker has discharged
//! its deliberately narrow source fragment against the same immutable epoch.

use std::cell::Cell;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermEntryStamp, TermStoreSnapshotStamp};
use ay_core::{Sort as CoreSort, TermId, TermStore as CoreTermStore};
use ay_frontend::{CheckedProjectionBinding, ProjectionBindingRequest, SourceContextStamp};
use ay_proof::{AuthenticatedBoolBvUnsatQuery, AuthenticatedBvLiaUnsatQuery};
use num_bigint::BigInt;

mod probe;
pub(in crate::executor) use probe::probe_cert_reject;

use super::{Executor, QuantifierDeadlinePolicy};
use crate::executor::exact_exists_bounds::CheckedExactExistsUnsat;
use crate::executor::exact_forall_exists::CheckedExactForallExistsUnsat;
use crate::executor::proof_resolution::CheckedSatRefutation;
use crate::executor::QueryAuthorityEpoch;
use crate::executor_types::{SolveResult, UnknownOrigin};

thread_local! {
    /// Re-entrancy depth for the deferred-trust discharge.
    ///
    /// The discharge runs nested solves, and those solves reach this same
    /// publication funnel. Admitting the rescue only at depth 0 bounds the
    /// recursion; nested certifications use plain strict checking, which
    /// terminates. See [`Executor::discharge_trust_steps_for_certification`].
    static TRUST_DISCHARGE_DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// Deterministic search allowances for the independent whole-problem
/// re-confirmation used by the context-dependent trust fallback.
///
/// These are the executor's already-calibrated ground-search defaults, made
/// explicit here so this mandatory accepting gate cannot be disabled by the
/// process-wide ground-budget experiment knob. Exhaustion is fail-closed:
/// the fresh solve reports `Unknown(ResourceLimit)` and no certificate is
/// minted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FreshReconfirmationLimits {
    max_conflicts: u64,
    max_decisions: u64,
}

const WHOLE_PROBLEM_RECONFIRMATION_LIMITS: FreshReconfirmationLimits = FreshReconfirmationLimits {
    max_conflicts: Executor::DEFAULT_GROUND_CONFLICT_ALLOWANCE,
    max_decisions: Executor::DEFAULT_GROUND_DECISION_ALLOWANCE,
};

fn tighter_optional_limit(left: Option<u64>, right: Option<u64>) -> Option<u64> {
    match (left, right) {
        (Some(left), Some(right)) => Some(left.min(right)),
        (Some(limit), None) | (None, Some(limit)) => Some(limit),
        (None, None) => None,
    }
}
/// True while a nested deferred-trust discharge solve is in flight.
///
/// Those solves run in a FRESH `Executor` purely to corroborate the outer
/// verdict, and they reach the same publication funnel. Their per-verdict
/// diagnostics describe an INTERNAL probe, not the user's query, and the
/// transcript is a shared stream -- so a probe that fails its own
/// certification must not narrate that on the user's stderr while the OUTER
/// certification goes on to succeed.
pub(crate) fn inside_trust_discharge_solve() -> bool {
    TRUST_DISCHARGE_DEPTH.with(|depth| depth.get()) > 0
}

/// One-shot capability proving that a provisional UNSAT verdict passed one
/// complete exact-query certification lane.
///
/// The tuple field is private to this module.  Consequently, code outside this
/// module can move the capability to the public result boundary but cannot mint
/// one. Ordinary UNSAT uses the strict proof checker; the deliberately separate
/// exact-source variants record independently checked semantic contradictions
/// and must never be reported as strict-proof acceptance.
#[derive(Debug)]
pub(crate) struct UnsatCertificate(UnsatCertificateKind);

#[derive(Debug)]
enum UnsatCertificateKind {
    StrictProof(AuthenticatedUnsatScope),
    CheckedSatRefutation {
        checked: CheckedSatRefutation,
        scope: AuthenticatedUnsatScope,
    },
    CheckedBoolBv(CheckedBoolBvUnsat),
    CheckedBvLia(CheckedBvLiaUnsat),
    DischargedTrust(AuthenticatedUnsatScope),
    CheckedExactExists(CheckedExactExistsUnsat),
    CheckedExactForallExists(CheckedExactForallExistsUnsat),
    CheckedExactClosedForall(CheckedExactClosedForallUnsat),
    CheckedExactForallUfGround(CheckedExactForallUfGroundUnsat),
    CheckedExactFiniteExpansion(CheckedExactFiniteExpansionUnsat),
}

/// Sealed evidence that one authored top-level universal has an exact closed
/// literal instance which evaluates to `false` under fixed theory semantics.
///
/// This is deliberately not a generic "semantic UNSAT" escape hatch.  The
/// sole constructor below independently requires all of the following:
///
/// - the current assumption-free public query and source/declaration epoch;
/// - an exact top-level conjunct of that authored root vector;
/// - a closed Int/Real/BV quantifier-free `forall` using only the
///   literal-witness operator fragment and no declaration-owned canonical
///   operator identity;
/// - exact raw substitution of one constant per binder; and
/// - `EvalValue::Bool(false)` for that exact closed instance.
///
/// The full term-store snapshot plus individual entry stamps make the token
/// fail closed across append, rollback, or numeric-slot reuse.  Its fields are
/// private to this module, so other solver lanes cannot relabel an arbitrary
/// provisional result as this theorem.
#[derive(Debug)]
pub(in crate::executor) struct CheckedExactClosedForallUnsat {
    query_epoch: QueryAuthorityEpoch,
    /// `SourceContextStamp` is also the declaration/scope revision: any push,
    /// pop, declaration, definition, or reset retires this evidence.
    source_declaration_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[TermEntryStamp]>,
    forall_id: TermId,
    forall_entry: TermEntryStamp,
    body: TermId,
    body_entry: TermEntryStamp,
    literals: Box<[TermId]>,
    literal_entries: Box<[TermEntryStamp]>,
    exact_instance: TermId,
    exact_instance_entry: TermEntryStamp,
    interpreted_operators: Box<[String]>,
    term_snapshot: TermStoreSnapshotStamp,
}

/// Sealed source theorem for one exact authored `forall` instance whose
/// elementary ground consequence contradicts an authored UF-value pin.
///
/// This is deliberately narrower than a ground-solver fallback.  The sole
/// constructor below accepts exactly one Int binder, a lower bound on one
/// unary Int->Int ordinary source UF at an affine argument `x + k`, and an
/// authored equality pin for that same declaration at one literal point.  It
/// derives the unique literal witness, performs raw capture-safe substitution,
/// and checks `pinned_value < lower_bound` after independently normalizing only
/// Int literals and `+`/`-` ground arithmetic.  No raw UNSAT verdict, proof
/// `Generic` leaf, transformed assertion, or model evaluation participates.
#[derive(Debug)]
pub(in crate::executor) struct CheckedExactForallUfGroundUnsat {
    query_epoch: QueryAuthorityEpoch,
    source_declaration_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[TermEntryStamp]>,
    forall_id: TermId,
    forall_entry: TermEntryStamp,
    body: TermId,
    body_entry: TermEntryStamp,
    bound: TermId,
    bound_entry: TermEntryStamp,
    pin: TermId,
    pin_entry: TermEntryStamp,
    witness: TermId,
    witness_entry: TermEntryStamp,
    exact_instance: TermId,
    exact_instance_entry: TermEntryStamp,
    uf_binding: CheckedProjectionBinding,
    interpreted_operators: Box<[String]>,
    contradiction: ExactForallUfGroundContradiction,
    term_snapshot: TermStoreSnapshotStamp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExactForallUfGroundContradiction {
    point: BigInt,
    lower_bound: BigInt,
    pinned_value: BigInt,
}

const EXACT_FORALL_UF_GROUND_MAX_ROOTS: usize = 256;

/// Normalize the complete audited ground-Int fragment used by the theorem.
/// Any variable, UF application, multiplication, division, `let`, `ite`, or
/// future operator declines rather than inheriting solver preprocessing.
fn exact_ground_int_value(
    terms: &CoreTermStore,
    term: TermId,
    remaining: &mut usize,
) -> Option<BigInt> {
    if *remaining == 0 || terms.entry_stamp(term).is_none() || terms.sort(term) != &CoreSort::Int {
        return None;
    }
    *remaining -= 1;
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) => Some(value.clone()),
        TermData::App(Symbol::Named(operator), args) if operator == "+" && !args.is_empty() => {
            let mut value = BigInt::from(0);
            for &arg in args {
                value += exact_ground_int_value(terms, arg, remaining)?;
            }
            Some(value)
        }
        TermData::App(Symbol::Named(operator), args) if operator == "-" && !args.is_empty() => {
            let mut values = args.iter();
            let first = exact_ground_int_value(terms, *values.next()?, remaining)?;
            if args.len() == 1 {
                return Some(-first);
            }
            let mut value = first;
            for &arg in values {
                value -= exact_ground_int_value(terms, arg, remaining)?;
            }
            Some(value)
        }
        _ => None,
    }
}

/// Recover `coefficient * bound + offset` from the equally narrow source
/// fragment.  The theorem accepts the result only when `coefficient == 1`, so
/// non-surjective maps such as `2*x` can never borrow whole-domain authority.
fn exact_affine_int_in_bound(
    terms: &CoreTermStore,
    term: TermId,
    bound: TermId,
    remaining: &mut usize,
) -> Option<(BigInt, BigInt)> {
    if *remaining == 0 || terms.entry_stamp(term).is_none() || terms.sort(term) != &CoreSort::Int {
        return None;
    }
    *remaining -= 1;
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) => Some((BigInt::from(0), value.clone())),
        TermData::Var(_, _) if term == bound => Some((BigInt::from(1), BigInt::from(0))),
        TermData::App(Symbol::Named(operator), args) if operator == "+" && !args.is_empty() => {
            let mut coefficient = BigInt::from(0);
            let mut offset = BigInt::from(0);
            for &arg in args {
                let (arg_coefficient, arg_offset) =
                    exact_affine_int_in_bound(terms, arg, bound, remaining)?;
                coefficient += arg_coefficient;
                offset += arg_offset;
            }
            Some((coefficient, offset))
        }
        TermData::App(Symbol::Named(operator), args) if operator == "-" && !args.is_empty() => {
            let mut values = args.iter();
            let (mut coefficient, mut offset) =
                exact_affine_int_in_bound(terms, *values.next()?, bound, remaining)?;
            if args.len() == 1 {
                return Some((-coefficient, -offset));
            }
            for &arg in values {
                let (arg_coefficient, arg_offset) =
                    exact_affine_int_in_bound(terms, arg, bound, remaining)?;
                coefficient -= arg_coefficient;
                offset -= arg_offset;
            }
            Some((coefficient, offset))
        }
        _ => None,
    }
}

/// Recover the sole exact `Var` identity carrying a binder's source name.
/// Quantifier metadata stores names and sorts, while native construction can
/// still place two distinct same-named `Var` nodes in one term store.  A name
/// match is therefore never authority: ambiguity, a missing occurrence, an
/// ill-sorted occurrence, a nested binder, or a future term form all decline.
fn exact_unique_named_int_var(terms: &CoreTermStore, root: TermId, name: &str) -> Option<TermId> {
    let mut remaining = EXACT_CLOSED_FORALL_WORK_LIMIT;
    let mut seen = HashSet::default();
    let mut stack = vec![root];
    let mut found = None;
    while let Some(term) = stack.pop() {
        if remaining == 0 || terms.entry_stamp(term).is_none() {
            return None;
        }
        remaining -= 1;
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Var(candidate, _) if candidate == name => {
                if terms.sort(term) != &CoreSort::Int || found.is_some_and(|prior| prior != term) {
                    return None;
                }
                found = Some(term);
            }
            TermData::Var(_, _) | TermData::Const(_) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.extend([*condition, *then_term, *else_term]);
            }
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return None,
            _ => return None,
        }
    }
    found
}

fn exact_unary_int_uf_term(terms: &CoreTermStore, term: TermId) -> Option<(Symbol, TermId)> {
    if terms.entry_stamp(term).is_none() || terms.sort(term) != &CoreSort::Int {
        return None;
    }
    let TermData::App(symbol, args) = terms.get(term) else {
        return None;
    };
    let [argument] = args.as_slice() else {
        return None;
    };
    (terms.entry_stamp(*argument).is_some() && terms.sort(*argument) == &CoreSort::Int)
        .then(|| (symbol.clone(), *argument))
}

/// Extract the exact lower-bound atom `f(arg) >= literal` (including only its
/// canonical spelling-equivalent `literal <= f(arg)`).
fn exact_int_uf_lower_bound(
    terms: &CoreTermStore,
    term: TermId,
    remaining: &mut usize,
) -> Option<(Symbol, TermId, BigInt)> {
    if *remaining == 0 || terms.entry_stamp(term).is_none() || terms.sort(term) != &CoreSort::Bool {
        return None;
    }
    *remaining -= 1;
    let TermData::App(Symbol::Named(operator), args) = terms.get(term) else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    match operator.as_str() {
        ">=" => {
            let (symbol, argument) = exact_unary_int_uf_term(terms, *left)?;
            let lower = exact_ground_int_value(terms, *right, remaining)?;
            Some((symbol, argument, lower))
        }
        "<=" => {
            let lower = exact_ground_int_value(terms, *left, remaining)?;
            let (symbol, argument) = exact_unary_int_uf_term(terms, *right)?;
            Some((symbol, argument, lower))
        }
        _ => None,
    }
}

/// Extract one exact authored equality `f(literal_point) = literal_value`.
fn exact_int_uf_pin(
    terms: &CoreTermStore,
    term: TermId,
    remaining: &mut usize,
) -> Option<(Symbol, BigInt, BigInt)> {
    if *remaining == 0 || terms.entry_stamp(term).is_none() || terms.sort(term) != &CoreSort::Bool {
        return None;
    }
    *remaining -= 1;
    let TermData::App(Symbol::Named(operator), args) = terms.get(term) else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    if operator != "=" {
        return None;
    }
    if let Some((symbol, argument)) = exact_unary_int_uf_term(terms, *left) {
        let point = exact_ground_int_value(terms, argument, remaining)?;
        let value = exact_ground_int_value(terms, *right, remaining)?;
        return Some((symbol, point, value));
    }
    let (symbol, argument) = exact_unary_int_uf_term(terms, *right)?;
    let point = exact_ground_int_value(terms, argument, remaining)?;
    let value = exact_ground_int_value(terms, *left, remaining)?;
    Some((symbol, point, value))
}

fn exact_forall_uf_source_contradiction(
    terms: &CoreTermStore,
    forall_id: TermId,
    expected_bound: TermId,
    pin: TermId,
    witness: TermId,
    expected_symbol: &Symbol,
) -> Option<(TermId, ExactForallUfGroundContradiction)> {
    if terms.entry_stamp(forall_id).is_none()
        || terms.sort(forall_id) != &CoreSort::Bool
        || crate::ematching::contains_quantifier(terms, pin)
    {
        return None;
    }
    let TermData::Forall(vars, body, _) = terms.get(forall_id) else {
        return None;
    };
    let [(bound, CoreSort::Int)] = vars.as_slice() else {
        return None;
    };
    if crate::ematching::contains_quantifier(terms, *body) {
        return None;
    }

    let mut remaining = EXACT_CLOSED_FORALL_WORK_LIMIT;
    let (body_symbol, argument, lower_bound) =
        exact_int_uf_lower_bound(terms, *body, &mut remaining)?;
    let bound_term = exact_unique_named_int_var(terms, argument, bound)?;
    if bound_term != expected_bound {
        return None;
    }
    let (coefficient, offset) =
        exact_affine_int_in_bound(terms, argument, bound_term, &mut remaining)?;
    if coefficient != BigInt::from(1) || &body_symbol != expected_symbol {
        return None;
    }
    let (pin_symbol, point, pinned_value) = exact_int_uf_pin(terms, pin, &mut remaining)?;
    if &pin_symbol != expected_symbol || pinned_value >= lower_bound {
        return None;
    }
    let witness_value = exact_ground_int_value(terms, witness, &mut remaining)?;
    if witness_value != point.clone() - offset {
        return None;
    }
    Some((
        *body,
        ExactForallUfGroundContradiction {
            point,
            lower_bound,
            pinned_value,
        },
    ))
}

fn exact_forall_uf_instance_contradiction(
    terms: &CoreTermStore,
    exact_instance: TermId,
    pin: TermId,
    expected_symbol: &Symbol,
) -> Option<ExactForallUfGroundContradiction> {
    if crate::ematching::contains_quantifier(terms, exact_instance)
        || crate::ematching::contains_quantifier(terms, pin)
    {
        return None;
    }
    let mut remaining = EXACT_CLOSED_FORALL_WORK_LIMIT;
    let (instance_symbol, argument, lower_bound) =
        exact_int_uf_lower_bound(terms, exact_instance, &mut remaining)?;
    let point = exact_ground_int_value(terms, argument, &mut remaining)?;
    let (pin_symbol, pin_point, pinned_value) = exact_int_uf_pin(terms, pin, &mut remaining)?;
    if &instance_symbol != expected_symbol
        || &pin_symbol != expected_symbol
        || point != pin_point
        || pinned_value >= lower_bound
    {
        return None;
    }
    Some(ExactForallUfGroundContradiction {
        point,
        lower_bound,
        pinned_value,
    })
}

impl CheckedExactForallUfGroundUnsat {
    fn is_current(&self, executor: &Executor) -> bool {
        if crate::executor::model::scoped_term_evaluation_override_active()
            || !self
                .query_epoch
                .is_same_epoch(&executor.query_authority_epoch)
            || self.source_declaration_stamp != executor.ctx.source_context_stamp()
            || self.roots.as_ref() != executor.ctx.assertions.as_slice()
            || self.term_snapshot != executor.ctx.terms.snapshot_stamp()
            || !CheckedExactClosedForallUnsat::entries_are_current(
                &executor.ctx.terms,
                &self.roots,
                &self.root_entries,
            )
            || executor.ctx.terms.entry_stamp(self.forall_id) != Some(self.forall_entry)
            || executor.ctx.terms.entry_stamp(self.body) != Some(self.body_entry)
            || executor.ctx.terms.entry_stamp(self.bound) != Some(self.bound_entry)
            || executor.ctx.terms.entry_stamp(self.pin) != Some(self.pin_entry)
            || executor.ctx.terms.entry_stamp(self.witness) != Some(self.witness_entry)
            || executor.ctx.terms.entry_stamp(self.exact_instance)
                != Some(self.exact_instance_entry)
            || !authored_top_level_conjunct_contains(
                &executor.ctx.terms,
                &self.roots,
                self.forall_id,
            )
            || !authored_top_level_conjunct_contains(&executor.ctx.terms, &self.roots, self.pin)
            || executor
                .ctx
                .symbol_iter()
                .any(|(_, info)| info.term == Some(self.bound))
            || !executor
                .ctx
                .projection_binding_still_current(&self.uf_binding)
            || !exact_operator_identities_are_unshadowed(&executor.ctx, &self.interpreted_operators)
        {
            return false;
        }

        let Some((body, source_contradiction)) = exact_forall_uf_source_contradiction(
            &executor.ctx.terms,
            self.forall_id,
            self.bound,
            self.pin,
            self.witness,
            self.uf_binding.symbol(),
        ) else {
            return false;
        };
        body == self.body
            && source_contradiction == self.contradiction
            && exact_forall_uf_instance_contradiction(
                &executor.ctx.terms,
                self.exact_instance,
                self.pin,
                self.uf_binding.symbol(),
            ) == Some(self.contradiction.clone())
    }
}

/// Sealed source theorem for one exact finite-BV expansion whose complete
/// ground replacement contains a directly checkable contradiction.
///
/// The producer-side expansion record is authenticated separately by the
/// quantifier result mapper.  This token never retargets that record to the
/// public roots: its private constructor independently re-expands the exact
/// immutable public-query roots and accepts only a literal `false` conjunct or
/// two equalities assigning the identical ground term distinct exact scalar
/// literals.  Thus no raw ground-solver verdict, proof `Generic` step, or
/// transformed assertion is authority for the public UNSAT.
#[derive(Debug)]
pub(in crate::executor) struct CheckedExactFiniteExpansionUnsat {
    query_epoch: QueryAuthorityEpoch,
    source_declaration_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[TermEntryStamp]>,
    expanded_roots: Box<[TermId]>,
    expanded_root_entries: Box<[TermEntryStamp]>,
    contradiction: ExactFiniteExpansionContradiction,
    interpreted_operators: Box<[String]>,
    term_snapshot: TermStoreSnapshotStamp,
}

/// Recover every canonical head whose fixed theory meaning may be used
/// while substituting and simplifying the exact authored roots.
///
/// This deliberately derives the set from the complete root DAG instead of a
/// hand-maintained operator list: `subst_vars` has simplifying constructors for
/// arithmetic, arrays, and the full BV family, and a future canonical operator
/// added there must automatically join this ownership firewall.  `and` is also
/// included because finite universal expansion synthesizes that head even when
/// it was absent from the source.
fn exact_finite_expansion_interpreted_operators(
    terms: &CoreTermStore,
    roots: &[TermId],
) -> Option<Vec<String>> {
    let mut remaining = EXACT_CLOSED_FORALL_WORK_LIMIT;
    let mut seen = HashSet::default();
    let mut stack = roots.to_vec();
    let mut operators = vec!["and".to_string()];
    while let Some(term) = stack.pop() {
        if remaining == 0 || terms.entry_stamp(term).is_none() {
            return None;
        }
        remaining -= 1;
        if !seen.insert(term) {
            continue;
        }
        if let TermData::App(symbol, _) = terms.get(term) {
            let name = symbol.name();
            if ay_frontend::is_canonical_theory_operator_identity(name) {
                operators.push(name.to_string());
            }
        }
        stack.extend(terms.children(term));
    }
    operators.sort_unstable();
    operators.dedup();
    Some(operators)
}

/// Validate the binder-sensitive part of the quantified body before invoking
/// the production expander.
///
/// `subst_vars` indexes substitutions by core name.  A malformed low-level
/// TermStore could otherwise give one binder name multiple Var identities or a
/// Var of the wrong sort, causing the replay to replace a term that is not a
/// well-sorted occurrence of that binder.  Normal elaboration prevents this;
/// the certificate checker enforces it independently because low-level Context
/// mutation is part of the repository's adversarial test model.
fn exact_finite_binder_occurrences_are_well_sorted(
    terms: &CoreTermStore,
    body: TermId,
    binders: &[(String, CoreSort)],
) -> bool {
    let mut binder_sorts: HashMap<&str, &CoreSort> = HashMap::default();
    for (name, sort) in binders {
        if name.is_empty()
            || !matches!(sort, CoreSort::BitVec(width) if width.width > 0)
            || binder_sorts.insert(name.as_str(), sort).is_some()
        {
            return false;
        }
    }

    let mut remaining = EXACT_CLOSED_FORALL_WORK_LIMIT;
    let mut matched_var_ids: HashMap<String, u32> = HashMap::default();
    let mut seen = HashSet::default();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        if remaining == 0 || terms.entry_stamp(term).is_none() {
            return false;
        }
        remaining -= 1;
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Const(constant) => {
                let well_sorted = match (constant, terms.sort(term)) {
                    (Constant::Bool(_), CoreSort::Bool)
                    | (Constant::Int(_), CoreSort::Int)
                    | (Constant::Rational(_), CoreSort::Real)
                    | (Constant::String(_), CoreSort::String) => true,
                    (
                        Constant::BitVec { width, .. },
                        CoreSort::BitVec(ay_core::BitVecSort { width: sort_width }),
                    ) => width == sort_width && *width > 0,
                    _ => false,
                };
                if !well_sorted {
                    return false;
                }
            }
            TermData::Var(name, id) => {
                if let Some(expected_sort) = binder_sorts.get(name.as_str()) {
                    if terms.sort(term) != *expected_sort {
                        return false;
                    }
                    match matched_var_ids.get(name) {
                        Some(seen_id) if seen_id != id => return false,
                        Some(_) => {}
                        None => {
                            matched_var_ids.insert(name.clone(), *id);
                        }
                    }
                }
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => {
                if terms.sort(term) != &CoreSort::Bool || terms.sort(*inner) != &CoreSort::Bool {
                    return false;
                }
                stack.push(*inner);
            }
            TermData::Ite(condition, then_term, else_term) => {
                if terms.sort(*condition) != &CoreSort::Bool
                    || terms.sort(*then_term) != terms.sort(*else_term)
                    || terms.sort(term) != terms.sort(*then_term)
                {
                    return false;
                }
                stack.extend([*condition, *then_term, *else_term]);
            }
            // The ordinary expander has capture-aware Let support, but the
            // exact source token intentionally keeps a smaller auditable
            // fragment. Parsed lets are normally elaborated away already.
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return false,
            _ => return false,
        }
    }
    true
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExactFiniteExpansionContradiction {
    FalseConjunct(TermId),
    DistinctScalarAssignments {
        subject: TermId,
        first: TermId,
        second: TermId,
    },
}

fn exact_ground_scalar_value(
    terms: &CoreTermStore,
    term: TermId,
    remaining: &mut usize,
) -> Option<Constant> {
    if *remaining == 0 || terms.entry_stamp(term).is_none() {
        return None;
    }
    *remaining -= 1;
    match terms.get(term) {
        TermData::Const(
            constant @ (Constant::Bool(_)
            | Constant::Int(_)
            | Constant::Rational(_)
            | Constant::BitVec { .. }),
        ) => match (constant, terms.sort(term)) {
            (Constant::Bool(_), CoreSort::Bool)
            | (Constant::Int(_), CoreSort::Int)
            | (Constant::Rational(_), CoreSort::Real) => Some(constant.clone()),
            (
                Constant::BitVec { width, .. },
                CoreSort::BitVec(ay_core::BitVecSort { width: sort_width }),
            ) if width == sort_width => Some(constant.clone()),
            _ => None,
        },
        // `bv2int`/`ubv_to_int` elaborate to the canonical unsigned
        // `bv2nat` core operator. Quantifier substitution deliberately uses a
        // raw fallback for this node, so independently normalize its literal
        // argument here rather than assuming preprocessing folded it.
        TermData::App(Symbol::Named(operator), args)
            if operator == "bv2nat"
                && args.len() == 1
                && terms.sort(term) == &CoreSort::Int
                && matches!(terms.sort(args[0]), CoreSort::BitVec(_)) =>
        {
            match exact_ground_scalar_value(terms, args[0], remaining)? {
                Constant::BitVec { value, .. } => Some(Constant::Int(value)),
                _ => None,
            }
        }
        TermData::App(Symbol::Named(operator), args)
            if matches!(operator.as_str(), "+" | "-" | "*") && !args.is_empty() =>
        {
            let mut values = args
                .iter()
                .map(|&arg| exact_ground_scalar_value(terms, arg, remaining));
            let first = values.next()??;
            match first {
                Constant::Int(mut value) if terms.sort(term) == &CoreSort::Int => {
                    if operator == "-" && args.len() == 1 {
                        return Some(Constant::Int(-value));
                    }
                    for next in values {
                        let Constant::Int(next) = next? else {
                            return None;
                        };
                        match operator.as_str() {
                            "+" => value += next,
                            "-" => value -= next,
                            "*" => value *= next,
                            _ => return None,
                        }
                    }
                    Some(Constant::Int(value))
                }
                Constant::Rational(mut value) if terms.sort(term) == &CoreSort::Real => {
                    if operator == "-" && args.len() == 1 {
                        return Some(Constant::Rational((-value.0).into()));
                    }
                    for next in values {
                        let Constant::Rational(next) = next? else {
                            return None;
                        };
                        match operator.as_str() {
                            "+" => value.0 += next.0,
                            "-" => value.0 -= next.0,
                            "*" => value.0 *= next.0,
                            _ => return None,
                        }
                    }
                    Some(Constant::Rational(value))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn collect_exact_ground_conjuncts(
    terms: &CoreTermStore,
    term: TermId,
    remaining: &mut usize,
    conjuncts: &mut Vec<TermId>,
) -> bool {
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if *remaining == 0
            || terms.entry_stamp(current).is_none()
            || terms.sort(current) != &CoreSort::Bool
        {
            return false;
        }
        *remaining -= 1;
        match terms.get(current) {
            TermData::App(Symbol::Named(operator), args) if operator == "and" => {
                stack.extend(args.iter().rev().copied());
            }
            TermData::Forall(..) | TermData::Exists(..) => return false,
            _ => conjuncts.push(current),
        }
    }
    true
}

/// Recognize only two elementary, model-independent ground contradictions.
/// The bounded walk is intentionally much smaller than a ground solver: this
/// is a theorem checker, not a second heuristic decision procedure.
fn exact_finite_expansion_ground_contradiction(
    terms: &CoreTermStore,
    expanded_roots: &[TermId],
) -> Option<ExactFiniteExpansionContradiction> {
    let mut remaining = EXACT_CLOSED_FORALL_WORK_LIMIT;
    let mut conjuncts = Vec::new();
    for &root in expanded_roots {
        if !collect_exact_ground_conjuncts(terms, root, &mut remaining, &mut conjuncts) {
            return None;
        }
    }

    let mut assignments: HashMap<TermId, (TermId, Constant)> = HashMap::default();
    for conjunct in conjuncts {
        if matches!(terms.get(conjunct), TermData::Const(Constant::Bool(false))) {
            return Some(ExactFiniteExpansionContradiction::FalseConjunct(conjunct));
        }
        let TermData::App(Symbol::Named(operator), args) = terms.get(conjunct) else {
            continue;
        };
        if operator != "=" || args.len() != 2 || terms.sort(args[0]) != terms.sort(args[1]) {
            continue;
        }
        let left_literal = exact_ground_scalar_value(terms, args[0], &mut remaining);
        let right_literal = exact_ground_scalar_value(terms, args[1], &mut remaining);
        if let (Some(left), Some(right)) = (&left_literal, &right_literal) {
            if left != right {
                return Some(
                    ExactFiniteExpansionContradiction::DistinctScalarAssignments {
                        subject: args[0],
                        first: args[0],
                        second: args[1],
                    },
                );
            }
            continue;
        }
        let (subject, literal, value) = match (left_literal, right_literal) {
            (Some(value), None) => (args[1], args[0], value),
            (None, Some(value)) => (args[0], args[1], value),
            _ => continue,
        };
        if let Some((prior_literal, prior_value)) = assignments.get(&subject) {
            if terms.sort(*prior_literal) == terms.sort(literal) && *prior_value != value {
                return Some(
                    ExactFiniteExpansionContradiction::DistinctScalarAssignments {
                        subject,
                        first: *prior_literal,
                        second: literal,
                    },
                );
            }
        } else {
            assignments.insert(subject, (literal, value));
        }
    }
    None
}

impl CheckedExactFiniteExpansionUnsat {
    fn is_current(&self, executor: &Executor) -> bool {
        !crate::executor::model::scoped_term_evaluation_override_active()
            && self
                .query_epoch
                .is_same_epoch(&executor.query_authority_epoch)
            && self.source_declaration_stamp == executor.ctx.source_context_stamp()
            && self.roots.as_ref() == executor.ctx.assertions.as_slice()
            && self.term_snapshot == executor.ctx.terms.snapshot_stamp()
            && CheckedExactClosedForallUnsat::entries_are_current(
                &executor.ctx.terms,
                &self.roots,
                &self.root_entries,
            )
            && CheckedExactClosedForallUnsat::entries_are_current(
                &executor.ctx.terms,
                &self.expanded_roots,
                &self.expanded_root_entries,
            )
            && exact_operator_identities_are_unshadowed(&executor.ctx, &self.interpreted_operators)
            && exact_finite_expansion_interpreted_operators(&executor.ctx.terms, &self.roots)
                .is_some_and(|operators| {
                    operators.as_slice() == self.interpreted_operators.as_ref()
                })
            && exact_finite_expansion_ground_contradiction(
                &executor.ctx.terms,
                &self.expanded_roots,
            ) == Some(self.contradiction)
    }
}

impl CheckedExactClosedForallUnsat {
    fn entries_are_current(
        terms: &CoreTermStore,
        roots: &[TermId],
        entries: &[TermEntryStamp],
    ) -> bool {
        roots.len() == entries.len()
            && entries
                .iter()
                .copied()
                .map(Some)
                .eq(roots.iter().map(|&root| terms.entry_stamp(root)))
    }

    pub(in crate::executor) fn is_current(&self, executor: &Executor) -> bool {
        if crate::executor::model::scoped_term_evaluation_override_active()
            || !self
                .query_epoch
                .is_same_epoch(&executor.query_authority_epoch)
            || self.source_declaration_stamp != executor.ctx.source_context_stamp()
            || self.roots.as_ref() != executor.ctx.assertions.as_slice()
            || self.term_snapshot != executor.ctx.terms.snapshot_stamp()
            || !Self::entries_are_current(&executor.ctx.terms, &self.roots, &self.root_entries)
            || executor.ctx.terms.entry_stamp(self.forall_id) != Some(self.forall_entry)
            || executor.ctx.terms.entry_stamp(self.body) != Some(self.body_entry)
            || !Self::entries_are_current(
                &executor.ctx.terms,
                &self.literals,
                &self.literal_entries,
            )
            || executor.ctx.terms.entry_stamp(self.exact_instance)
                != Some(self.exact_instance_entry)
            || !authored_top_level_conjunct_contains(
                &executor.ctx.terms,
                &self.roots,
                self.forall_id,
            )
        {
            return false;
        }

        let Some((vars, body)) =
            crate::executor::quantifier_loop::closed_quantifier_free_forall_literal_parts(
                &executor.ctx.terms,
                self.forall_id,
            )
        else {
            return false;
        };
        if body != self.body
            || vars.len() != self.literals.len()
            || executor.ctx.terms.sort(self.forall_id) != &CoreSort::Bool
            || executor.ctx.terms.sort(body) != &CoreSort::Bool
            || vars
                .iter()
                .map(|(name, _)| name)
                .collect::<HashSet<_>>()
                .len()
                != vars.len()
            || !vars
                .iter()
                .zip(self.literals.iter())
                .all(|((_, sort), &literal)| {
                    exact_scalar_literal_has_sort(&executor.ctx.terms, literal, sort)
                })
        {
            return false;
        }

        let Some(operators) = exact_closed_forall_operators(&executor.ctx.terms, body) else {
            return false;
        };
        operators.as_slice() == self.interpreted_operators.as_ref()
            && exact_operator_identities_are_unshadowed(&executor.ctx, &operators)
            && crate::executor::model::with_isolated_eval_memo(|| {
                matches!(
                    executor.evaluate_term(
                        &crate::executor::model::Model::empty(),
                        self.exact_instance,
                    ),
                    crate::executor::model::EvalValue::Bool(false)
                )
            })
    }
}

/// Bounded source walk used only by the exact closed-forall token.
const EXACT_CLOSED_FORALL_WORK_LIMIT: usize = 100_000;

fn authored_top_level_conjunct_contains(
    terms: &CoreTermStore,
    roots: &[TermId],
    target: TermId,
) -> bool {
    let mut remaining = EXACT_CLOSED_FORALL_WORK_LIMIT;
    let mut seen = HashSet::default();
    let mut stack = roots.to_vec();
    while let Some(term) = stack.pop() {
        if remaining == 0 {
            return false;
        }
        remaining -= 1;
        if !seen.insert(term) {
            continue;
        }
        if terms.entry_stamp(term).is_none() || terms.sort(term) != &CoreSort::Bool {
            return false;
        }
        if term == target {
            return true;
        }
        if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
            if name == "and" {
                if !args.iter().all(|&arg| {
                    terms.entry_stamp(arg).is_some() && terms.sort(arg) == &CoreSort::Bool
                }) {
                    return false;
                }
                stack.extend(args.iter().copied());
            }
        }
    }
    false
}

fn exact_scalar_literal_has_sort(terms: &CoreTermStore, literal: TermId, sort: &CoreSort) -> bool {
    if terms.entry_stamp(literal).is_none() || terms.sort(literal) != sort {
        return false;
    }
    match (sort, terms.get(literal)) {
        (CoreSort::Int, TermData::Const(Constant::Int(_)))
        | (CoreSort::Real, TermData::Const(Constant::Rational(_))) => true,
        (CoreSort::BitVec(bitvec_sort), TermData::Const(Constant::BitVec { width, .. })) => {
            bitvec_sort.width == *width
        }
        _ => false,
    }
}

/// Recover the exact canonical application identities used by the body.
/// Special core nodes (`Not`, `Ite`, and `Let`) cannot be confused with a
/// declaration-owned application.  Any other node kind is outside this token.
fn exact_closed_forall_operators(terms: &CoreTermStore, body: TermId) -> Option<Vec<String>> {
    let mut remaining = EXACT_CLOSED_FORALL_WORK_LIMIT;
    let mut seen = HashSet::default();
    let mut stack = vec![body];
    let mut operators = vec!["and".to_string()];
    while let Some(term) = stack.pop() {
        if remaining == 0 {
            return None;
        }
        remaining -= 1;
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Var(..) | TermData::Const(..) => {}
            TermData::App(Symbol::Named(name), args) => {
                if !crate::executor::quantifier_loop::is_literal_witness_operator(name) {
                    return None;
                }
                operators.push(name.clone());
                stack.extend(args.iter().copied());
            }
            TermData::App(..) => return None,
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.push(*condition);
                stack.push(*then_term);
                stack.push(*else_term);
            }
            TermData::Let(bindings, let_body) => {
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*let_body);
            }
            _ => return None,
        }
    }
    operators.sort_unstable();
    operators.dedup();
    Some(operators)
}

fn exact_operator_identities_are_unshadowed(
    ctx: &ay_frontend::Context,
    operators: &[String],
) -> bool {
    ctx.symbol_iter().all(|(surface, info)| {
        let identity = ctx.symbol_identity_name(surface, info);
        !operators.iter().any(|operator| operator == identity)
    })
}

/// Exact public-query scope retained by proof-based certification lanes.
///
/// A proof check is a statement about one immutable authored obligation, not
/// about a bare epoch counter. Retaining the full scope lets the final one-shot
/// consumer reject any source, root, assumption, or declared-extension change
/// that occurs after the checker returns.
#[derive(Debug)]
struct AuthenticatedUnsatScope {
    authority_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    assertions: Box<[TermId]>,
    assertion_entries: Box<[TermEntryStamp]>,
    assumptions: Box<[TermId]>,
    assumption_entries: Box<[TermEntryStamp]>,
    declared_extension: Box<[TermId]>,
    declared_extension_entries: Box<[TermEntryStamp]>,
    declared_extension_objectives: Option<Box<[ay_frontend::Objective]>>,
    declared_extension_objective_entries: Option<Box<[TermEntryStamp]>>,
    solver_assumptions: Option<Box<[TermId]>>,
    solver_assumption_entries: Option<Box<[TermEntryStamp]>>,
}

impl AuthenticatedUnsatScope {
    fn capture_entries(executor: &Executor, roots: &[TermId]) -> Option<Box<[TermEntryStamp]>> {
        roots
            .iter()
            .map(|&root| executor.ctx.terms.entry_stamp(root))
            .collect::<Option<Vec<_>>>()
            .map(Vec::into_boxed_slice)
    }

    fn entries_are_current(
        &self,
        executor: &Executor,
        roots: &[TermId],
        entries: &[TermEntryStamp],
    ) -> bool {
        entries.len() == roots.len()
            && entries.iter().copied().map(Some).eq(roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
    }

    fn capture(
        executor: &Executor,
        epoch: &UnsatQueryEpoch,
        assumptions: &[TermId],
    ) -> Option<Self> {
        let solver_assumptions: Option<Box<[TermId]>> =
            executor.last_assumptions.as_deref().map(Box::from);
        let solver_assumption_entries = match solver_assumptions.as_deref() {
            Some(roots) => Some(Self::capture_entries(executor, roots)?),
            None => None,
        };
        Some(Self {
            authority_epoch: epoch.authority_epoch.clone(),
            source_context_stamp: epoch.source_context_stamp.clone(),
            assertions: epoch.assertions.as_slice().into(),
            assertion_entries: epoch.assertion_entries.clone().into_boxed_slice(),
            assumptions: assumptions.into(),
            assumption_entries: epoch.assumption_entries.clone()?.into_boxed_slice(),
            declared_extension: epoch.declared_extension.as_slice().into(),
            declared_extension_entries: epoch.declared_extension_entries.clone().into_boxed_slice(),
            declared_extension_objectives: epoch
                .declared_extension_objectives
                .as_deref()
                .map(Box::from),
            declared_extension_objective_entries: epoch
                .declared_extension_objective_entries
                .as_deref()
                .map(Box::from),
            solver_assumptions,
            solver_assumption_entries,
        })
    }

    fn is_current(&self, executor: &Executor) -> bool {
        let Some(epoch) = executor.unsat_query_epoch.as_ref() else {
            return false;
        };
        self.authority_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.authority_epoch.is_same_epoch(&epoch.authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.source_context_stamp == epoch.source_context_stamp
            && self.assertions.as_ref() == epoch.assertions.as_slice()
            && self.entries_are_current(executor, &self.assertions, &self.assertion_entries)
            && self.assertion_entries.as_ref() == epoch.assertion_entries.as_slice()
            && epoch.assumptions.as_deref() == Some(self.assumptions.as_ref())
            && self.entries_are_current(executor, &self.assumptions, &self.assumption_entries)
            && epoch.assumption_entries.as_deref() == Some(self.assumption_entries.as_ref())
            && self.declared_extension.as_ref() == epoch.declared_extension.as_slice()
            && self.entries_are_current(
                executor,
                &self.declared_extension,
                &self.declared_extension_entries,
            )
            && self
                .declared_extension_entries
                .as_ref()
                .eq(epoch.declared_extension_entries.as_slice())
            && self.declared_extension_objectives.as_deref()
                == epoch.declared_extension_objectives.as_deref()
            && self.declared_extension_objective_entries.as_deref()
                == epoch.declared_extension_objective_entries.as_deref()
            && epoch.declared_extension_provenance_is_current(executor)
            && self.solver_assumptions.as_deref() == executor.last_assumptions.as_deref()
            && match (
                self.solver_assumptions.as_deref(),
                self.solver_assumption_entries.as_deref(),
            ) {
                (Some(roots), Some(entries)) => self.entries_are_current(executor, roots, entries),
                (None, None) => true,
                _ => false,
            }
            && executor
                .proof_problem_assertion_provenance
                .as_ref()
                .is_some_and(|provenance| {
                    provenance.original_problem_assertions == self.assertions.as_ref()
                })
    }
}

/// A source-level Bool/BV refutation bound to one exact public-query scope.
///
/// `bind` is the only constructor: it compares the proof checker's opaque
/// ordered roots with the sealed assertion/assumption vectors once.  Final
/// consumption then needs only the scope-currentness check plus the opaque
/// term-snapshot check; neither component can be retargeted independently.
#[derive(Debug)]
struct CheckedBoolBvUnsat {
    scope: AuthenticatedUnsatScope,
    evidence: AuthenticatedBoolBvUnsatQuery,
}

impl CheckedBoolBvUnsat {
    fn bind(
        scope: AuthenticatedUnsatScope,
        evidence: AuthenticatedBoolBvUnsatQuery,
        terms: &ay_core::TermStore,
        exact_roots: &[TermId],
    ) -> Option<Self> {
        if !scope.declared_extension.is_empty()
            || scope.declared_extension_objectives.is_some()
            || !evidence.is_current_for(terms, exact_roots)
            || !exact_roots.iter().copied().eq(scope
                .assertions
                .iter()
                .chain(scope.assumptions.iter())
                .copied())
        {
            return None;
        }
        Some(Self { scope, evidence })
    }

    fn is_current(&self, executor: &Executor) -> bool {
        self.scope.is_current(executor)
            && self.scope.declared_extension.is_empty()
            && self.scope.declared_extension_objectives.is_none()
            && self.evidence.term_snapshot_is_current(&executor.ctx.terms)
    }
}

/// A source-level mixed Bool/Int/BV semantic refutation bound to one exact
/// public-query scope.
#[derive(Debug)]
struct CheckedBvLiaUnsat {
    scope: AuthenticatedUnsatScope,
    evidence: AuthenticatedBvLiaUnsatQuery,
}

impl CheckedBvLiaUnsat {
    fn bind(
        scope: AuthenticatedUnsatScope,
        evidence: AuthenticatedBvLiaUnsatQuery,
        terms: &ay_core::TermStore,
        exact_roots: &[TermId],
    ) -> Option<Self> {
        if !scope.declared_extension.is_empty()
            || scope.declared_extension_objectives.is_some()
            || !evidence.is_current_for(terms, exact_roots)
            || !exact_roots.iter().copied().eq(scope
                .assertions
                .iter()
                .chain(scope.assumptions.iter())
                .copied())
        {
            return None;
        }
        Some(Self { scope, evidence })
    }

    fn is_current(&self, executor: &Executor) -> bool {
        self.scope.is_current(executor)
            && self.scope.declared_extension.is_empty()
            && self.scope.declared_extension_objectives.is_none()
            && self.evidence.term_snapshot_is_current(&executor.ctx.terms)
    }
}

/// Exact certification class consumed by the SMT-LIB command boundary.
///
/// The one-shot certificate itself cannot remain available after publication,
/// but diagnostics and cross-check policy must not infer its trust class from
/// the bare `Unsat` verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CommandUnsatAdmission {
    StrictProof,
    CheckedSatRefutation,
    CheckedBoolBv,
    CheckedBvLia,
    DischargedTrust,
    CheckedExactExists,
    CheckedExactForallExists,
    CheckedExactClosedForall,
    CheckedExactForallUfGround,
    CheckedExactFiniteExpansion,
}

impl UnsatCertificate {
    fn checked_exact_semantic_is_current(&self, executor: &Executor) -> bool {
        if !executor.exact_plain_hard_unsat_scope_is_current() {
            return false;
        }
        match &self.0 {
            UnsatCertificateKind::CheckedExactExists(evidence) => evidence.is_current(executor),
            UnsatCertificateKind::CheckedExactForallExists(evidence) => {
                evidence.is_current(executor)
            }
            UnsatCertificateKind::CheckedExactClosedForall(evidence) => {
                evidence.is_current(executor)
            }
            UnsatCertificateKind::CheckedExactForallUfGround(evidence) => {
                evidence.is_current(executor)
            }
            UnsatCertificateKind::CheckedExactFiniteExpansion(evidence) => {
                evidence.is_current(executor)
            }
            UnsatCertificateKind::StrictProof(_)
            | UnsatCertificateKind::CheckedSatRefutation { .. }
            | UnsatCertificateKind::CheckedBoolBv(_)
            | UnsatCertificateKind::CheckedBvLia(_)
            | UnsatCertificateKind::DischargedTrust(_) => false,
        }
    }

    pub(crate) fn strict_proof_verified(&self) -> bool {
        matches!(&self.0, UnsatCertificateKind::StrictProof(_))
    }

    pub(crate) fn independently_verified(&self) -> bool {
        matches!(
            &self.0,
            UnsatCertificateKind::CheckedSatRefutation { .. }
                | UnsatCertificateKind::CheckedBoolBv(_)
                | UnsatCertificateKind::CheckedBvLia(_)
                | UnsatCertificateKind::DischargedTrust(_)
        )
    }

    pub(crate) fn exact_semantic_verified(&self) -> bool {
        matches!(
            &self.0,
            UnsatCertificateKind::CheckedExactExists(_)
                | UnsatCertificateKind::CheckedExactForallExists(_)
                | UnsatCertificateKind::CheckedExactClosedForall(_)
                | UnsatCertificateKind::CheckedExactForallUfGround(_)
                | UnsatCertificateKind::CheckedExactFiniteExpansion(_)
        )
    }

    pub(super) fn command_admission(&self) -> CommandUnsatAdmission {
        match &self.0 {
            UnsatCertificateKind::StrictProof(_) => CommandUnsatAdmission::StrictProof,
            UnsatCertificateKind::CheckedSatRefutation { .. } => {
                CommandUnsatAdmission::CheckedSatRefutation
            }
            UnsatCertificateKind::CheckedBoolBv(_) => CommandUnsatAdmission::CheckedBoolBv,
            UnsatCertificateKind::CheckedBvLia(_) => CommandUnsatAdmission::CheckedBvLia,
            UnsatCertificateKind::DischargedTrust(_) => CommandUnsatAdmission::DischargedTrust,
            UnsatCertificateKind::CheckedExactExists(_) => {
                CommandUnsatAdmission::CheckedExactExists
            }
            UnsatCertificateKind::CheckedExactForallExists(_) => {
                CommandUnsatAdmission::CheckedExactForallExists
            }
            UnsatCertificateKind::CheckedExactClosedForall(_) => {
                CommandUnsatAdmission::CheckedExactClosedForall
            }
            UnsatCertificateKind::CheckedExactForallUfGround(_) => {
                CommandUnsatAdmission::CheckedExactForallUfGround
            }
            UnsatCertificateKind::CheckedExactFiniteExpansion(_) => {
                CommandUnsatAdmission::CheckedExactFiniteExpansion
            }
        }
    }
}

/// Exact authenticated inputs for one public decision query.
///
/// The initial pre-elaboration assertion snapshot may be replaced once by the
/// frontend's materialized SMT-LIB 2.7 schematic instances before assumptions
/// are bound. It is immutable after that pre-solve rebind.
#[derive(Debug, Clone)]
pub(super) struct UnsatQueryEpoch {
    authority_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    assertions: Vec<TermId>,
    assertion_entries: Vec<TermEntryStamp>,
    assumptions: Option<Vec<TermId>>,
    assumption_entries: Option<Vec<TermEntryStamp>>,
    /// The solver-declared EXTENSION of this query's obligation.
    ///
    /// Empty for every ordinary query, and writable only through
    /// [`Executor::declare_pareto_front_exhaustion_extension`], which consumes
    /// the opaque blocker package built for the exact seed probe. That package
    /// is bound to the public query epoch, source scope, authored roots, and
    /// objective inventory; no caller can supply or retarget an arbitrary term
    /// slice, so this cannot become a general escape hatch.
    ///
    /// #pareto-terminal-obligation — a Pareto `(check-sat)` after N emitted
    /// points does not ask "is the authored formula unsatisfiable"; it asks
    /// "is there a feasible point no emitted point dominates-or-equals". The
    /// refutation the seed probe produces is of `authored AND blocking`, and
    /// that is exactly the claim `unsat` makes there (Z3 behaves the same).
    /// Certifying it against `authored` ALONE rejects a correct refutation.
    ///
    /// This certifies the refutation only. It deliberately does NOT cover the
    /// separate enumeration-completeness claim that the emitted set IS the
    /// whole front — that rests on the lex-push construction and its debug
    /// assertions, exactly as before.
    declared_extension: Vec<TermId>,
    declared_extension_entries: Vec<TermEntryStamp>,
    /// Exact objective inventory that justified a Pareto obligation extension.
    /// `None` for every ordinary public query.
    declared_extension_objectives: Option<Vec<ay_frontend::Objective>>,
    declared_extension_objective_entries: Option<Vec<TermEntryStamp>>,
}

impl UnsatQueryEpoch {
    fn capture_entries(executor: &Executor, roots: &[TermId]) -> Option<Vec<TermEntryStamp>> {
        roots
            .iter()
            .map(|&root| executor.ctx.terms.entry_stamp(root))
            .collect()
    }

    fn entries_are_current(
        executor: &Executor,
        roots: &[TermId],
        entries: &[TermEntryStamp],
    ) -> bool {
        entries.len() == roots.len()
            && entries.iter().copied().map(Some).eq(roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
    }

    fn declared_extension_provenance_is_current(&self, executor: &Executor) -> bool {
        match (
            self.declared_extension_objectives.as_deref(),
            self.declared_extension_objective_entries.as_deref(),
        ) {
            (Some(objectives), Some(entries)) => {
                objectives == executor.ctx.objectives()
                    && entries.len() == objectives.len()
                    && entries.iter().copied().map(Some).eq(objectives
                        .iter()
                        .map(|objective| executor.ctx.terms.entry_stamp(objective.term)))
            }
            (None, None) => self.declared_extension.is_empty(),
            _ => false,
        }
    }

    fn term_entries_are_current(&self, executor: &Executor) -> bool {
        Self::entries_are_current(executor, &self.assertions, &self.assertion_entries)
            && match (
                self.assumptions.as_deref(),
                self.assumption_entries.as_deref(),
            ) {
                (Some(assumptions), Some(entries)) => {
                    Self::entries_are_current(executor, assumptions, entries)
                }
                (None, None) => true,
                _ => false,
            }
            && Self::entries_are_current(
                executor,
                &self.declared_extension,
                &self.declared_extension_entries,
            )
            && self.declared_extension_provenance_is_current(executor)
    }

    fn is_current(&self, executor: &Executor) -> bool {
        self.authority_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.term_entries_are_current(executor)
    }
}

/// Typed failure from the mandatory UNSAT publication gate.
#[derive(Debug, thiserror::Error)]
pub(crate) enum UnsatCertificationError {
    /// No public-query epoch was established for this provisional result.
    #[error("no public UNSAT query epoch is active")]
    MissingEpoch,
    /// A later public decision replaced the authority captured for this query.
    #[error("the public UNSAT query epoch is no longer current")]
    StaleEpoch,
    /// The frontend source/declaration scope changed after the query was bound.
    #[error("the public UNSAT source context is no longer current")]
    StaleSourceContext,
    /// A numeric term slot was rolled back and reused after the query was bound.
    #[error("the public UNSAT query contains a stale or replaced term entry")]
    StaleTermEntry,
    /// The public wrapper did not bind the assumptions before solving.
    #[error("the public UNSAT query epoch has no bound assumption set")]
    UnboundAssumptions,
    /// A wrapper attempted to certify a different assumption set.
    #[error("the UNSAT publication assumptions do not match the bound query epoch")]
    AssumptionEpochMismatch,
    /// Proof-source provenance is absent or belongs to another assertion epoch.
    #[error("the UNSAT proof provenance is not bound to the authored assertion epoch")]
    AssertionEpochMismatch,
    /// An internal assumption used by a redirect was not authored by this query.
    #[error("the UNSAT proof contains an assumption outside the authored query epoch")]
    ForeignInternalAssumption,
    /// No refutation artifact was produced.
    #[error("the provisional UNSAT verdict has no proof")]
    MissingProof,
    /// The strict proof checker rejected the refutation.
    #[error("strict UNSAT proof validation failed: {reason}")]
    StrictProofRejected { reason: String },
}

impl Executor {
    /// Whether the most recent text-command UNSAT publication consumed an
    /// exact-query strict-proof certificate.
    pub(crate) fn last_command_unsat_was_strictly_verified(&self) -> bool {
        matches!(
            self.last_command_unsat_admission,
            Some(CommandUnsatAdmission::StrictProof)
        )
    }

    /// Whether the most recent text-command UNSAT publication consumed one of
    /// the narrow exact source-semantic certificates.
    pub(crate) fn last_command_unsat_was_exact_semantically_verified(&self) -> bool {
        matches!(
            self.last_command_unsat_admission,
            Some(
                CommandUnsatAdmission::CheckedExactExists
                    | CommandUnsatAdmission::CheckedExactForallExists
                    | CommandUnsatAdmission::CheckedExactClosedForall
                    | CommandUnsatAdmission::CheckedExactForallUfGround
                    | CommandUnsatAdmission::CheckedExactFiniteExpansion
            )
        )
    }

    /// Whether the most recent text-command UNSAT publication consumed an
    /// independently checked SAT-refutation or trust-discharge certificate.
    pub(crate) fn last_command_unsat_was_independently_verified(&self) -> bool {
        matches!(
            self.last_command_unsat_admission,
            Some(
                CommandUnsatAdmission::CheckedSatRefutation
                    | CommandUnsatAdmission::CheckedBoolBv
                    | CommandUnsatAdmission::CheckedBvLia
                    | CommandUnsatAdmission::DischargedTrust
            )
        )
    }

    /// Exact assumption-free public source/root scope shared by the sealed
    /// pre-solve semantic UNSAT certificates.
    fn exact_plain_hard_unsat_scope_is_current(&self) -> bool {
        self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
            epoch.is_current(self)
                && epoch.assertions == self.ctx.assertions
                && epoch
                    .assumptions
                    .as_deref()
                    .is_some_and(|assumptions| assumptions.is_empty())
                && epoch.declared_extension.is_empty()
                && epoch.declared_extension_entries.is_empty()
                && epoch.declared_extension_objectives.is_none()
                && epoch.declared_extension_objective_entries.is_none()
        }) && self
            .proof_problem_assertion_provenance
            .as_ref()
            .is_some_and(|provenance| provenance.original_problem_assertions == self.ctx.assertions)
            && self.last_assumptions.iter().flatten().next().is_none()
    }

    /// Authenticate one exact source theorem from the immutable
    /// public-query epoch before any solver-owned quantifier transformation.
    ///
    /// The structural checker receives the epoch roots explicitly; live
    /// `ctx.assertions` participates only as a currentness equality check. This
    /// keeps a later Skolemized or instantiated working window from acquiring
    /// source-level authority by shape coincidence.
    pub(in crate::executor) fn try_authorize_current_query_exact_forall_exists_unsat(
        &self,
    ) -> Option<CheckedExactForallExistsUnsat> {
        if !self.exact_plain_hard_unsat_scope_is_current() {
            return None;
        }
        let authored_roots = self.unsat_query_epoch.as_ref()?.assertions.clone();
        let evidence = self.try_authorize_exact_forall_exists_roots(&authored_roots)?;
        // Recheck the complete public scope after the structural traversal and
        // before installing the one-shot token.
        if !self.exact_plain_hard_unsat_scope_is_current() {
            return None;
        }
        Some(evidence)
    }

    /// Authenticate one exact false literal instance of an authored top-level
    /// closed universal.
    ///
    /// `literals` are only an untrusted witness proposal.  This method derives
    /// the binder/body pair again from the exact authored conjunct, rebuilds a
    /// raw capture-safe quantifier-free substitution, and evaluates that rebuilt
    /// proposition independently.  No caller-provided Boolean verdict or
    /// transformed assertion root participates in the certificate.
    pub(in crate::executor) fn try_authorize_current_query_exact_closed_forall_unsat(
        &mut self,
        forall_id: TermId,
        literals: &[TermId],
    ) -> Option<CheckedExactClosedForallUnsat> {
        if crate::executor::model::scoped_term_evaluation_override_active()
            || !self.exact_plain_hard_unsat_scope_is_current()
        {
            return None;
        }
        let (roots, root_entries) = {
            let epoch = self.unsat_query_epoch.as_ref()?;
            (epoch.assertions.clone(), epoch.assertion_entries.clone())
        };
        if !authored_top_level_conjunct_contains(&self.ctx.terms, &roots, forall_id) {
            return None;
        }

        let (vars, body) =
            crate::executor::quantifier_loop::closed_quantifier_free_forall_literal_parts(
                &self.ctx.terms,
                forall_id,
            )?;
        if self.ctx.terms.sort(forall_id) != &CoreSort::Bool
            || self.ctx.terms.sort(body) != &CoreSort::Bool
            || vars.len() != literals.len()
            || vars
                .iter()
                .map(|(name, _)| name)
                .collect::<HashSet<_>>()
                .len()
                != vars.len()
            || !vars.iter().zip(literals).all(|((_, sort), &literal)| {
                exact_scalar_literal_has_sort(&self.ctx.terms, literal, sort)
            })
        {
            return None;
        }
        let interpreted_operators = exact_closed_forall_operators(&self.ctx.terms, body)?;
        if !exact_operator_identities_are_unshadowed(&self.ctx, &interpreted_operators) {
            return None;
        }

        let substitution: HashMap<String, TermId> = vars
            .iter()
            .zip(literals)
            .map(|((name, _), &literal)| (name.clone(), literal))
            .collect();
        let exact_instance =
            crate::ematching::subst_vars_exact_qf(&mut self.ctx.terms, body, &substitution)?;
        if self.ctx.terms.entry_stamp(exact_instance).is_none()
            || self.ctx.terms.sort(exact_instance) != &CoreSort::Bool
            || !crate::executor::model::with_isolated_eval_memo(|| {
                matches!(
                    self.evaluate_term(&crate::executor::model::Model::empty(), exact_instance,),
                    crate::executor::model::EvalValue::Bool(false)
                )
            })
        {
            return None;
        }

        let forall_entry = self.ctx.terms.entry_stamp(forall_id)?;
        let body_entry = self.ctx.terms.entry_stamp(body)?;
        let literal_entries = literals
            .iter()
            .map(|&literal| self.ctx.terms.entry_stamp(literal))
            .collect::<Option<Vec<_>>>()?;
        let exact_instance_entry = self.ctx.terms.entry_stamp(exact_instance)?;
        let term_snapshot = self.ctx.terms.snapshot_stamp();

        // Recheck the exact public scope after substitution/evaluation and
        // before sealing the one-shot token.  Term growth is allowed, but no
        // source, declaration, root, assumption, or root-entry change is.
        if !self.exact_plain_hard_unsat_scope_is_current()
            || !self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
                epoch.assertions == roots && epoch.assertion_entries == root_entries
            })
            || term_snapshot != self.ctx.terms.snapshot_stamp()
        {
            return None;
        }

        Some(CheckedExactClosedForallUnsat {
            query_epoch: self.query_authority_epoch.clone(),
            source_declaration_stamp: self.ctx.source_context_stamp(),
            roots: roots.into_boxed_slice(),
            root_entries: root_entries.into_boxed_slice(),
            forall_id,
            forall_entry,
            body,
            body_entry,
            literals: literals.into(),
            literal_entries: literal_entries.into_boxed_slice(),
            exact_instance,
            exact_instance_entry,
            interpreted_operators: interpreted_operators.into_boxed_slice(),
            term_snapshot,
        })
    }

    /// Authenticate one exact authored Int-forall instance against one exact
    /// authored ground UF-value pin.
    ///
    /// Candidate discovery is not authority: after deriving the unique literal
    /// witness for `f(x + k)`, this method raw-substitutes the immutable authored
    /// body and independently rechecks the resulting ground lower-bound clash.
    /// The UF head must carry positive live ordinary-declaration identity and
    /// kind evidence.  Every unsupported shape declines without consulting a
    /// solver verdict.
    pub(in crate::executor) fn try_authorize_current_query_exact_forall_uf_ground_unsat(
        &mut self,
    ) -> Option<CheckedExactForallUfGroundUnsat> {
        if crate::executor::model::scoped_term_evaluation_override_active()
            || !self.exact_plain_hard_unsat_scope_is_current()
            || self.should_abort_theory_loop()
            || self.strict_unsat_presentation_required()
        {
            return None;
        }
        let (roots, root_entries) = {
            let epoch = self.unsat_query_epoch.as_ref()?;
            (epoch.assertions.clone(), epoch.assertion_entries.clone())
        };
        if roots.len() > EXACT_FORALL_UF_GROUND_MAX_ROOTS {
            return None;
        }
        let interpreted_operators: Vec<String> = ["=", ">=", "<=", "+", "-"]
            .into_iter()
            .map(str::to_string)
            .collect();
        if !exact_operator_identities_are_unshadowed(&self.ctx, &interpreted_operators) {
            return None;
        }

        for &forall_id in &roots {
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(forall_id).clone() else {
                continue;
            };
            let [(bound, CoreSort::Int)] = vars.as_slice() else {
                continue;
            };
            if crate::ematching::contains_quantifier(&self.ctx.terms, body) {
                continue;
            }
            let mut remaining = EXACT_CLOSED_FORALL_WORK_LIMIT;
            let Some((body_symbol, argument, lower_bound)) =
                exact_int_uf_lower_bound(&self.ctx.terms, body, &mut remaining)
            else {
                continue;
            };
            let Some(bound_term) = exact_unique_named_int_var(&self.ctx.terms, argument, bound)
            else {
                continue;
            };
            let Some((coefficient, offset)) =
                exact_affine_int_in_bound(&self.ctx.terms, argument, bound_term, &mut remaining)
            else {
                continue;
            };
            if coefficient != BigInt::from(1) {
                continue;
            }

            for &pin in &roots {
                if pin == forall_id {
                    continue;
                }
                let mut remaining = EXACT_CLOSED_FORALL_WORK_LIMIT;
                let Some((pin_symbol, point, pinned_value)) =
                    exact_int_uf_pin(&self.ctx.terms, pin, &mut remaining)
                else {
                    continue;
                };
                if pin_symbol != body_symbol || pinned_value >= lower_bound {
                    continue;
                }
                let request = ProjectionBindingRequest {
                    symbol: body_symbol.clone(),
                    parameter_sorts: vec![CoreSort::Int],
                    result_sort: CoreSort::Int,
                };
                let Ok(uf_binding) = self.ctx.check_projection_declaration(&request) else {
                    continue;
                };

                let witness_value = point - offset.clone();
                let witness = self.ctx.terms.mk_int(witness_value);
                let Some((checked_body, source_contradiction)) =
                    exact_forall_uf_source_contradiction(
                        &self.ctx.terms,
                        forall_id,
                        bound_term,
                        pin,
                        witness,
                        uf_binding.symbol(),
                    )
                else {
                    continue;
                };
                if checked_body != body {
                    continue;
                }

                let substitution: HashMap<String, TermId> =
                    [(bound.clone(), witness)].into_iter().collect();
                let Some(exact_instance) =
                    crate::ematching::subst_vars_exact_qf(&mut self.ctx.terms, body, &substitution)
                else {
                    continue;
                };
                if exact_forall_uf_instance_contradiction(
                    &self.ctx.terms,
                    exact_instance,
                    pin,
                    uf_binding.symbol(),
                ) != Some(source_contradiction.clone())
                {
                    continue;
                }

                let forall_entry = self.ctx.terms.entry_stamp(forall_id)?;
                let body_entry = self.ctx.terms.entry_stamp(body)?;
                let bound_entry = self.ctx.terms.entry_stamp(bound_term)?;
                let pin_entry = self.ctx.terms.entry_stamp(pin)?;
                let witness_entry = self.ctx.terms.entry_stamp(witness)?;
                let exact_instance_entry = self.ctx.terms.entry_stamp(exact_instance)?;
                let term_snapshot = self.ctx.terms.snapshot_stamp();

                if !self.exact_plain_hard_unsat_scope_is_current()
                    || self.should_abort_theory_loop()
                    || self.strict_unsat_presentation_required()
                    || !self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
                        epoch.assertions == roots && epoch.assertion_entries == root_entries
                    })
                    || !self.ctx.projection_binding_still_current(&uf_binding)
                    || term_snapshot != self.ctx.terms.snapshot_stamp()
                {
                    return None;
                }

                return Some(CheckedExactForallUfGroundUnsat {
                    query_epoch: self.query_authority_epoch.clone(),
                    source_declaration_stamp: self.ctx.source_context_stamp(),
                    roots: roots.clone().into_boxed_slice(),
                    root_entries: root_entries.clone().into_boxed_slice(),
                    forall_id,
                    forall_entry,
                    body,
                    body_entry,
                    bound: bound_term,
                    bound_entry,
                    pin,
                    pin_entry,
                    witness,
                    witness_entry,
                    exact_instance,
                    exact_instance_entry,
                    uf_binding,
                    interpreted_operators: interpreted_operators.into_boxed_slice(),
                    contradiction: source_contradiction,
                    term_snapshot,
                });
            }
        }
        None
    }

    /// Independently re-expand the immutable public roots and prove a narrow
    /// ground contradiction in the complete replacement vector.
    ///
    /// This constructor is intentionally BV-forall-only.  Wide binders are
    /// accepted only when the canonical expander itself proves a bounded guard;
    /// small binders use its exhaustive finite carrier.  Every other quantified
    /// shape, nested quantifier, assumption-bearing query, stale source/root
    /// epoch, incomplete expansion, or non-elementary ground conflict declines.
    pub(in crate::executor) fn try_authorize_current_query_exact_finite_expansion_unsat(
        &mut self,
    ) -> Option<CheckedExactFiniteExpansionUnsat> {
        if crate::executor::model::scoped_term_evaluation_override_active()
            || !self.exact_plain_hard_unsat_scope_is_current()
            || self.should_abort_theory_loop()
            || self.strict_unsat_presentation_required()
        {
            return None;
        }
        // Public-root replay must be independent of producer-local derived
        // bounds and BOOL_GROUND extras retained in finite-domain TLS.
        let _standalone_replay = crate::skolemize::scoped_standalone_finite_domain_replay();
        let (roots, root_entries) = {
            let epoch = self.unsat_query_epoch.as_ref()?;
            (epoch.assertions.clone(), epoch.assertion_entries.clone())
        };
        if roots.is_empty()
            || roots
                .iter()
                .any(|&root| self.ctx.terms.sort(root) != &CoreSort::Bool)
        {
            return None;
        }
        let interpreted_operators =
            exact_finite_expansion_interpreted_operators(&self.ctx.terms, &roots)?;
        if !exact_operator_identities_are_unshadowed(&self.ctx, &interpreted_operators) {
            return None;
        }
        let mut expanded_roots = Vec::with_capacity(roots.len());
        let mut quantified_roots = 0usize;
        for &root in &roots {
            if !crate::ematching::contains_quantifier(&self.ctx.terms, root) {
                expanded_roots.push(root);
                continue;
            }
            quantified_roots += 1;
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(root).clone() else {
                return None;
            };
            if vars.is_empty()
                || self.ctx.terms.sort(body) != &CoreSort::Bool
                || !exact_finite_binder_occurrences_are_well_sorted(&self.ctx.terms, body, &vars)
                || crate::ematching::contains_quantifier(&self.ctx.terms, body)
            {
                return None;
            }
            let (expanded, _) =
                crate::skolemize::finite_domain_expand_with_instances(&mut self.ctx.terms, root)?;
            if self.ctx.terms.sort(expanded) != &CoreSort::Bool
                || crate::ematching::contains_quantifier(&self.ctx.terms, expanded)
            {
                return None;
            }
            expanded_roots.push(expanded);
        }
        if quantified_roots == 0 || expanded_roots.len() != roots.len() {
            return None;
        }
        let contradiction =
            exact_finite_expansion_ground_contradiction(&self.ctx.terms, &expanded_roots)?;
        let expanded_root_entries = expanded_roots
            .iter()
            .map(|&root| self.ctx.terms.entry_stamp(root))
            .collect::<Option<Vec<_>>>()?;
        let term_snapshot = self.ctx.terms.snapshot_stamp();

        // Recheck after canonical replay: expansion can grow the term store but
        // cannot change the query/source epoch or any authored root entry.
        if !self.exact_plain_hard_unsat_scope_is_current()
            || self.should_abort_theory_loop()
            || !self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
                epoch.assertions == roots && epoch.assertion_entries == root_entries
            })
            || !exact_operator_identities_are_unshadowed(&self.ctx, &interpreted_operators)
            || term_snapshot != self.ctx.terms.snapshot_stamp()
        {
            return None;
        }

        Some(CheckedExactFiniteExpansionUnsat {
            query_epoch: self.query_authority_epoch.clone(),
            source_declaration_stamp: self.ctx.source_context_stamp(),
            roots: roots.into_boxed_slice(),
            root_entries: root_entries.into_boxed_slice(),
            expanded_roots: expanded_roots.into_boxed_slice(),
            expanded_root_entries: expanded_root_entries.into_boxed_slice(),
            contradiction,
            interpreted_operators: interpreted_operators.into_boxed_slice(),
            term_snapshot,
        })
    }

    /// Whether an independently certified UNSAT result must also provide a
    /// translated, checker-accepted authored-scope proof.
    ///
    /// Public solves always enable the internal proof tracker so every
    /// ordinary UNSAT can be certified. That bookkeeping is not a user proof
    /// request. Conversely, the synthesized default CLI certificate is
    /// explicitly best-effort and must not turn an independently certified
    /// semantic verdict into `unknown` merely because an independent lane
    /// cannot translate its theorem into Alethe. Only an explicit API/CLI proof
    /// requirement or SMT-LIB `:produce-proofs true` makes the missing
    /// translation verdict-relevant. Strict verification modes impose the same
    /// requirement even when proof export itself was not requested.
    fn strict_unsat_presentation_required(&self) -> bool {
        self.proof_artifact_required
            || self.self_check()
            || self.verification_level().has_proof_checking()
            || self.strict_proofs_enabled()
            || matches!(
                self.ctx.get_option("produce-proofs"),
                Some(ay_frontend::OptionValue::Bool(true))
            )
    }

    /// Emit UNSAT from the exact unit-difference existential theorem.
    ///
    /// This is a distinct semantic-certificate lane, not an assertion that the
    /// ordinary proof checker accepted an LRAT/Alethe refutation. The evidence
    /// itself remains inside the one-shot token so the later certification and
    /// API boundaries can recheck its exact term snapshot.
    pub(in crate::executor) fn emit_checked_exact_exists_unsat(
        &mut self,
        evidence: CheckedExactExistsUnsat,
    ) -> SolveResult {
        self.last_unsat_certificate = None;
        self.last_sat_certificate = None;
        self.last_model = None;
        self.last_model_validated = false;
        self.last_proof = None;
        self.clear_finite_enum_proof_state();

        if !self.exact_plain_hard_unsat_scope_is_current() || !evidence.is_current(self) {
            return self.reject_uncertified_verdict_for_publication(
                "checked exact-exists UNSAT evidence was stale at emission".to_string(),
            );
        }
        if self.strict_unsat_presentation_required() {
            return self.reject_uncertified_verdict_for_publication(
                "checked exact-exists UNSAT has no translated authored-scope proof for the requested proof artifact"
                    .to_string(),
            );
        }

        self.suppress_unsat_proof_reconstruction();
        self.last_unknown_reason = None;
        self.last_statistics
            .set_int("verdict_certification.checked_exact_exists", 1);
        self.last_result = Some(SolveResult::unsat());
        self.last_unsat_certificate = Some(UnsatCertificate(
            UnsatCertificateKind::CheckedExactExists(evidence),
        ));
        SolveResult::unsat()
    }

    /// Emit UNSAT from one of the exact source-level `forall`/`exists`
    /// theorems. This is an independently checked semantic certificate, not a
    /// claim that a Skolemized inner proof was translated to authored Alethe.
    pub(in crate::executor) fn emit_checked_exact_forall_exists_unsat(
        &mut self,
        evidence: CheckedExactForallExistsUnsat,
    ) -> SolveResult {
        self.last_unsat_certificate = None;
        self.last_sat_certificate = None;
        self.last_model = None;
        self.last_model_validated = false;
        self.last_proof = None;
        self.clear_finite_enum_proof_state();

        if !self.exact_plain_hard_unsat_scope_is_current() || !evidence.is_current(self) {
            return self.reject_uncertified_verdict_for_publication(
                "checked exact-forall-exists UNSAT evidence was stale at emission".to_string(),
            );
        }
        if self.strict_unsat_presentation_required() {
            return self.reject_uncertified_verdict_for_publication(
                "checked exact-forall-exists UNSAT has no translated authored-scope proof for the requested proof artifact"
                    .to_string(),
            );
        }

        self.suppress_unsat_proof_reconstruction();
        self.last_unknown_reason = None;
        self.last_statistics
            .set_int("verdict_certification.checked_exact_forall_exists", 1);
        self.last_result = Some(SolveResult::unsat());
        self.last_unsat_certificate = Some(UnsatCertificate(
            UnsatCertificateKind::CheckedExactForallExists(evidence),
        ));
        SolveResult::unsat()
    }

    /// Emit UNSAT from a sealed exact false instance of one authored
    /// top-level closed universal.  This semantic certificate is distinct from
    /// a translated `forall_inst` proof; explicit proof and strict verification
    /// modes therefore continue to fail closed.
    pub(in crate::executor) fn emit_checked_exact_closed_forall_unsat(
        &mut self,
        evidence: CheckedExactClosedForallUnsat,
    ) -> SolveResult {
        self.last_unsat_certificate = None;
        self.last_sat_certificate = None;
        self.last_model = None;
        self.last_model_validated = false;
        self.last_proof = None;
        self.clear_finite_enum_proof_state();

        if !self.exact_plain_hard_unsat_scope_is_current() || !evidence.is_current(self) {
            return self.reject_uncertified_verdict_for_publication(
                "checked exact closed-forall UNSAT evidence was stale at emission".to_string(),
            );
        }
        if self.strict_unsat_presentation_required() {
            return self.reject_uncertified_verdict_for_publication(
                "checked exact closed-forall UNSAT has no translated authored-scope forall-inst proof for the requested proof artifact"
                    .to_string(),
            );
        }

        self.suppress_unsat_proof_reconstruction();
        self.last_unknown_reason = None;
        self.last_statistics
            .set_int("verdict_certification.checked_exact_closed_forall", 1);
        self.last_result = Some(SolveResult::unsat());
        self.last_unsat_certificate = Some(UnsatCertificate(
            UnsatCertificateKind::CheckedExactClosedForall(evidence),
        ));
        SolveResult::unsat()
    }

    /// Emit UNSAT from one exact authored Int-forall instance plus its
    /// contradictory authored ground UF-value pin.  This semantic certificate
    /// does not claim a translated `forall_inst` artifact, so every explicit
    /// proof or proof-checking mode remains fail-closed.
    pub(in crate::executor) fn emit_checked_exact_forall_uf_ground_unsat(
        &mut self,
        evidence: CheckedExactForallUfGroundUnsat,
    ) -> SolveResult {
        self.last_unsat_certificate = None;
        self.last_sat_certificate = None;
        self.last_model = None;
        self.last_model_validated = false;
        self.last_proof = None;
        self.clear_finite_enum_proof_state();

        if !self.exact_plain_hard_unsat_scope_is_current() || !evidence.is_current(self) {
            return self.reject_uncertified_verdict_for_publication(
                "checked exact authored-forall UF-ground UNSAT evidence was stale at emission"
                    .to_string(),
            );
        }
        if self.strict_unsat_presentation_required() {
            return self.reject_uncertified_verdict_for_publication(
                "checked exact authored-forall UF-ground UNSAT has no translated authored-scope forall-inst proof for the requested proof artifact"
                    .to_string(),
            );
        }

        self.suppress_unsat_proof_reconstruction();
        self.last_unknown_reason = None;
        self.last_statistics
            .set_int("verdict_certification.checked_exact_forall_uf_ground", 1);
        self.last_result = Some(SolveResult::unsat());
        self.last_unsat_certificate = Some(UnsatCertificate(
            UnsatCertificateKind::CheckedExactForallUfGround(evidence),
        ));
        SolveResult::unsat()
    }

    /// Emit UNSAT from exact canonical finite-BV expansion plus one elementary
    /// ground contradiction.  It is semantic authority, not a translated
    /// `forall_inst` artifact, so explicit proof modes continue to fail closed.
    pub(in crate::executor) fn emit_checked_exact_finite_expansion_unsat(
        &mut self,
        evidence: CheckedExactFiniteExpansionUnsat,
    ) -> SolveResult {
        self.last_unsat_certificate = None;
        self.last_sat_certificate = None;
        self.last_model = None;
        self.last_model_validated = false;
        self.last_proof = None;
        self.clear_finite_enum_proof_state();

        if !self.exact_plain_hard_unsat_scope_is_current() || !evidence.is_current(self) {
            return self.reject_uncertified_verdict_for_publication(
                "checked exact finite-expansion UNSAT evidence was stale at emission".to_string(),
            );
        }
        if self.strict_unsat_presentation_required() {
            return self.reject_uncertified_verdict_for_publication(
                "checked exact finite-expansion UNSAT has no translated authored-scope forall-inst proof for the requested proof artifact"
                    .to_string(),
            );
        }

        self.suppress_unsat_proof_reconstruction();
        self.last_unknown_reason = None;
        self.last_statistics
            .set_int("verdict_certification.checked_exact_finite_expansion", 1);
        self.last_result = Some(SolveResult::unsat());
        self.last_unsat_certificate = Some(UnsatCertificate(
            UnsatCertificateKind::CheckedExactFiniteExpansion(evidence),
        ));
        SolveResult::unsat()
    }

    /// Whether an assumption leaf belongs to the authenticated public query.
    ///
    /// Named-core solving may assumption-track an equivalence-exact rewrite of
    /// an authored named assertion. `named_assert_rewrites` is populated only
    /// by per-assertion equivalence-preserving passes and maps the rewritten
    /// term back to its authored root, so accepting that root relationship does
    /// not widen the query. Solver-generated assumptions without such a root
    /// remain foreign.
    fn query_authorizes_assumption(
        &self,
        term: TermId,
        authored_assertions: &[TermId],
        public_assumptions: &[TermId],
    ) -> bool {
        authored_assertions.contains(&term)
            || public_assumptions.contains(&term)
            || self
                .named_assert_rewrites
                .get(&term)
                .is_some_and(|root| authored_assertions.contains(root))
    }

    /// Canonically reject a definite verdict that lacks its one-shot
    /// publication capability.
    ///
    /// This is shared by strict UNSAT certification and the final native API
    /// wrapper boundary. It publishes the registered verdict-certification
    /// origin immediately, revoking every model/proof/core/optimum artifact so
    /// the executor state and returned wrapper cannot disagree.
    pub(crate) fn reject_uncertified_verdict_for_publication(
        &mut self,
        diagnostic: String,
    ) -> SolveResult {
        self.publish_unknown_from_origin(UnknownOrigin::VerdictCertification);
        self.record_model_validation_unknown_diagnostic(diagnostic);
        SolveResult::Unknown
    }

    /// Start a new immutable public-query epoch.
    ///
    /// Called only after the preceding query artifacts have been invalidated.
    /// [`Self::rebind_unsat_query_epoch_assertions`] may replace this initial
    /// snapshot once command elaboration has materialized authenticated
    /// schematic instances, but no solver-owned transformation may intervene.
    pub(super) fn begin_unsat_query_epoch(&mut self, assertions: &[TermId]) {
        let Some(assertion_entries) = UnsatQueryEpoch::capture_entries(self, assertions) else {
            self.unsat_query_epoch = None;
            self.last_unsat_certificate = None;
            return;
        };
        self.unsat_query_epoch = Some(UnsatQueryEpoch {
            authority_epoch: self.query_authority_epoch.clone(),
            source_context_stamp: self.ctx.source_context_stamp(),
            assertions: assertions.to_vec(),
            assertion_entries,
            assumptions: None,
            assumption_entries: None,
            declared_extension: Vec::new(),
            declared_extension_entries: Vec::new(),
            declared_extension_objectives: None,
            declared_extension_objective_entries: None,
        });
        self.last_unsat_certificate = None;
    }

    /// Replace the pre-elaboration assertion snapshot with the exact roots
    /// produced by the frontend for this same public query.
    ///
    /// SMT-LIB 2.7 schematic assertions are authenticated authored inputs, but
    /// their concrete instances do not exist until command elaboration. This
    /// rebind is permitted only before assumptions have been attached and
    /// before solving starts. Any lifecycle violation drops the epoch so a
    /// later provisional UNSAT fails closed instead of borrowing authority.
    pub(super) fn rebind_unsat_query_epoch_assertions(&mut self, assertions: &[TermId]) -> bool {
        let can_rebind = self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
            epoch.assumptions.is_none()
                && epoch.assumption_entries.is_none()
                && epoch.declared_extension.is_empty()
                && epoch.declared_extension_entries.is_empty()
                && epoch.declared_extension_objectives.is_none()
                && epoch.declared_extension_objective_entries.is_none()
        });
        if !can_rebind {
            self.unsat_query_epoch = None;
            self.last_unsat_certificate = None;
            return false;
        }
        let Some(assertion_entries) = UnsatQueryEpoch::capture_entries(self, assertions) else {
            self.unsat_query_epoch = None;
            self.last_unsat_certificate = None;
            return false;
        };
        let source_context_stamp = self.ctx.source_context_stamp();
        if let Some(epoch) = self.unsat_query_epoch.as_mut() {
            epoch.source_context_stamp = source_context_stamp;
            epoch.assertions.clear();
            epoch.assertions.extend_from_slice(assertions);
            epoch.assertion_entries = assertion_entries;
            self.last_unsat_certificate = None;
            true
        } else {
            self.last_unsat_certificate = None;
            false
        }
    }

    /// Bind the exact caller-supplied assumptions before entering a solve.
    ///
    /// Rebinding is accepted only when it is byte-for-byte identical. This lets
    /// narrow wrapper layers be idempotent without permitting an internal retry
    /// to change the authority of an already-started public query.
    pub(crate) fn bind_unsat_query_assumptions(&mut self, assumptions: &[TermId]) {
        // Binding is a pre-solve authority mutation. Even an idempotent or
        // rejected late bind must retire a previously minted one-shot token.
        self.last_unsat_certificate = None;
        let Some(assumption_entries) = UnsatQueryEpoch::capture_entries(self, assumptions) else {
            self.unsat_query_epoch = None;
            return;
        };
        let Some(epoch) = self.unsat_query_epoch.as_ref() else {
            return;
        };
        if !epoch.is_current(self) {
            self.unsat_query_epoch = None;
            return;
        }
        let retire = match (&epoch.assumptions, &epoch.assumption_entries) {
            (Some(bound), Some(_)) if bound != assumptions => {
                // Preserve the first binding. Certification will reject the
                // wrapper's later, mismatching assumption slice.
                false
            }
            (Some(_), Some(bound_entries)) => bound_entries != &assumption_entries,
            (None, None) => false,
            _ => true,
        };
        if retire {
            self.unsat_query_epoch = None;
            return;
        }
        if let Some(epoch) = self.unsat_query_epoch.as_mut() {
            if epoch.assumptions.is_none() {
                epoch.assumptions = Some(assumptions.to_vec());
                epoch.assumption_entries = Some(assumption_entries);
            }
        }
    }

    /// Exact public query authority available to the checked SAT-refutation
    /// composer.
    ///
    /// This is deliberately narrower than general UNSAT publication: Pareto
    /// obligation extensions remain outside this composed-certificate slice.
    /// Assumptions must already be bound to the immutable public-query epoch; a
    /// missing or stale scope simply disables the alternate certificate path.
    fn checked_sat_refutation_query_epoch(&self) -> Option<&UnsatQueryEpoch> {
        let epoch = self.unsat_query_epoch.as_ref()?;
        if !epoch.is_current(self)
            || epoch.assumptions.is_none()
            || !epoch.declared_extension.is_empty()
            || !epoch.declared_extension_entries.is_empty()
            || epoch.declared_extension_objectives.is_some()
            || epoch.declared_extension_objective_entries.is_some()
        {
            return None;
        }
        Some(epoch)
    }

    /// Constant-size identity for the exact public query.
    ///
    /// The potentially large authored-root vector is deliberately exposed by
    /// [`Self::checked_sat_refutation_query_roots`] as a borrowed slice.  The
    /// checked-refutation gate can then charge its aggregate resource meter
    /// before making the retained copy carried by the capability.
    pub(in crate::executor) fn checked_sat_refutation_query_scope(
        &self,
    ) -> Option<(QueryAuthorityEpoch, SourceContextStamp)> {
        let epoch = self.checked_sat_refutation_query_epoch()?;
        Some((
            epoch.authority_epoch.clone(),
            epoch.source_context_stamp.clone(),
        ))
    }

    /// Borrow the ordered authored roots of the exact supported query scope.
    pub(in crate::executor) fn checked_sat_refutation_query_roots(&self) -> Option<&[TermId]> {
        Some(&self.checked_sat_refutation_query_epoch()?.assertions)
    }

    /// Borrow the exact ordered assumptions bound to the supported query.
    pub(in crate::executor) fn checked_sat_refutation_query_assumptions(
        &self,
    ) -> Option<&[TermId]> {
        self.checked_sat_refutation_query_epoch()?
            .assumptions
            .as_deref()
    }

    /// Borrow one bounded, plain public-query root window for the narrow
    /// finite-enum proof path.
    ///
    /// The length check intentionally precedes `is_current`: currentness scans
    /// every retained entry stamp, so an oversized source must be declined
    /// before that scan. Only an exact `(check-sat)` query with an explicitly
    /// bound empty assumption set and no solver-declared extension is eligible.
    pub(in crate::executor) fn bounded_plain_unsat_query_scope(
        &self,
        max_roots: usize,
    ) -> Option<(QueryAuthorityEpoch, SourceContextStamp, &[TermId])> {
        let epoch = self.unsat_query_epoch.as_ref()?;
        if epoch.assertions.len() > max_roots
            || epoch.assumptions.as_deref() != Some(&[])
            || !epoch.declared_extension.is_empty()
            || !epoch.declared_extension_entries.is_empty()
            || epoch.declared_extension_objectives.is_some()
            || epoch.declared_extension_objective_entries.is_some()
            || !epoch.is_current(self)
        {
            return None;
        }
        Some((
            epoch.authority_epoch.clone(),
            epoch.source_context_stamp.clone(),
            &epoch.assertions,
        ))
    }

    /// The solver-declared obligation extension for the active query, if any.
    /// Empty for every query but a Pareto terminal (#pareto-terminal-obligation).
    pub(crate) fn declared_obligation_extension(&self) -> Vec<TermId> {
        self.unsat_query_epoch
            .as_ref()
            .filter(|epoch| epoch.is_current(self))
            .map(|epoch| epoch.declared_extension.clone())
            .unwrap_or_default()
    }

    /// Declare that THIS query's obligation is `authored AND blocking`, using
    /// the opaque blocker package built by the Pareto enumerator.
    ///
    /// #pareto-terminal-obligation. Called only from the Pareto terminal arm,
    /// which is publishing "the front is exhausted" — a refutation of
    /// `authored AND blocking`, not of `authored`.
    ///
    ///
    /// Returns `false` without changing the epoch if query/source/root/objective
    /// identity changed between blocker construction and the terminal probe.
    pub(crate) fn declare_pareto_front_exhaustion_extension(
        &mut self,
        extension: super::optimization::ParetoFrontExhaustionExtension,
    ) -> bool {
        if self.ctx.objectives().is_empty() {
            return false;
        }
        let Some(binding) = extension.into_current_binding(self) else {
            return false;
        };
        let epoch_matches = self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
            epoch.is_current(self)
                && epoch.assertions.as_slice() == binding.hard_roots.as_ref()
                && epoch.assertion_entries.as_slice() == binding.hard_root_entries.as_ref()
                && epoch.declared_extension.is_empty()
                && epoch.declared_extension_entries.is_empty()
                && epoch.declared_extension_objectives.is_none()
                && epoch.declared_extension_objective_entries.is_none()
        });
        if !epoch_matches {
            return false;
        }
        if let Some(epoch) = self.unsat_query_epoch.as_mut() {
            epoch.declared_extension = binding.blocking.into_vec();
            epoch.declared_extension_entries = binding.blocking_entries.into_vec();
            epoch.declared_extension_objectives = Some(binding.objectives.into_vec());
            epoch.declared_extension_objective_entries = Some(binding.objective_entries.into_vec());
            true
        } else {
            false
        }
    }

    /// Strictly certify a provisional public UNSAT result and mint its token.
    fn mint_unsat_certificate(
        &mut self,
        assumptions: &[TermId],
    ) -> Result<UnsatCertificate, UnsatCertificationError> {
        let epoch = self
            .unsat_query_epoch
            .as_ref()
            .ok_or(UnsatCertificationError::MissingEpoch)?;
        if !epoch
            .authority_epoch
            .is_same_epoch(&self.query_authority_epoch)
        {
            return Err(UnsatCertificationError::StaleEpoch);
        }
        if epoch.source_context_stamp != self.ctx.source_context_stamp() {
            return Err(UnsatCertificationError::StaleSourceContext);
        }
        if !epoch.term_entries_are_current(self) {
            return Err(UnsatCertificationError::StaleTermEntry);
        }
        let bound = epoch
            .assumptions
            .as_deref()
            .ok_or(UnsatCertificationError::UnboundAssumptions)?;
        if bound != assumptions {
            return Err(UnsatCertificationError::AssumptionEpochMismatch);
        }

        // The public-query lifecycle installs this provenance from the exact
        // authored/materialized assertion snapshot before any preprocessing or
        // theory axiom can alter the working stack. Requiring exact vector
        // equality prevents a proof from borrowing authority from an older or
        // solver-generated assertion set.
        let Some(provenance) = self.proof_problem_assertion_provenance.as_ref() else {
            probe_cert_reject(|| "assertion epoch: no proof provenance is installed".to_string());
            return Err(UnsatCertificationError::AssertionEpochMismatch);
        };
        if provenance.original_problem_assertions != epoch.assertions {
            probe_cert_reject(|| {
                let render = |ids: &[TermId]| -> String {
                    ids.iter()
                        .enumerate()
                        .map(|(i, t)| {
                            let rendered = ay_proof::format_term_alethe(&self.ctx.terms, *t);
                            format!("    [{i}] {rendered}")
                        })
                        .collect::<Vec<_>>()
                        .join("\n")
                };
                format!(
                    "assertion epoch mismatch\n  provenance.original_problem_assertions \
                     ({}):\n{}\n  epoch.assertions ({}):\n{}",
                    provenance.original_problem_assertions.len(),
                    render(&provenance.original_problem_assertions),
                    epoch.assertions.len(),
                    render(&epoch.assertions),
                )
            });
            return Err(UnsatCertificationError::AssertionEpochMismatch);
        }

        // Named-core redirects temporarily move authored assertions into the
        // executor's assumption slot. Such terms remain legitimate only when
        // they occur in the frozen base or in the caller's exact assumption
        // slice. No solver-generated term may expand the proof's authority.
        if self
            .last_assumptions
            .iter()
            .flatten()
            .any(|&term| !self.query_authorizes_assumption(term, &epoch.assertions, assumptions))
        {
            return Err(UnsatCertificationError::ForeignInternalAssumption);
        }
        // The declared extension travels in its own slot and must never also
        // arrive through `last_assumptions`, which the check above keeps
        // strict. Overlap would mean a solver-generated term had reached the
        // assumption channel, and that is exactly the tripwire to preserve.
        debug_assert!(
            self.last_assumptions
                .iter()
                .flatten()
                .all(|term| { !epoch.declared_extension.contains(term) }),
            "BUG: the Pareto obligation extension leaked into last_assumptions"
        );

        let authenticated_scope = AuthenticatedUnsatScope::capture(self, epoch, assumptions)
            .ok_or(UnsatCertificationError::StaleTermEntry)?;

        enum CertificationSource {
            StrictProof,
            CheckedSatRefutation,
            CheckedBoolBv {
                evidence: AuthenticatedBoolBvUnsatQuery,
                exact_roots: Box<[TermId]>,
            },
            CheckedBvLia {
                evidence: AuthenticatedBvLiaUnsatQuery,
                exact_roots: Box<[TermId]>,
            },
            DischargedTrust,
        }
        enum StrictProofPresentationFailure {
            Missing,
            Rejected(ay_proof::ProofCheckError),
        }

        let strict_presentation = match self.last_proof.as_ref() {
            Some(proof) => self
                .check_proof_strict_with_datatypes(proof)
                .map(|_| ())
                .map_err(StrictProofPresentationFailure::Rejected),
            None => Err(StrictProofPresentationFailure::Missing),
        };

        let certification_source = match strict_presentation {
            Ok(()) => CertificationSource::StrictProof,
            Err(presentation_failure) => {
                // These three lanes authenticate the exact immutable public
                // query independently of the Alethe presentation. Consequently
                // a missing, malformed, resource-limited, or otherwise
                // structurally rejected presentation cannot invalidate their
                // theorem. They are deliberately unavailable when the caller
                // explicitly requested a translated proof or strict proof
                // verification: those modes promise that artifact itself.
                let independently_checked = if self.strict_unsat_presentation_required() {
                    None
                } else if self.checked_sat_refutation_authorizes(epoch, assumptions) {
                    Some(CertificationSource::CheckedSatRefutation)
                } else if let Some((evidence, exact_roots)) =
                    self.authenticate_bool_bv_query(epoch, assumptions)?
                {
                    Some(CertificationSource::CheckedBoolBv {
                        evidence,
                        exact_roots,
                    })
                } else if let Some((evidence, exact_roots)) =
                    self.authenticate_bv_lia_query(epoch, assumptions)?
                {
                    Some(CertificationSource::CheckedBvLia {
                        evidence,
                        exact_roots,
                    })
                } else {
                    None
                };

                if let Some(independently_checked) = independently_checked {
                    independently_checked
                } else {
                    match presentation_failure {
                        StrictProofPresentationFailure::Missing => {
                            return Err(UnsatCertificationError::MissingProof);
                        }
                        // Only trust-family presentation failures are eligible
                        // for the separate clause-discharge fallback. Explicit
                        // proof and proof-checking modes were excluded above and
                        // must see the original strict rejection.
                        StrictProofPresentationFailure::Rejected(
                            error @ (ay_proof::ProofCheckError::TrustStep { .. }
                            | ay_proof::ProofCheckError::StrictProofModeTrust { .. }
                            | ay_proof::ProofCheckError::HoleStep { .. }),
                        ) if !self.strict_unsat_presentation_required() => {
                            self.discharge_trust_steps_for_certification(&error)?;
                            CertificationSource::DischargedTrust
                        }
                        StrictProofPresentationFailure::Rejected(
                            error @ ay_proof::ProofCheckError::UnsupportedTheoryLemmaKind {
                                kind: ay_core::TheoryLemmaKind::Generic,
                                ..
                            },
                        ) if !self.strict_unsat_presentation_required() => {
                            self.discharge_trust_steps_for_certification(&error)?;
                            CertificationSource::DischargedTrust
                        }
                        StrictProofPresentationFailure::Rejected(error) => {
                            return Err(UnsatCertificationError::StrictProofRejected {
                                reason: error.to_string(),
                            });
                        }
                    }
                }
            }
        };

        let kind = match certification_source {
            CertificationSource::StrictProof => {
                UnsatCertificateKind::StrictProof(authenticated_scope)
            }
            CertificationSource::CheckedSatRefutation => {
                let checked = self.last_checked_sat_refutation.take().ok_or_else(|| {
                    UnsatCertificationError::StrictProofRejected {
                        reason: "checked SAT-refutation authority disappeared before token mint"
                            .to_string(),
                    }
                })?;
                UnsatCertificateKind::CheckedSatRefutation {
                    checked,
                    scope: authenticated_scope,
                }
            }
            CertificationSource::CheckedBoolBv {
                evidence,
                exact_roots,
            } => {
                let checked = CheckedBoolBvUnsat::bind(
                    authenticated_scope,
                    evidence,
                    &self.ctx.terms,
                    &exact_roots,
                )
                .ok_or_else(|| UnsatCertificationError::StrictProofRejected {
                    reason: "source-level Bool/BV authority became stale before token mint"
                        .to_string(),
                })?;
                UnsatCertificateKind::CheckedBoolBv(checked)
            }
            CertificationSource::CheckedBvLia {
                evidence,
                exact_roots,
            } => {
                let checked = CheckedBvLiaUnsat::bind(
                    authenticated_scope,
                    evidence,
                    &self.ctx.terms,
                    &exact_roots,
                )
                .ok_or_else(|| UnsatCertificationError::StrictProofRejected {
                    reason: "source-level BV/LIA authority became stale before token mint"
                        .to_string(),
                })?;
                UnsatCertificateKind::CheckedBvLia(checked)
            }
            CertificationSource::DischargedTrust => {
                UnsatCertificateKind::DischargedTrust(authenticated_scope)
            }
        };
        Ok(UnsatCertificate(kind))
    }

    /// Whether the independent SAT-resolution sidecar proves this exact public
    /// query. It is consulted after any failed strict-proof presentation when
    /// the caller did not explicitly require that translated proof artifact.
    fn checked_sat_refutation_authorizes(
        &self,
        epoch: &UnsatQueryEpoch,
        assumptions: &[TermId],
    ) -> bool {
        epoch.declared_extension.is_empty()
            && epoch.declared_extension_entries.is_empty()
            && epoch.declared_extension_objectives.is_none()
            && epoch.declared_extension_objective_entries.is_none()
            && self
                .last_checked_sat_refutation
                .as_ref()
                .is_some_and(|checked| {
                    let ok = checked.is_current_for(
                        &epoch.authority_epoch,
                        &epoch.source_context_stamp,
                        &epoch.assertions,
                        assumptions,
                    );
                    if !ok {
                        probe_cert_reject(|| {
                            "checked SAT sidecar present but NOT current for this query".to_string()
                        });
                    }
                    ok
                })
    }

    /// Independently prove the exact source query in the bounded Bool/BV
    /// fragment. Unsupported source forms leave publication to the original
    /// proof-failure policy; a supported query that is SAT or whose proof cannot
    /// be surfaced fails closed instead of trying another solver lane after
    /// contradictory semantic evidence.
    fn authenticate_bool_bv_query(
        &self,
        epoch: &UnsatQueryEpoch,
        assumptions: &[TermId],
    ) -> Result<Option<(AuthenticatedBoolBvUnsatQuery, Box<[TermId]>)>, UnsatCertificationError>
    {
        if !epoch.declared_extension.is_empty() || epoch.declared_extension_objectives.is_some() {
            return Ok(None);
        }

        let root_count = epoch
            .assertions
            .len()
            .checked_add(assumptions.len())
            .ok_or_else(|| UnsatCertificationError::StrictProofRejected {
                reason: "Bool/BV query root count overflow".to_string(),
            })?;
        let mut exact_roots = Vec::new();
        exact_roots.try_reserve_exact(root_count).map_err(|error| {
            UnsatCertificationError::StrictProofRejected {
                reason: format!("Bool/BV query root allocation failed: {error}"),
            }
        })?;
        exact_roots.extend_from_slice(&epoch.assertions);
        exact_roots.extend_from_slice(assumptions);

        if self.make_should_stop()() {
            return Err(UnsatCertificationError::StrictProofRejected {
                reason: "Bool/BV authentication cancelled before proof production".to_string(),
            });
        }
        match ay_proof::authenticate_bool_bv_unsat_query(
            &self.ctx.terms,
            &exact_roots,
            self.current_solve_deadline(),
        ) {
            Ok(evidence) => Ok(Some((evidence, exact_roots.into_boxed_slice()))),
            Err(error) if error.is_unsupported_fragment() => Ok(None),
            Err(error) => Err(UnsatCertificationError::StrictProofRejected {
                reason: format!("independent source-level Bool/BV check rejected query: {error}"),
            }),
        }
    }

    /// Independently interpret the exact source query in the bounded
    /// Bool/Int/BV fragment.  This checker neither consumes the production
    /// bridge assertions nor repeats its AUFLIA solve: it symbolically checks
    /// width/range identities and exhausts finite source-derived domains.
    fn authenticate_bv_lia_query(
        &self,
        epoch: &UnsatQueryEpoch,
        assumptions: &[TermId],
    ) -> Result<Option<(AuthenticatedBvLiaUnsatQuery, Box<[TermId]>)>, UnsatCertificationError>
    {
        if !epoch.declared_extension.is_empty() || epoch.declared_extension_objectives.is_some() {
            return Ok(None);
        }

        let root_count = epoch
            .assertions
            .len()
            .checked_add(assumptions.len())
            .ok_or_else(|| UnsatCertificationError::StrictProofRejected {
                reason: "BV/LIA query root count overflow".to_string(),
            })?;
        let mut exact_roots = Vec::new();
        exact_roots.try_reserve_exact(root_count).map_err(|error| {
            UnsatCertificationError::StrictProofRejected {
                reason: format!("BV/LIA query root allocation failed: {error}"),
            }
        })?;
        exact_roots.extend_from_slice(&epoch.assertions);
        exact_roots.extend_from_slice(assumptions);

        if self.make_should_stop()() {
            return Err(UnsatCertificationError::StrictProofRejected {
                reason: "BV/LIA authentication cancelled before semantic replay".to_string(),
            });
        }
        match ay_proof::authenticate_bv_lia_unsat_query(
            &self.ctx.terms,
            &exact_roots,
            self.current_solve_deadline(),
        ) {
            Ok(evidence) => Ok(Some((evidence, exact_roots.into_boxed_slice()))),
            // A lane that cannot answer must DECLINE, not veto. See
            // `is_capability_decline`: exhausting this lane's own bounded budget
            // used to reject the whole certification, killing the deferred-trust
            // discharge that runs next.
            Err(error) if error.is_capability_decline() => Ok(None),
            Err(error) => Err(UnsatCertificationError::StrictProofRejected {
                reason: format!("independent source-level BV/LIA check rejected query: {error}"),
            }),
        }
    }

    /// Re-discharge the whole authored problem for a context-dependent trust
    /// clause in a fresh executor.
    ///
    /// Repeating the raw `Unsat` verdict is not sufficient: the fresh solve must
    /// also emit a proof accepted by the plain strict checker. This keeps the
    /// fallback non-circular when the same wrong-UNSAT engine path is repeatable.
    fn reconfirms_unsat_within(
        &self,
        problem: &[TermId],
        limits: FreshReconfirmationLimits,
    ) -> bool {
        if problem.is_empty() {
            // An empty conjunction is satisfiable; there is nothing to confirm.
            return false;
        }
        let conflict_limit =
            tighter_optional_limit(self.resource_limit(), Some(limits.max_conflicts));
        let decision_limit =
            tighter_optional_limit(self.decision_limit(), Some(limits.max_decisions));
        if conflict_limit == Some(0) || decision_limit == Some(0) {
            return false;
        }
        let mut exec = Executor::new();
        exec.ctx = self.ctx.clone();
        // Re-decide the AUTHORED problem, NOT `self.ctx.assertions` — the same
        // set steps (1) and (2) use, which `proof_export_scope_assertions`
        // builds to INCLUDE the query's `check-sat-assuming` assumptions.
        //
        // `ctx.assertions` holds the base alone. For `check-sat-assuming A` the
        // published claim is `base AND A |= false`, so re-solving the base by
        // itself asks a strictly STRONGER question: for
        // `(assert (=> p (< x 0))) (assert (> x 0)) (check-sat-assuming (p))`
        // the base is plainly satisfiable with `p` false, so this declined and a
        // CORRECT `unsat` was published UNCONFIRMED. Sound but over-conservative
        // — `base |= false` implies `base AND A |= false`, never the reverse.
        exec.ctx.assertions = problem.to_vec();
        // Mint exact authored-root/proof provenance for the nested obligation.
        // We intentionally run only the PLAIN strict checker below rather than
        // `certify_unsat_for_publication`: this method is itself the
        // deferred-trust fallback, so invoking that rescue recursively would
        // let a trust-bearing proof corroborate another trust-bearing proof.
        exec.begin_public_solve(false);
        exec.bind_unsat_query_assumptions(&[]);
        // This is an ACCEPTING step, so its operating boundary must be a
        // deterministic count rather than elapsed wall time. These fixed caps
        // win over executor defaults and AY_NO_GROUND_BUDGET, but never widen a
        // tighter caller-supplied deterministic limit. Preserve the outer
        // cancellation/deadline/memory envelope as well; any stop, count
        // exhaustion, or incomplete result declines.
        exec.set_resource_limit(conflict_limit);
        exec.set_decision_limit(decision_limit);
        // The caller's absolute deadline is a hard fail-closed ceiling for
        // certification, not the nominal quantified timeout that ordinary
        // solves may relax into a later hang-protection backstop.
        exec.set_quantifier_deadline_policy(QuantifierDeadlinePolicy::Exact);
        exec.set_memory_limit(self.memory_limit());
        exec.set_solve_controls(self.solve_interrupt.clone(), self.solve_deadline.get());
        let trace_rc = std::env::var_os("AY_PHASE_TRACE").is_some();
        let verdict = exec.check_sat();
        if !matches!(verdict, Ok(ref result) if result.is_unsat()) {
            if trace_rc {
                eprintln!("c phase-trace reconfirm DECLINED at re-solve verdict={verdict:?}");
            }
            return false;
        }
        if trace_rc {
            eprintln!(
                "c phase-trace reconfirm re-solve returned UNSAT; now strict-checking its proof"
            );
        }
        // This is an internal soundness certificate even when the caller did
        // not request a user-visible proof artifact. Read the proof tracker
        // output directly; `last_proof()` intentionally hides it unless output
        // production was requested.
        let Some(proof) = exec.last_proof.as_ref() else {
            if trace_rc {
                eprintln!("c phase-trace reconfirm DECLINED: re-solve produced no proof");
            }
            return false;
        };
        let strict = exec.check_proof_strict_with_datatypes(proof);
        if trace_rc {
            match &strict {
                Ok(_) => eprintln!("c phase-trace reconfirm ACCEPTED"),
                Err(e) => eprintln!(
                    "c phase-trace reconfirm DECLINED: strict check of re-solve proof failed: {e}"
                ),
            }
        }
        strict.is_ok()
    }

    /// The MINIMAL authored obligation for the step-(4) corroborating re-solve.
    ///
    /// `problem_assertions_for_strict_proof` is a deliberate SUPERSET, and that
    /// is right for the freshness and authority tests in steps (1)-(3), where
    /// extra terms only make the test stricter. It is the wrong input to a
    /// RE-SOLVE. It folds in `last_proof_rebuild_originals`, which carries
    /// ALPHA-RENAMED copies of the background `forall` axioms; renamed binders
    /// are not hash-cons-equal, so the nested solve carries every quantified
    /// axiom TWICE and pays for instantiating both.
    ///
    /// Measured on the `ext_eq_7956` fixture: 26 assertions, 203_520 decisions,
    /// 5.85s versus 16 assertions, 110_953 decisions, 2.90s — the same `Unsat`,
    /// half the work. That margin is the whole defect. The nominal
    /// `WHOLE_PROBLEM_RESOLVE_BUDGET_MS` is not the operative wall:
    /// `install_quantifier_deadline_backstop` extends the deadline by
    /// `remaining * (QUANTIFIED_BACKSTOP_FACTOR - 1)`, so the real wall is 4x
    /// the budget, and a 5.85s re-solve sat at 1.37x margin against it. Any CPU
    /// contention past ~1.4x flipped a correct `unsat` to `unknown`. Halving the
    /// work takes the margin to 2.7x; measured 6/6 correct at a load average of
    /// 18, where the superset scored 0/6.
    ///
    /// SUBSET-ONLY, and that is the entire soundness argument. If the minimal
    /// scope is not contained in `problem` this returns `problem` unchanged, so
    /// the re-solve can only ever be asked a question at least as strong as
    /// today's. Note what the guard does NOT buy: `problem` already unions the
    /// assumptions and the rebuild originals, so a solver-derived term that also
    /// appears in `problem` passes it. It buys MONOTONICITY, not provenance.
    ///
    /// The assumptions union is required, not tidiness: for
    /// `check-sat-assuming A` the published claim is `base AND A |= false`, and
    /// re-solving the base alone asks a strictly stronger question that
    /// previously threw away correct refutations (see the note in
    /// [`Self::reconfirms_unsat_within`]).
    ///
    /// COUPLING, load-bearing and previously undocumented: branch (1) below is
    /// dead on every real query. `check_sat.rs` saves and restores
    /// `self_check_authored_assertions` around the solve, so it is `None` at
    /// certification time by design and only the `ctx.assertions` fallback runs.
    /// That fallback is authored-only SOLELY because `check_sat.rs` restores
    /// `scope_tracked_assertions` into `ctx.assertions` on exit. If that restore
    /// ever stops happening, this scope silently becomes the post-preprocessing
    /// window and the `debug_assert!` below is what should catch it.
    fn authored_corroboration_scope(&self, problem: &[TermId]) -> Vec<TermId> {
        let mut scope = self
            .self_check_authored_assertions
            .clone()
            .unwrap_or_else(|| self.ctx.assertions.clone());
        if let Some(assumptions) = self.last_assumptions.as_ref() {
            for &assumption in assumptions {
                if !scope.contains(&assumption) {
                    scope.push(assumption);
                }
            }
        }
        for extension in self.declared_obligation_extension() {
            if !scope.contains(&extension) {
                scope.push(extension);
            }
        }
        debug_assert!(
            scope.iter().all(|t| problem.contains(t)),
            "the corroboration scope must stay a subset of the strict-proof \
             problem; a term outside it would mean the re-solve is answering a \
             question the publication never claimed"
        );
        if !scope.iter().all(|t| problem.contains(t)) {
            return problem.to_vec();
        }
        scope
    }

    fn redecides_definitive_sat_within(&self, authored: &[TermId], budget_ms: u64) -> bool {
        if authored.is_empty() {
            return false;
        }
        let local_conflict_limit =
            crate::pipeline_fns::effective_conflict_allowance(None, self.ground_budget_enabled());
        let local_decision_limit =
            crate::pipeline_fns::effective_decision_allowance(None, self.ground_budget_enabled());
        let conflict_limit = tighter_optional_limit(self.resource_limit(), local_conflict_limit);
        let decision_limit = tighter_optional_limit(self.decision_limit(), local_decision_limit);
        if conflict_limit == Some(0) || decision_limit == Some(0) {
            return false;
        }
        let mut exec = Executor::new();
        exec.ctx = self.ctx.clone();
        // Re-decide the AUTHORED assertions, NOT `self.ctx.assertions`.
        //
        // By certification time the working set has been through the solve
        // pipeline: `flatten_and_strip_quantifiers` has removed the quantifiers,
        // CE lemmas have been pushed, preprocessing has run. That formula is
        // strictly WEAKER than the user's problem, so it is routinely satisfiable
        // even when the authored problem is not — whereupon this guard reports
        // "definitive SAT", concludes the refutation is forged, and destroys a
        // CORRECT `unsat`.
        //
        // Measured: 13 of the `ay-dpll --lib` failures were this guard rejecting
        // valid refutations with "forged UNSAT: a fresh Executor independently
        // re-decides the authored assertions as DEFINITIVE SAT". The message
        // said "authored"; the code passed the working set.
        //
        // The guard remains downgrade-only either way, so this was a
        // completeness bug rather than a soundness one — but silently discarding
        // sound answers is precisely the failure mode this funnel exists to
        // prevent.
        exec.ctx.assertions = authored.to_vec();
        let local_deadline =
            ay_core::time::Instant::now().checked_add(std::time::Duration::from_millis(budget_ms));
        let outer_deadline = self.solve_deadline.get();
        let deadline = match (outer_deadline, local_deadline) {
            (Some(outer), Some(local)) => Some(outer.min(local)),
            (Some(deadline), None) | (None, Some(deadline)) => Some(deadline),
            (None, None) => None,
        };
        // Although this guard is downgrade-only, it is still part of the
        // caller's solve/publication transaction. Never let its private latency
        // cap replace an earlier caller deadline, and do not let quantified
        // solving relax either deadline into a later backstop. The same outer
        // interrupt and effective RSS ceiling remain authoritative throughout.
        exec.set_resource_limit(conflict_limit);
        exec.set_decision_limit(decision_limit);
        // The effective limits above are now explicit. Disable the fresh
        // executor's independent default so it cannot silently replace a
        // caller opt-out (or reintroduce a limit when both sides are unbounded).
        exec.set_ground_budget_enabled(false);
        exec.set_quantifier_deadline_policy(QuantifierDeadlinePolicy::Exact);
        exec.set_memory_limit(self.memory_limit());
        exec.set_solve_controls(self.solve_interrupt.clone(), deadline);
        matches!(exec.check_sat(), Ok(result) if result.is_sat())
    }

    fn discharge_trust_steps_for_certification(
        &self,
        plain_error: &ay_proof::ProofCheckError,
    ) -> Result<(), UnsatCertificationError> {
        let reject = |reason: String| UnsatCertificationError::StrictProofRejected { reason };

        // Depth 0 only. Raising this limit was TRIED AND MEASURED: 64 of the
        // `ay-dpll --lib` certification rejections report "discharge not attempted"
        // from this branch, which looks like the guard starving the rescue of its
        // own evidence — a nested solve that leans on a trust step cannot discharge
        // it, publishes `unknown`, and so the outer `reconfirms_unsat_within` sees
        // a non-`unsat` and declines. Allowing two levels instead of one moved the
        // failure count by exactly ZERO (115 -> 115, 483.3s -> 483.5s), so those
        // nested downgrades are not what blocks the outer rescue. The limit stays
        // at depth 0: no measured benefit is worth extra recursion surface in a
        // mandatory soundness gate.
        if TRUST_DISCHARGE_DEPTH.with(|depth| depth.get()) > 0 {
            return Err(reject(format!(
                "{plain_error}; deferred-trust discharge not attempted: already \
                 inside a nested discharge solve"
            )));
        }

        struct DepthGuard;
        impl Drop for DepthGuard {
            fn drop(&mut self) {
                TRUST_DISCHARGE_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
            }
        }
        TRUST_DISCHARGE_DEPTH.with(|depth| depth.set(depth.get() + 1));
        let _guard = DepthGuard;

        // (1) Forged-UNSAT guard, dominant — but BUDGETED.
        //
        // The API-layer guard re-solves with no deadline, which is fine there
        // because it runs once per public call. Here it runs on the rejection
        // path of every proof that leaned on a trust step, so an unbounded solve
        // would add unbounded latency to verdicts that are being DOWNGRADED
        // anyway. Measured before this budget: `group_quantifiers` went 2.7s ->
        // 20.1s. The guard is downgrade-only, so cutting it short can only cost
        // the downgrade it would have forced, never soundness — and the
        // per-clause discharge in (3) still has to pass.
        const FORGED_GUARD_BUDGET_MS: u64 = 250;
        // The whole-problem re-solve runs at most once per certification and only
        // after per-clause discharge has already failed. Its conflict/decision
        // allowances are fixed above; do not replace them with a wall-clock
        // accepting boundary. MEASURED NULL — raising the former wall budget did
        // not rescue the residual
        // "a collected trust clause is not a standalone theory tautology AND the
        // authored assertions could not be independently re-solved as UNSAT"
        // rejections. A census at this commit counted 8 of them, and raising the
        // budget 30x (2000 -> 60000) cleared exactly ONE:
        //
        //   group_auflia 28 -> 27, group_bv 5 -> 5, group_arrays 7 -> 7,
        //   group_lia 7 -> 7, group_theory_misc 4 -> 4
        //
        // while `group_lia`'s wall clock went 7.1s -> 30.0s. Those eight are
        // STRUCTURAL, not budget-bound. And a longer fixed budget inside a
        // MANDATORY gate is actively harmful: it is the reason bucket counts move
        // with machine load at all, since this re-solve is an ACCEPTING step, so
        // a slow machine silently downgrades correct refutations.
        // AND THE DEEPER PROBLEM: a wall-clock budget inside a MANDATORY gate
        // makes the published VERDICT NONDETERMINISTIC. Measured on
        // `auflia_verification_consumer_ext_eq_7956::test_quantifier_consumer_singleton_prefix_array_ext_eq_proves_first_element`,
        // six release runs of the identical binary on the identical input:
        //
        //     unknown unknown unknown unsat unsat unsat
        //
        // AY computes the correct `unsat` every time; whether it PUBLISHES it
        // depends on whether this re-solve finishes inside 2000ms. The same
        // query answers differently run to run, which is a worse property than
        // the incompleteness it is trading against — a caller cannot tell a
        // capability limit from a busy machine.
        //
        // (In debug the same test fails 6/6, so the nondeterminism is
        // release-only; do not conclude from a debug run that it is stable.)
        //
        // MEASURED NULL #2 — swapping the wall clock for a DETERMINISTIC decision
        // budget does not fix it either, and costs 2-4x wall time. Tried:
        // `set_decision_limit(2_000_000)` as the operative bound with the wall
        // clock widened to a 30s hang-backstop, following the
        // `DEFAULT_GROUND_DECISION_ALLOWANCE` precedent. Result on the flaky
        // test: still 5 of 6 runs `unknown`, and each run 20-35s instead of 9s.
        //
        // CORRECTED — the "why" first recorded here was wrong, and the wrong
        // diagnosis is worth more than the null. It said the re-solve "genuinely
        // does not converge". It converges, deterministically: `Unsat`, 365
        // conflicts, 203_520 decisions, 5.79-6.01s, the SAME decision count on
        // every run and in every arm. Null #2 failed for a mundane reason —
        // 2_000_000 decisions is ~10x more than the re-solve ever needs, so that
        // bound was simply never reached and the wall clock still decided.
        //
        // Nor is 2000ms the operative wall. `install_quantifier_deadline_backstop`
        // extends the deadline by `remaining * (QUANTIFIED_BACKSTOP_FACTOR - 1)`,
        // so the real bound here is 4x this constant = 8000ms, and a 5.85s
        // re-solve sat at just 1.37x margin. That margin — not chance, and not
        // non-convergence — is the entire nondeterminism: contention slowing the
        // box past ~1.4x flips a correct `unsat` to `unknown`. Sweeping the
        // budget across 2000 / 10000 / 60000 / 300000 / none gives the identical
        // 203_520 decisions, which is why every "raise the number" experiment
        // came back null.
        //
        // WHAT ACTUALLY FIXED IT: halving the WORK instead of widening the bound
        // — see `authored_corroboration_scope`, which stops feeding the re-solve
        // two alpha-renamed copies of every quantified axiom. 110_953 decisions,
        // 2.90s, margin 2.7x, and 6/6 correct at a load average of 18 where the
        // superset scored 0/6.
        //
        // STILL OPEN, and deliberately not papered over: the authored-16 re-solve
        // needs 110_953 decisions where the identical COLD solve of the same
        // query needs 19. E-matching is identical in both (2 rounds, 13
        // instances), so it is downstream of instantiation; a fresh `Context`
        // reproduces the numbers exactly, ruling out inherited state. Unexplained.
        // This change buys margin, it does not close that gap. The accepting
        // step also uses explicit conflict and decision allowances rather than
        // a machine-load-sensitive elapsed-time cutoff; caller cancellation
        // remains a fail-closed external stop.
        // The guard must re-decide the AUTHORED problem, so its assertions have
        // to be resolved before it runs — see the note on
        // `redecides_definitive_sat_within` for why using the working set here
        // silently destroys correct refutations.
        let decls = self.datatype_decls_for_strict_proof();
        let selectors = self.ctor_selector_decls_for_strict_proof();
        let problem = self.problem_assertions_for_strict_proof();
        if self.redecides_definitive_sat_within(&problem, FORGED_GUARD_BUDGET_MS) {
            return Err(reject(
                "forged UNSAT: a fresh Executor independently re-decides the \
                 authored assertions as DEFINITIVE SAT, so the trust-fallback \
                 refutation is not reproducible"
                    .to_string(),
            ));
        }

        // (2) Full strict validation, deferring only `trust`.
        let proof = self
            .last_proof
            .as_ref()
            .ok_or(UnsatCertificationError::MissingProof)?;
        let collected = ay_proof::check_proof_collecting_trust_with_context(
            proof,
            &self.ctx.terms,
            (!decls.is_empty()).then_some(decls.as_slice()),
            (!selectors.is_empty()).then_some(selectors.as_slice()),
            Some(problem.as_slice()),
        )
        .map_err(|error| {
            reject(format!(
                "deferred-trust discharge rejected a NON-trust step: {error}"
            ))
        })?;

        if tracing::enabled!(tracing::Level::DEBUG) {
            for (step, clause) in &collected {
                let rendered: Vec<String> = clause
                    .iter()
                    .map(|&literal| self.format_term(literal))
                    .collect();
                tracing::debug!(
                    ?step,
                    clause = ?rendered,
                    "collected deferred-trust obligation"
                );
            }
        }
        // Defensive: nothing deferred means the plain checker should have passed,
        // so honour its original rejection rather than inventing an acceptance.
        if collected.is_empty() {
            return Err(reject(format!(
                "{plain_error}; deferred-trust discharge declined: the collecting \
                 checker deferred no clause, so the plain rejection stands"
            )));
        }

        let corroboration_scope = self.authored_corroboration_scope(&problem);
        probe_cert_reject(|| self.deferred_trust_probe_message(&collected, &corroboration_scope));

        // (3) Independently discharge every deferred clause.
        let all_discharged = collected.iter().all(|(_, clause)| {
            crate::api::proofs::discharge_trust_clause(&self.ctx.terms, clause, &problem).is_some()
        });
        if all_discharged {
            return Ok(());
        }

        // (4) CONTEXT-DEPENDENT FALLBACK.
        //
        // A collected clause can be valid only GIVEN the other assertions rather
        // than standalone — the norm for LIA `Generic` lemmas (an ite-arithmetic
        // lemma whose proof is not Farkas-pure) and for the terminal trust step.
        // Such a clause is not a tautology, so (3) correctly declines it, but the
        // CONCLUSION can still be certified independently: re-decide the ORIGINAL
        // authored assertions in a fresh executor and require UNSAT.
        //
        // This certifies the property without trusting the original proof's
        // structure. The re-solve's own proof must pass plain strict checking;
        // a repeated raw UNSAT, trust/hole proof, SAT, or Unknown all decline.
        // Re-solve the MINIMAL authored obligation, not the strict-proof
        // superset — the superset carries every quantified axiom twice and
        // doubled the cost of this step. See `authored_corroboration_scope`.
        if self.reconfirms_unsat_within(&corroboration_scope, WHOLE_PROBLEM_RECONFIRMATION_LIMITS) {
            return Ok(());
        }

        Err(reject(format!(
            "{plain_error}; deferred-trust discharge failed: a collected trust \
             clause is not a standalone theory tautology AND the authored \
             assertions could not be independently re-solved as UNSAT"
        )))
    }

    /// Convert a live external stop into a fully revoked public Unknown.
    fn stop_declines_unsat_publication(&mut self) -> Option<SolveResult> {
        if !self.should_abort_theory_loop() {
            return None;
        }
        // `should_abort_theory_loop` records the exact interrupt/deadline/memory
        // origin. Publish that Unknown through the canonical revocation boundary
        // before any prechecked or freshly minted token can become observable.
        self.last_unsat_certificate = None;
        if !self.is_producing_proofs() {
            self.proof_tracker.disable();
        }
        Some(self.finalize_unknown_publication(SolveResult::Unknown))
    }

    /// Withhold a computed UNSAT whose terminal derivation chain is not
    /// trust-free, when strict proofs are on (#8759).
    ///
    /// This is the LIBRARY half of the gate, and it is the half that was
    /// missing. ay 0.5 published `UnknownReason::ProofTrusted` for this; 0.6
    /// deleted the variant and moved the decision into the `ay` binary, so a
    /// consumer that links `ay-dpll` and sets `:check-proofs-strict true` still
    /// received a raw `SolveResult::Unsat` for a proof no checker can confirm.
    /// The predicate is not a weaker restatement of what the certification
    /// funnel already does: a `Seq` refutation can be clean — zero `trust`,
    /// zero `hole`, every `assume` provenance-backed — mint a certificate, and
    /// still be unpresentable to carcara. Certification asks "did AY check
    /// it?"; this asks "can anyone else?".
    ///
    /// Applied to the verdict that certification is about to publish, never
    /// earlier. That ordering is the whole point: it mirrors the CLI's
    /// `output == "unsat" && strict_proofs && terminal_trust_detected`
    /// condition exactly, so the gate can only ever turn a would-be UNSAT into
    /// `Unknown`. Running it ahead of certification would instead relabel
    /// rejections the certification funnel already makes — `SelfCheckRejected`
    /// would silently become `ProofTrusted` — and would pre-empt
    /// `discharge_trust_steps_for_certification`, the one lane entitled to
    /// re-discharge a trust-kind rejection.
    fn decline_trust_bearing_unsat_under_strict_proofs(
        &mut self,
        published: SolveResult,
    ) -> SolveResult {
        if !published.is_unsat()
            || !self.strict_proofs_enabled()
            || !self.unsat_proof_terminal_trust_detected()
        {
            return published;
        }
        self.last_unsat_certificate = None;
        if !self.is_producing_proofs() {
            self.proof_tracker.disable();
        }
        self.publish_unknown_from_origin(UnknownOrigin::TerminalTrust);
        SolveResult::Unknown
    }

    /// The single public UNSAT publication funnel.
    ///
    /// Non-UNSAT results pass through after revoking stale UNSAT authority. A
    /// provisional UNSAT is retained only when one complete, exactly scoped
    /// certification lane mints a token; every failure revokes all query
    /// artifacts and becomes `Unknown`.
    pub(crate) fn certify_unsat_for_publication(
        &mut self,
        proposed: SolveResult,
        assumptions: &[TermId],
    ) -> SolveResult {
        let published = self.certify_unsat_presentation(proposed, assumptions);
        self.decline_trust_bearing_unsat_under_strict_proofs(published)
    }

    /// Certification proper. Every UNSAT it returns is one the mandatory
    /// certification lanes accepted; the caller above is the sole place a
    /// certified UNSAT can still be withheld.
    fn certify_unsat_presentation(
        &mut self,
        proposed: SolveResult,
        assumptions: &[TermId],
    ) -> SolveResult {
        if proposed.is_unsat() {
            if let Some(unknown) = self.stop_declines_unsat_publication() {
                return unknown;
            }
        }
        // A narrow exact-source lane may already have performed its complete
        // semantic check inside this same authored transaction. Preserve only
        // such a DISTINCT token, and only while its full query/source/term
        // snapshot is still current. An ordinary strict-proof token is never
        // preserved here, so this cannot mask a later structural rejection.
        let prechecked = self.last_unsat_certificate.take();
        if proposed.is_unsat()
            && assumptions.is_empty()
            && prechecked
                .as_ref()
                .is_some_and(|certificate| certificate.checked_exact_semantic_is_current(self))
        {
            // Evidence currentness can perform non-trivial structural work. A
            // stop arriving during that work must still dominate publication.
            if let Some(unknown) = self.stop_declines_unsat_publication() {
                return unknown;
            }
            self.last_unsat_certificate = prechecked;
            if !self.is_producing_proofs() {
                self.proof_tracker.disable();
            }
            return proposed;
        }
        self.last_unsat_certificate = None;
        if !proposed.is_unsat() {
            if !self.is_producing_proofs() {
                self.proof_tracker.disable();
            }
            return self.finalize_unknown_publication(proposed);
        }

        let minted = self.mint_unsat_certificate(assumptions);
        // Strict checking and independent discharge can outlive the solve that
        // produced the provisional verdict. Never retain their token after a
        // late interrupt/deadline/memory stop.
        if let Some(unknown) = self.stop_declines_unsat_publication() {
            return unknown;
        }
        let published = match minted {
            Ok(certificate) => {
                self.last_unsat_certificate = Some(certificate);
                proposed
            }
            Err(error) => {
                tracing::warn!(%error, "rejecting uncertified public UNSAT verdict");
                probe_cert_reject(|| error.to_string());
                self.reject_uncertified_verdict_for_publication(format!(
                    "computed UNSAT rejected by mandatory strict certification: {error}"
                ))
            }
        };
        if !self.is_producing_proofs() {
            self.proof_tracker.disable();
        }
        published
    }

    /// Whether the active solve is a public exact-query epoch whose eventual
    /// UNSAT publication must carry authored-scope certification.
    ///
    /// Strict proof checking is the primary lane; sealed independent fallback
    /// certificates remain explicitly classified. Internal disposable solves
    /// have no epoch and cannot borrow this publication requirement as
    /// authority.
    pub(crate) fn active_unsat_query_requires_strict_proof(&self) -> bool {
        self.unsat_query_epoch.is_some()
    }

    /// Consume the one-shot capability for the immediately preceding verdict.
    pub(crate) fn take_unsat_certificate(&mut self) -> Option<UnsatCertificate> {
        let certificate = self.last_unsat_certificate.take()?;
        let epoch = self.unsat_query_epoch.as_ref()?;
        let bound_assumptions = epoch.assumptions.as_deref()?;
        let current = match &certificate.0 {
            UnsatCertificateKind::StrictProof(scope)
            | UnsatCertificateKind::DischargedTrust(scope) => scope.is_current(self),
            UnsatCertificateKind::CheckedSatRefutation { checked, scope } => {
                let solver_assumptions_match = self.last_assumptions.as_deref()
                    == Some(bound_assumptions)
                    || (bound_assumptions.is_empty() && self.last_assumptions.is_none());
                scope.is_current(self)
                    && epoch.is_current(self)
                    && epoch.declared_extension.is_empty()
                    && epoch.declared_extension_entries.is_empty()
                    && epoch.declared_extension_objectives.is_none()
                    && epoch.declared_extension_objective_entries.is_none()
                    && solver_assumptions_match
                    && self
                        .proof_problem_assertion_provenance
                        .as_ref()
                        .is_some_and(|provenance| {
                            provenance.original_problem_assertions == epoch.assertions
                        })
                    && checked.is_current_for(
                        &epoch.authority_epoch,
                        &epoch.source_context_stamp,
                        &epoch.assertions,
                        bound_assumptions,
                    )
            }
            UnsatCertificateKind::CheckedBoolBv(checked) => checked.is_current(self),
            UnsatCertificateKind::CheckedBvLia(checked) => checked.is_current(self),
            UnsatCertificateKind::CheckedExactExists(evidence) => {
                self.exact_plain_hard_unsat_scope_is_current() && evidence.is_current(self)
            }
            UnsatCertificateKind::CheckedExactForallExists(evidence) => {
                self.exact_plain_hard_unsat_scope_is_current() && evidence.is_current(self)
            }
            UnsatCertificateKind::CheckedExactClosedForall(evidence) => {
                self.exact_plain_hard_unsat_scope_is_current() && evidence.is_current(self)
            }
            UnsatCertificateKind::CheckedExactForallUfGround(evidence) => {
                self.exact_plain_hard_unsat_scope_is_current() && evidence.is_current(self)
            }
            UnsatCertificateKind::CheckedExactFiniteExpansion(evidence) => {
                self.exact_plain_hard_unsat_scope_is_current() && evidence.is_current(self)
            }
        };
        current.then_some(certificate)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;
    use std::time::Duration;

    use ay_core::Proof;

    use super::*;
    use crate::executor::exact_exists_bounds::ExactExistsDecision;
    use crate::executor_types::UnknownReason;

    fn strict_boolean_contradiction(executor: &mut Executor) -> Vec<TermId> {
        // Match the small contradiction used by the established independent
        // trust-discharge test below. Raw authored roots avoid exercising the
        // unrelated parsed-surface proof reconstruction lane in a test whose
        // sole subject is propagation of external controls.
        let proposition = executor
            .ctx
            .terms
            .mk_var("reconfirmation_controls_p", ay_core::Sort::Bool);
        let not_proposition = executor.ctx.terms.mk_not_raw(proposition);
        executor.ctx.assertions = vec![proposition, not_proposition];
        executor.ctx.assertions.clone()
    }

    fn independently_checked_boolean_contradiction() -> (Executor, SolveResult) {
        let mut executor = Executor::new();
        let _problem = strict_boolean_contradiction(&mut executor);
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let proposed = executor
            .check_sat()
            .expect("contradictory Boolean units must solve");
        assert!(proposed.is_unsat());
        assert!(
            executor.last_checked_sat_refutation.is_some(),
            "the fixture requires an independently checked SAT refutation"
        );
        (executor, proposed)
    }

    fn satisfiable_boolean_assertion(executor: &mut Executor) -> TermId {
        let proposition = executor
            .ctx
            .terms
            .mk_var("forged_unsat_guard_controls_p", ay_core::Sort::Bool);
        executor.ctx.assertions = vec![proposition];
        proposition
    }

    fn pigeonhole_contradiction(executor: &mut Executor) -> Vec<TermId> {
        const PIGEONS: u32 = 8;
        const HOLES: u32 = 7;
        let mut smt = String::from("(set-logic QF_UF)\n");
        for pigeon in 1..=PIGEONS {
            for hole in 1..=HOLES {
                smt.push_str(&format!("(declare-const p_{pigeon}_{hole} Bool)\n"));
            }
        }
        for pigeon in 1..=PIGEONS {
            let choices: Vec<String> = (1..=HOLES)
                .map(|hole| format!("p_{pigeon}_{hole}"))
                .collect();
            smt.push_str(&format!("(assert (or {}))\n", choices.join(" ")));
        }
        for hole in 1..=HOLES {
            for first in 1..=PIGEONS {
                for second in (first + 1)..=PIGEONS {
                    smt.push_str(&format!(
                        "(assert (or (not p_{first}_{hole}) (not p_{second}_{hole})))\n"
                    ));
                }
            }
        }
        let commands = ay_frontend::parse(&smt).expect("pigeonhole fixture must parse");
        executor
            .execute_all(&commands)
            .expect("pigeonhole fixture must elaborate");
        executor.ctx.assertions.clone()
    }

    fn concrete_signed_add_safety_executor(lhs: &str, rhs: &str) -> Executor {
        let smt = format!(
            "(set-logic QF_BV)\n\
             (declare-const auth_a (_ BitVec 4))\n\
             (declare-const auth_b (_ BitVec 4))\n\
             (assert (= auth_a {lhs}))\n\
             (assert (= auth_b {rhs}))\n\
             (assert (=> (and (bvsgt auth_a #x0) (bvsgt auth_b #x0))\n\
                         (bvsgt (bvadd auth_a auth_b) #x0)))"
        );
        let commands = ay_frontend::parse(&smt).expect("Bool/BV fixture must parse");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("Bool/BV fixture must elaborate");
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        executor
    }

    fn wide_signed_keep_max_executor() -> Executor {
        let commands = ay_frontend::parse(
            "(set-logic QF_BV)\n\
             (declare-const auth_wide_lo (_ BitVec 128))\n\
             (declare-const auth_wide_hi (_ BitVec 128))\n\
             (assert (not (bvslt (_ bv0 128)\n\
                                (bvsub auth_wide_hi auth_wide_lo))))\n\
             (assert (bvslt auth_wide_lo auth_wide_hi))\n\
             (assert (bvsle (_ bv1 128) auth_wide_lo))",
        )
        .expect("wide Bool/BV fixture must parse");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("wide Bool/BV fixture must elaborate");
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        executor
    }

    fn mixed_bv_lia_bridge_executor(lower_bound: u32) -> Executor {
        let smt = format!(
            "(set-logic ALL)\n\
             (declare-const auth_mixed_x (_ BitVec 8))\n\
             (assert (> (bv2nat auth_mixed_x) {lower_bound}))\n\
             (assert (bvult auth_mixed_x #x03))"
        );
        let commands = ay_frontend::parse(&smt).expect("mixed BV/LIA fixture must parse");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("mixed BV/LIA fixture must elaborate");
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        executor
    }

    #[test]
    fn unsat_query_epoch_preserves_authority_across_append_only_term_growth() {
        let mut executor = Executor::new();
        let root = executor
            .ctx
            .terms
            .mk_fresh_var("unsat_epoch_append_root", ay_core::Sort::Bool);
        let assumption = executor
            .ctx
            .terms
            .mk_fresh_var("unsat_epoch_append_assumption", ay_core::Sort::Bool);
        executor.ctx.assertions = vec![root];
        executor.begin_unsat_query_epoch(&[root]);
        executor.bind_unsat_query_assumptions(&[assumption]);

        let _suffix = executor
            .ctx
            .terms
            .mk_fresh_var("unsat_epoch_unrelated_suffix", ay_core::Sort::Bool);

        assert!(executor
            .unsat_query_epoch
            .as_ref()
            .is_some_and(|epoch| epoch.is_current(&executor)));
        assert!(executor.checked_sat_refutation_query_scope().is_some());
    }

    #[test]
    fn unsat_query_epoch_rejects_reused_assertion_slot_before_mint() {
        let mut executor = Executor::new();
        let checkpoint = executor.ctx.terms.rollback_checkpoint();
        let root = executor
            .ctx
            .terms
            .mk_fresh_var("unsat_epoch_rolled_root", ay_core::Sort::Bool);
        executor.ctx.assertions = vec![root];
        executor.begin_unsat_query_epoch(&[root]);
        executor.bind_unsat_query_assumptions(&[]);

        executor.ctx.terms.rollback_to(checkpoint);
        let replacement = executor
            .ctx
            .terms
            .mk_fresh_var("unsat_epoch_replacement_root", ay_core::Sort::Bool);
        assert_eq!(replacement, root, "the canary must reuse the numeric slot");

        assert!(matches!(
            executor.mint_unsat_certificate(&[]),
            Err(UnsatCertificationError::StaleTermEntry)
        ));
        assert!(executor.checked_sat_refutation_query_scope().is_none());
    }

    #[test]
    fn unsat_query_epoch_rejects_reused_assumption_slot_before_mint() {
        let mut executor = Executor::new();
        let root = executor.ctx.terms.true_term();
        executor.ctx.assertions = vec![root];
        executor.begin_unsat_query_epoch(&[root]);
        let checkpoint = executor.ctx.terms.rollback_checkpoint();
        let assumption = executor
            .ctx
            .terms
            .mk_fresh_var("unsat_epoch_rolled_assumption", ay_core::Sort::Bool);
        executor.bind_unsat_query_assumptions(&[assumption]);

        executor.ctx.terms.rollback_to(checkpoint);
        let replacement = executor
            .ctx
            .terms
            .mk_fresh_var("unsat_epoch_replacement_assumption", ay_core::Sort::Bool);
        assert_eq!(
            replacement, assumption,
            "the canary must reuse the numeric slot"
        );

        assert!(matches!(
            executor.mint_unsat_certificate(&[replacement]),
            Err(UnsatCertificationError::StaleTermEntry)
        ));
        assert!(executor.checked_sat_refutation_query_scope().is_none());
    }

    #[test]
    fn unsat_query_rebind_captures_the_rebound_entry_identity() {
        let mut executor = Executor::new();
        let original = executor.ctx.terms.true_term();
        executor.begin_unsat_query_epoch(&[original]);
        let checkpoint = executor.ctx.terms.rollback_checkpoint();
        let rebound = executor
            .ctx
            .terms
            .mk_fresh_var("unsat_epoch_rebound_root", ay_core::Sort::Bool);
        assert!(executor.rebind_unsat_query_epoch_assertions(&[rebound]));
        let _suffix = executor
            .ctx
            .terms
            .mk_fresh_var("unsat_epoch_rebound_suffix", ay_core::Sort::Bool);
        assert!(executor
            .unsat_query_epoch
            .as_ref()
            .is_some_and(|epoch| epoch.term_entries_are_current(&executor)));

        executor.ctx.terms.rollback_to(checkpoint);
        let replacement = executor
            .ctx
            .terms
            .mk_fresh_var("unsat_epoch_rebound_replacement", ay_core::Sort::Bool);
        assert_eq!(
            replacement, rebound,
            "the canary must reuse the rebound slot"
        );
        assert!(!executor
            .unsat_query_epoch
            .as_ref()
            .expect("rebound epoch remains installed but stale")
            .term_entries_are_current(&executor));
    }

    #[test]
    fn source_bool_bv_refutation_mints_distinct_snapshot_bound_authority() {
        // Signed four-bit 7 + 1 wraps to -8, contradicting the asserted
        // positive-overflow safety implication.
        let mut executor = concrete_signed_add_safety_executor("#x7", "#x1");
        let proposed = executor
            .check_sat()
            .expect("the production Bool/BV solve must finish");
        assert!(proposed.is_unsat());
        // Isolate this lane from the ordinary strict proof and checked-SAT
        // sidecar. The source theorem independently authenticates the exact
        // query even when no Alethe presentation was produced.
        executor.last_checked_sat_refutation = None;
        executor.last_proof = None;
        let published = executor.certify_unsat_for_publication(proposed, &[]);
        assert!(published.is_unsat());
        assert!(matches!(
            executor
                .last_unsat_certificate
                .as_ref()
                .map(|token| &token.0),
            Some(UnsatCertificateKind::CheckedBoolBv(_))
        ));

        // Even an unrelated append changes the structural snapshot.  The
        // one-shot publication boundary must retire the already minted token.
        let _late = executor
            .ctx
            .terms
            .mk_var("auth_bv_late_append", ay_core::Sort::Bool);
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn wide_source_bool_bv_refutation_mints_checked_authority() {
        let mut executor = wide_signed_keep_max_executor();
        let proposed = executor
            .check_sat()
            .expect("the production wide Bool/BV solve must finish");
        assert!(proposed.is_unsat());

        // Force the source-bound lane: neither a translated presentation nor
        // the production SAT sidecar may account for publication.
        executor.last_checked_sat_refutation = None;
        executor.last_proof = None;
        let published = executor.certify_unsat_for_publication(proposed, &[]);
        assert!(published.is_unsat());
        let certificate = executor
            .last_unsat_certificate
            .as_ref()
            .expect("the source-bound refutation must mint an authority token");
        assert!(matches!(
            &certificate.0,
            UnsatCertificateKind::CheckedBoolBv(_)
        ));
        assert!(certificate.independently_verified());
        assert_eq!(
            certificate.command_admission(),
            CommandUnsatAdmission::CheckedBoolBv
        );

        let _late = executor
            .ctx
            .terms
            .mk_var("auth_wide_late_append", ay_core::Sort::Bool);
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn source_bool_bv_refutation_rejects_forged_unsat_for_sat_query() {
        let mut executor = concrete_signed_add_safety_executor("#x1", "#x1");
        executor.last_checked_sat_refutation = None;
        executor.last_proof = None;

        let published = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(published.is_unknown());
        assert!(executor.take_unsat_certificate().is_none());
        assert_eq!(
            executor.unknown_reason(),
            Some(UnknownReason::SelfCheckRejected)
        );
    }

    #[test]
    fn source_bv_lia_refutation_mints_distinct_snapshot_bound_authority() {
        // An unsigned eight-bit value below 3 cannot have bv2nat value above 5.
        let mut executor = mixed_bv_lia_bridge_executor(5);
        let proposed = executor
            .check_sat()
            .expect("the production mixed BV/LIA solve must finish");
        assert!(proposed.is_unsat());
        executor.last_checked_sat_refutation = None;
        executor.last_proof = None;

        let published = executor.certify_unsat_for_publication(proposed, &[]);
        assert!(published.is_unsat());
        assert!(matches!(
            executor
                .last_unsat_certificate
                .as_ref()
                .map(|token| &token.0),
            Some(UnsatCertificateKind::CheckedBvLia(_))
        ));

        let _late = executor
            .ctx
            .terms
            .mk_var("auth_bv_lia_late_append", ay_core::Sort::Bool);
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn source_bv_lia_refutation_rejects_forged_unsat_for_sat_query() {
        // x = 2 satisfies both roots, so source re-authentication must refuse
        // to turn a forged raw verdict into public UNSAT authority.
        let mut executor = mixed_bv_lia_bridge_executor(1);
        executor.last_checked_sat_refutation = None;
        executor.last_proof = None;

        let published = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(published.is_unknown());
        assert!(executor.take_unsat_certificate().is_none());
        assert_eq!(
            executor.unknown_reason(),
            Some(UnknownReason::SelfCheckRejected)
        );
    }

    #[test]
    fn control_lifetime_strict_unsat_reconfirms_without_an_external_stop() {
        let mut executor = Executor::new();
        let problem = strict_boolean_contradiction(&mut executor);
        assert!(executor.reconfirms_unsat_within(&problem, WHOLE_PROBLEM_RECONFIRMATION_LIMITS));
    }

    #[test]
    fn control_lifetime_fired_interrupt_declines_strict_unsat_reconfirmation() {
        let mut executor = Executor::new();
        let problem = strict_boolean_contradiction(&mut executor);
        executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
        assert!(!executor.reconfirms_unsat_within(&problem, WHOLE_PROBLEM_RECONFIRMATION_LIMITS));
    }

    #[test]
    fn control_lifetime_expired_deadline_declines_strict_unsat_reconfirmation() {
        let mut executor = Executor::new();
        let problem = strict_boolean_contradiction(&mut executor);
        let expired = ay_core::time::Instant::now()
            .checked_sub(Duration::from_millis(1))
            .expect("one millisecond must fit before the current instant");
        executor.set_solve_controls(None, Some(expired));
        assert!(!executor.reconfirms_unsat_within(&problem, WHOLE_PROBLEM_RECONFIRMATION_LIMITS));
    }

    #[test]
    fn control_lifetime_tiny_outer_rlimit_declines_strict_unsat_reconfirmation() {
        let mut executor = Executor::new();
        let problem = pigeonhole_contradiction(&mut executor);
        // PHP(8,7) is deliberately immune to the cheap zero-conflict
        // preprocessing that solves smaller pigeonholes. The established
        // one-conflict executor regression therefore makes this a deterministic
        // witness that the nested accepting solve did not replace the caller's
        // tighter `:rlimit` with its 400k local cap.
        executor.set_resource_limit(Some(1));
        assert!(!executor.reconfirms_unsat_within(&problem, WHOLE_PROBLEM_RECONFIRMATION_LIMITS));
    }

    #[test]
    fn control_lifetime_forged_unsat_guard_redecides_sat_without_an_external_stop() {
        let mut executor = Executor::new();
        let assertion = satisfiable_boolean_assertion(&mut executor);
        assert!(executor.redecides_definitive_sat_within(&[assertion], 60_000));
    }

    #[test]
    fn control_lifetime_fired_interrupt_declines_forged_unsat_guard() {
        let mut executor = Executor::new();
        let assertion = satisfiable_boolean_assertion(&mut executor);
        executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
        assert!(!executor.redecides_definitive_sat_within(&[assertion], 60_000));
    }

    #[test]
    fn control_lifetime_expired_outer_deadline_declines_forged_unsat_guard() {
        let mut executor = Executor::new();
        let assertion = satisfiable_boolean_assertion(&mut executor);
        let expired = ay_core::time::Instant::now()
            .checked_sub(Duration::from_millis(1))
            .expect("one millisecond must fit before the current instant");
        executor.set_solve_controls(None, Some(expired));
        assert!(!executor.redecides_definitive_sat_within(&[assertion], 60_000));
    }

    #[test]
    fn control_lifetime_exhausted_outer_decision_limit_declines_forged_unsat_guard() {
        let mut executor = Executor::new();
        let assertion = satisfiable_boolean_assertion(&mut executor);
        executor.set_decision_limit(Some(0));
        assert!(!executor.redecides_definitive_sat_within(&[assertion], 60_000));
    }

    #[test]
    fn control_lifetime_late_interrupt_revokes_strict_unsat_publication() {
        let mut executor = Executor::new();
        let _problem = strict_boolean_contradiction(&mut executor);
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let proposed = executor
            .check_sat()
            .expect("strict Boolean contradiction must solve");
        assert!(proposed.is_unsat());
        // The stop gate precedes strict checking. Seed an artifact explicitly
        // so this regression also proves the canonical Unknown transition
        // revokes proof state even if this tiny raw solve needs no exported
        // proof payload of its own.
        executor.last_proof = Some(Proof::new());
        assert!(executor.last_proof.is_some());

        executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
        let published = executor.certify_unsat_for_publication(proposed, &[]);

        assert!(published.is_unknown());
        assert_eq!(executor.unknown_reason(), Some(UnknownReason::Interrupted));
        assert_eq!(
            executor.unknown_origin(),
            Some(UnknownOrigin::InterruptFlag)
        );
        assert!(executor.take_unsat_certificate().is_none());
        assert!(executor.last_proof.is_none());
    }

    #[test]
    fn control_lifetime_expired_deadline_revokes_prechecked_exact_unsat() {
        let mut executor = Executor::new();
        let commands = ay_frontend::parse(
            "(set-logic LIA) \
             (assert (exists ((x Int)) (and (> x 0) (< x 1))))",
        )
        .expect("exact-exists UNSAT fixture must parse");
        executor
            .execute_all(&commands)
            .expect("exact-exists UNSAT fixture must elaborate");
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let permit = executor
            .detached_authored_plain_hard_permit_for_test()
            .expect("plain hard fixture must mint test authority");
        let ExactExistsDecision::Unsat(evidence) =
            executor.try_authorize_exact_exists_decision(permit)
        else {
            panic!("unit-width integer interval must be exactly UNSAT");
        };
        let proposed = executor.emit_checked_exact_exists_unsat(evidence);
        assert!(proposed.is_unsat());
        assert!(executor.last_unsat_certificate.is_some());

        let expired = ay_core::time::Instant::now()
            .checked_sub(Duration::from_millis(1))
            .expect("one millisecond must fit before the current instant");
        executor.set_solve_controls(None, Some(expired));
        let published = executor.certify_unsat_for_publication(proposed, &[]);

        assert!(published.is_unknown());
        assert_eq!(executor.unknown_reason(), Some(UnknownReason::Timeout));
        assert_eq!(
            executor.unknown_origin(),
            Some(UnknownOrigin::SolveDeadline)
        );
        assert!(executor.take_unsat_certificate().is_none());
    }

    fn prechecked_exact_forall_exists_unsat() -> (Executor, SolveResult) {
        let mut executor = Executor::new();
        let commands = ay_frontend::parse(
            "(set-logic LIA) \
             (assert (forall ((x Int)) (exists ((y Int)) \
                (and (<= y x) (>= y (+ x 1))))))",
        )
        .expect("exact forall/exists fixture must parse");
        executor
            .execute_all(&commands)
            .expect("exact forall/exists fixture must elaborate");
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let evidence = executor
            .try_authorize_current_query_exact_forall_exists_unsat()
            .expect("exact authored query must authenticate");
        let proposed = executor.emit_checked_exact_forall_exists_unsat(evidence);
        assert!(proposed.is_unsat());
        (executor, proposed)
    }

    const EXACT_EXISTS_UNSAT_SCRIPT: &str =
        "(set-logic LIA) (assert (exists ((x Int)) (and (> x 0) (< x 1))))";
    const EXACT_FORALL_EXISTS_UNSAT_SCRIPT: &str = "(set-logic LIA) \
         (assert (forall ((x Int)) (exists ((y Int)) \
            (and (<= y x) (>= y (+ x 1))))))";
    const EXACT_CLOSED_FORALL_UNSAT_SCRIPT: &str = "(set-logic UFLIA) \
         (assert (forall ((y Int)) (= (rem 2 y) 0)))";
    const EXACT_CLOSED_BV_FORALL_UNSAT_SCRIPT: &str = "(set-logic BV) \
         (assert (forall ((x (_ BitVec 8))) (bvult x (_ bv255 8))))";
    const EXACT_FORALL_UF_GROUND_UNSAT_SCRIPT: &str = "(set-logic UFLIA) \
         (declare-fun f (Int) Int) \
         (assert (forall ((x Int)) (>= (f (+ x 1)) 0))) \
         (assert (= (f 3) (- 1)))";
    const EXACT_FINITE_EXPANSION_UNSAT_SCRIPT: &str = "(set-logic ALL) \
         (declare-const c (_ BitVec 8)) \
         (assert (forall ((x (_ BitVec 8))) \
           (or (bvult #x00 x) (= x #x00)))) \
         (assert (= c #x01)) \
         (assert (= c #x02))";

    fn load_exact_closed_forall(source: &str) -> Executor {
        let commands = ay_frontend::parse(source).expect("closed-forall fixture must parse");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("closed-forall fixture must elaborate");
        executor
    }

    fn bind_exact_closed_forall_query(executor: &mut Executor) -> TermId {
        let [forall_id] = executor.ctx.assertions.as_slice() else {
            panic!("closed-forall fixture must have one authored root");
        };
        let forall_id = *forall_id;
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        forall_id
    }

    fn load_exact_finite_expansion(source: &str) -> Executor {
        let commands = ay_frontend::parse(source).expect("finite-expansion fixture must parse");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("finite-expansion fixture must elaborate");
        executor
    }

    fn bind_empty_exact_finite_expansion_query(executor: &mut Executor) {
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
    }

    fn exact_forall_uf_ground_evidence(executor: &mut Executor) -> CheckedExactForallUfGroundUnsat {
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        executor
            .try_authorize_current_query_exact_forall_uf_ground_unsat()
            .expect("fixture has an exact authored forall-instance/pin contradiction")
    }

    fn exact_finite_expansion_evidence(
        executor: &mut Executor,
    ) -> CheckedExactFiniteExpansionUnsat {
        bind_empty_exact_finite_expansion_query(executor);
        executor
            .try_authorize_current_query_exact_finite_expansion_unsat()
            .expect("fixture has an exact canonical expansion assignment clash")
    }

    fn execute_authored_script(
        executor: &mut Executor,
        commands: &[ay_frontend::Command],
    ) -> Vec<String> {
        let mut outputs = Vec::new();
        for command in commands {
            if let Some(output) = executor
                .execute_authored(command)
                .expect("authored exact semantic script must execute")
            {
                outputs.push(output);
            }
        }
        outputs
    }

    #[test]
    fn exact_semantic_unsat_default_verdicts_remain_unsat() {
        for (source, expected_admission) in [
            (
                EXACT_EXISTS_UNSAT_SCRIPT,
                CommandUnsatAdmission::CheckedExactExists,
            ),
            (
                EXACT_FORALL_EXISTS_UNSAT_SCRIPT,
                CommandUnsatAdmission::CheckedExactForallExists,
            ),
            (
                EXACT_CLOSED_FORALL_UNSAT_SCRIPT,
                CommandUnsatAdmission::CheckedExactClosedForall,
            ),
            (
                EXACT_CLOSED_BV_FORALL_UNSAT_SCRIPT,
                CommandUnsatAdmission::CheckedExactClosedForall,
            ),
            (
                EXACT_FORALL_UF_GROUND_UNSAT_SCRIPT,
                CommandUnsatAdmission::CheckedExactForallUfGround,
            ),
        ] {
            let commands = ay_frontend::parse(&format!("{source} (check-sat)"))
                .expect("exact semantic UNSAT fixture must parse");
            let mut executor = Executor::new();
            let outputs = execute_authored_script(&mut executor, &commands);

            assert_eq!(outputs, vec!["unsat"]);
            assert_eq!(
                executor.last_command_unsat_admission,
                Some(expected_admission),
                "default verdict must come from the intended exact semantic lane"
            );
            assert!(
                executor.last_unsat_proof_reconstruction_suppressed,
                "semantic-only UNSAT must not expose an unrelated proof trace"
            );
        }
    }

    #[test]
    fn exact_closed_forall_token_is_one_shot_and_source_bound() {
        let mut executor = load_exact_closed_forall(EXACT_CLOSED_FORALL_UNSAT_SCRIPT);
        let forall_id = bind_exact_closed_forall_query(&mut executor);
        let three = executor.ctx.terms.mk_int(3.into());
        let evidence = executor
            .try_authorize_current_query_exact_closed_forall_unsat(forall_id, &[three])
            .expect("rem 2 3 = 0 is an exact false authored instance");

        let proposed = executor.emit_checked_exact_closed_forall_unsat(evidence);
        assert!(proposed.is_unsat());
        let published = executor.certify_unsat_for_publication(proposed, &[]);
        assert!(published.is_unsat());
        let certificate = executor
            .take_unsat_certificate()
            .expect("exact closed-forall token must cross publication once");
        assert!(certificate.exact_semantic_verified());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn exact_closed_forall_bv_token_requires_exact_width_literal() {
        let mut executor = load_exact_closed_forall(EXACT_CLOSED_BV_FORALL_UNSAT_SCRIPT);
        let forall_id = bind_exact_closed_forall_query(&mut executor);
        let wrong_width = executor.ctx.terms.mk_bitvec(255.into(), 16);
        assert!(executor
            .try_authorize_current_query_exact_closed_forall_unsat(forall_id, &[wrong_width])
            .is_none());

        let max = executor.ctx.terms.mk_bitvec(255.into(), 8);
        let evidence = executor
            .try_authorize_current_query_exact_closed_forall_unsat(forall_id, &[max])
            .expect("x = #xff must be an exact false BV8 instance");
        let proposed = executor.emit_checked_exact_closed_forall_unsat(evidence);
        assert!(proposed.is_unsat());
        assert!(executor
            .certify_unsat_for_publication(proposed, &[])
            .is_unsat());
        assert!(executor
            .take_unsat_certificate()
            .is_some_and(|certificate| certificate.exact_semantic_verified()));
    }

    #[test]
    fn exact_closed_forall_rejects_non_authored_root() {
        let mut executor = load_exact_closed_forall(EXACT_CLOSED_FORALL_UNSAT_SCRIPT);
        let unasserted_forall = executor.ctx.assertions[0];
        executor.ctx.assertions = vec![executor.ctx.terms.true_term()];
        let _authored_true = bind_exact_closed_forall_query(&mut executor);
        let three = executor.ctx.terms.mk_int(3.into());

        assert!(executor
            .try_authorize_current_query_exact_closed_forall_unsat(unasserted_forall, &[three],)
            .is_none());
    }

    #[test]
    fn exact_closed_forall_rejects_private_and_canonical_rem_declarations() {
        let mut private = load_exact_closed_forall(
            "(set-logic ALL) \
             (declare-fun rem (Int Int) Int) \
             (assert (forall ((y Int)) (= (rem 2 y) 0)))",
        );
        let private_forall = bind_exact_closed_forall_query(&mut private);
        let private_three = private.ctx.terms.mk_int(3.into());
        assert!(
            private
                .try_authorize_current_query_exact_closed_forall_unsat(
                    private_forall,
                    &[private_three],
                )
                .is_none()
        );

        // Bypass the collision-safe native registration API deliberately: a
        // live declaration now owns canonical `rem`, while the already-parsed
        // root still contains the builtin application. The positive identity
        // check must reject this malformed source environment.
        let mut canonical = load_exact_closed_forall(EXACT_CLOSED_FORALL_UNSAT_SCRIPT);
        let forged_owner = canonical
            .ctx
            .terms
            .mk_fresh_var("forged_canonical_rem_owner", CoreSort::Int);
        canonical
            .ctx
            .register_symbol("rem".to_string(), forged_owner, CoreSort::Int);
        let canonical_forall = bind_exact_closed_forall_query(&mut canonical);
        let canonical_three = canonical.ctx.terms.mk_int(3.into());
        assert!(canonical
            .try_authorize_current_query_exact_closed_forall_unsat(
                canonical_forall,
                &[canonical_three],
            )
            .is_none());
    }

    #[test]
    fn exact_closed_forall_rejects_true_and_undefined_instances() {
        let mut true_executor =
            load_exact_closed_forall("(set-logic LIA) (assert (forall ((y Int)) (= y y)))");
        let true_forall = bind_exact_closed_forall_query(&mut true_executor);
        let one = true_executor.ctx.terms.mk_int(1.into());

        let (_, body) =
            crate::executor::quantifier_loop::closed_quantifier_free_forall_literal_parts(
                &true_executor.ctx.terms,
                true_forall,
            )
            .expect("fixture is in the exact literal fragment");
        let substitution: HashMap<String, TermId> = [("y".to_string(), one)].into_iter().collect();
        let true_instance = crate::ematching::subst_vars_exact_qf(
            &mut true_executor.ctx.terms,
            body,
            &substitution,
        )
        .expect("fixture has an exact raw instance");
        assert_eq!(
            true_executor.evaluate_term(&crate::executor::model::Model::empty(), true_instance,),
            crate::executor::model::EvalValue::Bool(true)
        );
        assert!(true_executor
            .try_authorize_current_query_exact_closed_forall_unsat(true_forall, &[one])
            .is_none());

        let mut unknown_executor = load_exact_closed_forall(EXACT_CLOSED_FORALL_UNSAT_SCRIPT);
        let unknown_forall = bind_exact_closed_forall_query(&mut unknown_executor);
        let zero = unknown_executor.ctx.terms.mk_int(0.into());
        let (_, unknown_body) =
            crate::executor::quantifier_loop::closed_quantifier_free_forall_literal_parts(
                &unknown_executor.ctx.terms,
                unknown_forall,
            )
            .expect("fixture is in the exact literal fragment");
        let substitution: HashMap<String, TermId> = [("y".to_string(), zero)].into_iter().collect();
        let unknown_instance = crate::ematching::subst_vars_exact_qf(
            &mut unknown_executor.ctx.terms,
            unknown_body,
            &substitution,
        )
        .expect("fixture has an exact raw instance");
        assert_eq!(
            unknown_executor
                .evaluate_term(&crate::executor::model::Model::empty(), unknown_instance,),
            crate::executor::model::EvalValue::Unknown
        );
        assert!(unknown_executor
            .try_authorize_current_query_exact_closed_forall_unsat(unknown_forall, &[zero])
            .is_none());
    }

    #[test]
    fn exact_closed_forall_rejects_contextual_evaluator_override() {
        let mut executor =
            load_exact_closed_forall("(set-logic LIA) (assert (forall ((y Int)) (= y y)))");
        let forall_id = bind_exact_closed_forall_query(&mut executor);
        let one = executor.ctx.terms.mk_int(1.into());
        let (_, body) =
            crate::executor::quantifier_loop::closed_quantifier_free_forall_literal_parts(
                &executor.ctx.terms,
                forall_id,
            )
            .expect("fixture is in the exact literal fragment");
        let substitution: HashMap<String, TermId> = [("y".to_string(), one)].into_iter().collect();
        let true_instance =
            crate::ematching::subst_vars_exact_qf(&mut executor.ctx.terms, body, &substitution)
                .expect("fixture has an exact raw instance");
        assert!(matches!(
            executor.evaluate_term(&crate::executor::model::Model::empty(), true_instance),
            crate::executor::model::EvalValue::Bool(true)
        ));

        let forged = crate::executor::model::with_scoped_term_evaluation_override_for_test(
            true_instance,
            crate::executor::model::EvalValue::Bool(false),
            || executor.try_authorize_current_query_exact_closed_forall_unsat(forall_id, &[one]),
        );
        assert!(forged.is_none());
    }

    #[test]
    fn exact_closed_forall_ignores_and_preserves_ambient_eval_memo() {
        let mut executor =
            load_exact_closed_forall("(set-logic LIA) (assert (forall ((y Int)) (= y y)))");
        let forall_id = bind_exact_closed_forall_query(&mut executor);
        let one = executor.ctx.terms.mk_int(1.into());
        let (_, body) =
            crate::executor::quantifier_loop::closed_quantifier_free_forall_literal_parts(
                &executor.ctx.terms,
                forall_id,
            )
            .expect("fixture is in the exact literal fragment");
        let substitution: HashMap<String, TermId> = [("y".to_string(), one)].into_iter().collect();
        let true_instance =
            crate::ematching::subst_vars_exact_qf(&mut executor.ctx.terms, body, &substitution)
                .expect("fixture has an exact raw instance");

        let _ambient = crate::executor::model::EvalMemoSession::new();
        crate::executor::model::seed_eval_memo_for_test(
            true_instance,
            crate::executor::model::EvalValue::Bool(false),
        );
        assert!(
            executor
                .try_authorize_current_query_exact_closed_forall_unsat(forall_id, &[one])
                .is_none(),
            "an ambient memo entry from another model cannot forge the exact theorem"
        );
        assert!(
            matches!(
                executor.evaluate_term(&crate::executor::model::Model::empty(), true_instance),
                crate::executor::model::EvalValue::Bool(false)
            ),
            "the isolated check must restore the outer memo verbatim"
        );
    }

    #[test]
    fn isolated_eval_memo_restores_ambient_session_after_panic() {
        let mut executor =
            load_exact_closed_forall("(set-logic LIA) (assert (forall ((y Int)) (= y y)))");
        let forall_id = bind_exact_closed_forall_query(&mut executor);
        let one = executor.ctx.terms.mk_int(1.into());
        let (_, body) =
            crate::executor::quantifier_loop::closed_quantifier_free_forall_literal_parts(
                &executor.ctx.terms,
                forall_id,
            )
            .expect("fixture is in the exact literal fragment");
        let substitution: HashMap<String, TermId> = [("y".to_string(), one)].into_iter().collect();
        let true_instance =
            crate::ematching::subst_vars_exact_qf(&mut executor.ctx.terms, body, &substitution)
                .expect("fixture has an exact raw instance");

        let _ambient = crate::executor::model::EvalMemoSession::new();
        crate::executor::model::seed_eval_memo_for_test(
            true_instance,
            crate::executor::model::EvalValue::Bool(false),
        );
        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            crate::executor::model::with_isolated_eval_memo(|| {
                crate::executor::model::seed_eval_memo_for_test(
                    true_instance,
                    crate::executor::model::EvalValue::Bool(true),
                );
                panic!("exercise isolated memo unwind restoration");
            });
        }));
        assert!(unwind.is_err());
        assert!(
            matches!(
                executor.evaluate_term(&crate::executor::model::Model::empty(), true_instance),
                crate::executor::model::EvalValue::Bool(false)
            ),
            "unwinding must restore both the ambient session and its exact entries"
        );
    }

    #[test]
    fn exact_closed_forall_rejects_post_mint_term_slot_reuse() {
        let mut executor = load_exact_closed_forall(EXACT_CLOSED_FORALL_UNSAT_SCRIPT);
        let forall_id = bind_exact_closed_forall_query(&mut executor);
        let checkpoint = executor.ctx.terms.rollback_checkpoint();
        let three = executor.ctx.terms.mk_int(3.into());
        let evidence = executor
            .try_authorize_current_query_exact_closed_forall_unsat(forall_id, &[three])
            .expect("false literal instance must authenticate before rollback");

        executor.ctx.terms.rollback_to(checkpoint);
        let replacement = executor.ctx.terms.mk_int(137.into());
        assert_eq!(
            replacement, three,
            "the canary must reuse the witness literal's numeric slot"
        );
        assert!(executor
            .emit_checked_exact_closed_forall_unsat(evidence)
            .is_unknown());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn exact_closed_forall_self_check_still_requires_translated_proof() {
        let mut executor = load_exact_closed_forall(EXACT_CLOSED_FORALL_UNSAT_SCRIPT);
        let forall_id = bind_exact_closed_forall_query(&mut executor);
        let three = executor.ctx.terms.mk_int(3.into());
        let evidence = executor
            .try_authorize_current_query_exact_closed_forall_unsat(forall_id, &[three])
            .expect("false literal instance must authenticate");
        executor.set_self_check(true);

        assert!(executor
            .emit_checked_exact_closed_forall_unsat(evidence)
            .is_unknown());
        assert_eq!(
            executor.unknown_reason(),
            Some(UnknownReason::SelfCheckRejected)
        );
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn exact_forall_uf_ground_token_is_one_shot_and_snapshot_bound() {
        let mut executor = load_exact_closed_forall(EXACT_FORALL_UF_GROUND_UNSAT_SCRIPT);
        let evidence = exact_forall_uf_ground_evidence(&mut executor);
        assert_eq!(evidence.contradiction.point, BigInt::from(3));
        assert_eq!(evidence.contradiction.lower_bound, BigInt::from(0));
        assert_eq!(evidence.contradiction.pinned_value, BigInt::from(-1));

        let proposed = executor.emit_checked_exact_forall_uf_ground_unsat(evidence);
        assert!(proposed.is_unsat());
        assert!(executor
            .certify_unsat_for_publication(proposed, &[])
            .is_unsat());
        let certificate = executor
            .take_unsat_certificate()
            .expect("exact authored-forall instance token must cross publication once");
        assert!(matches!(
            certificate.0,
            UnsatCertificateKind::CheckedExactForallUfGround(_)
        ));
        assert!(executor.take_unsat_certificate().is_none());

        let mut appended = load_exact_closed_forall(EXACT_FORALL_UF_GROUND_UNSAT_SCRIPT);
        let stale = exact_forall_uf_ground_evidence(&mut appended);
        let _new_term = appended
            .ctx
            .terms
            .mk_fresh_var("post_forall_instance_certificate_append", CoreSort::Int);
        assert!(appended
            .emit_checked_exact_forall_uf_ground_unsat(stale)
            .is_unknown());
        assert!(appended.take_unsat_certificate().is_none());
    }

    #[test]
    fn exact_forall_uf_ground_token_rejects_stale_query_source_roots_and_term_reuse() {
        let mut query = load_exact_closed_forall(EXACT_FORALL_UF_GROUND_UNSAT_SCRIPT);
        let query_evidence = exact_forall_uf_ground_evidence(&mut query);
        query.begin_public_solve(false);
        query.bind_unsat_query_assumptions(&[]);
        assert!(query
            .emit_checked_exact_forall_uf_ground_unsat(query_evidence)
            .is_unknown());

        let mut source = load_exact_closed_forall(EXACT_FORALL_UF_GROUND_UNSAT_SCRIPT);
        let source_evidence = exact_forall_uf_ground_evidence(&mut source);
        let declaration = ay_frontend::parse("(declare-const later Int)")
            .expect("source-staleness declaration must parse");
        source
            .execute_all(&declaration)
            .expect("source-staleness declaration must execute");
        assert!(source
            .emit_checked_exact_forall_uf_ground_unsat(source_evidence)
            .is_unknown());

        let mut roots = load_exact_closed_forall(EXACT_FORALL_UF_GROUND_UNSAT_SCRIPT);
        let root_evidence = exact_forall_uf_ground_evidence(&mut roots);
        roots.ctx.assertions.swap(0, 1);
        assert!(roots
            .emit_checked_exact_forall_uf_ground_unsat(root_evidence)
            .is_unknown());

        let mut reused = load_exact_closed_forall(
            "(set-logic UFLIA) (declare-fun f (Int) Int) \
             (assert (forall ((x Int)) (>= (f (+ x 1)) 0))) \
             (assert (= (f 1000000007) (- 1)))",
        );
        reused.begin_public_solve(false);
        reused.bind_unsat_query_assumptions(&[]);
        let checkpoint = reused.ctx.terms.rollback_checkpoint();
        let reuse_evidence = reused
            .try_authorize_current_query_exact_forall_uf_ground_unsat()
            .expect("fixture must authenticate before rollback");
        let witness = reuse_evidence.witness;
        reused.ctx.terms.rollback_to(checkpoint);
        let replacement = reused.ctx.terms.mk_int(137.into());
        assert_eq!(
            replacement, witness,
            "the canary must reuse the witness literal's numeric slot"
        );
        assert!(reused
            .emit_checked_exact_forall_uf_ground_unsat(reuse_evidence)
            .is_unknown());
        assert!(reused.take_unsat_certificate().is_none());
    }

    #[test]
    fn exact_forall_uf_ground_declines_assumptions_and_proof_modes() {
        let mut assumed = load_exact_closed_forall(EXACT_FORALL_UF_GROUND_UNSAT_SCRIPT);
        assumed.begin_public_solve(false);
        let assumption = assumed.ctx.assertions[1];
        assumed.bind_unsat_query_assumptions(&[assumption]);
        assert!(assumed
            .try_authorize_current_query_exact_forall_uf_ground_unsat()
            .is_none());

        let mut proof = load_exact_closed_forall(EXACT_FORALL_UF_GROUND_UNSAT_SCRIPT);
        proof.set_produce_proofs(true);
        proof.begin_public_solve(false);
        proof.bind_unsat_query_assumptions(&[]);
        assert!(proof
            .try_authorize_current_query_exact_forall_uf_ground_unsat()
            .is_none());

        let mut self_check = load_exact_closed_forall(EXACT_FORALL_UF_GROUND_UNSAT_SCRIPT);
        let evidence = exact_forall_uf_ground_evidence(&mut self_check);
        self_check.set_self_check(true);
        assert!(self_check
            .emit_checked_exact_forall_uf_ground_unsat(evidence)
            .is_unknown());
        assert_eq!(
            self_check.unknown_reason(),
            Some(UnknownReason::SelfCheckRejected)
        );
        assert!(self_check.take_unsat_certificate().is_none());

        let mut stopped = load_exact_closed_forall(EXACT_FORALL_UF_GROUND_UNSAT_SCRIPT);
        stopped.begin_public_solve(false);
        stopped.bind_unsat_query_assumptions(&[]);
        stopped.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
        assert!(stopped
            .try_authorize_current_query_exact_forall_uf_ground_unsat()
            .is_none());
    }

    #[test]
    fn exact_forall_uf_ground_declines_nearby_non_theorems() {
        for source in [
            // The pin satisfies the universal lower bound.
            "(set-logic UFLIA) (declare-fun f (Int) Int) \
             (assert (forall ((x Int)) (>= (f (+ x 1)) 0))) \
             (assert (= (f 3) 5))",
            // `2*x` is not surjective over Int; the negative odd point is not
            // constrained by the universal.
            "(set-logic UFLIA) (declare-fun f (Int) Int) \
             (assert (forall ((x Int)) (>= (f (* 2 x)) 0))) \
             (assert (= (f 3) (- 1)))",
            // A pin for another declaration does not contradict the forall.
            "(set-logic UFLIA) (declare-fun f (Int) Int) \
             (declare-fun g (Int) Int) \
             (assert (forall ((x Int)) (>= (f (+ x 1)) 0))) \
             (assert (= (g 3) (- 1)))",
            // Symbolic pin points are outside literal witness normalization.
            "(set-logic UFLIA) (declare-fun f (Int) Int) (declare-const c Int) \
             (assert (forall ((x Int)) (>= (f (+ x 1)) 0))) \
             (assert (= (f c) (- 1)))",
            // A definition is not an ordinary free-UF declaration.
            "(set-logic UFLIA) (define-fun f ((x Int)) Int x) \
             (assert (forall ((x Int)) (>= (f (+ x 1)) 0))) \
             (assert (= (f 3) (- 1)))",
        ] {
            let mut executor = load_exact_closed_forall(source);
            executor.begin_public_solve(false);
            executor.bind_unsat_query_assumptions(&[]);
            assert!(
                executor
                    .try_authorize_current_query_exact_forall_uf_ground_unsat()
                    .is_none(),
                "nearby unsupported or satisfiable shape acquired UNSAT authority: {source}"
            );
        }
    }

    #[test]
    fn exact_finite_expansion_token_is_one_shot_and_snapshot_bound() {
        let mut executor = load_exact_finite_expansion(EXACT_FINITE_EXPANSION_UNSAT_SCRIPT);
        let evidence = exact_finite_expansion_evidence(&mut executor);
        let proposed = executor.emit_checked_exact_finite_expansion_unsat(evidence);
        assert!(proposed.is_unsat());
        assert!(executor
            .certify_unsat_for_publication(proposed, &[])
            .is_unsat());
        let certificate = executor
            .take_unsat_certificate()
            .expect("exact finite-expansion token must cross publication once");
        assert!(matches!(
            certificate.0,
            UnsatCertificateKind::CheckedExactFiniteExpansion(_)
        ));
        assert!(executor.take_unsat_certificate().is_none());

        let mut appended = load_exact_finite_expansion(EXACT_FINITE_EXPANSION_UNSAT_SCRIPT);
        let stale = exact_finite_expansion_evidence(&mut appended);
        let _new_term = appended
            .ctx
            .terms
            .mk_fresh_var("post_certificate_append", CoreSort::Int);
        assert!(appended
            .emit_checked_exact_finite_expansion_unsat(stale)
            .is_unknown());
        assert!(appended.take_unsat_certificate().is_none());
    }

    #[test]
    fn exact_finite_expansion_token_rejects_stale_query_source_and_root_order() {
        let mut query = load_exact_finite_expansion(EXACT_FINITE_EXPANSION_UNSAT_SCRIPT);
        let query_evidence = exact_finite_expansion_evidence(&mut query);
        query.begin_public_solve(false);
        query.bind_unsat_query_assumptions(&[]);
        assert!(query
            .emit_checked_exact_finite_expansion_unsat(query_evidence)
            .is_unknown());

        let mut source = load_exact_finite_expansion(EXACT_FINITE_EXPANSION_UNSAT_SCRIPT);
        let source_evidence = exact_finite_expansion_evidence(&mut source);
        let declaration = ay_frontend::parse("(declare-const later Int)")
            .expect("source-staleness declaration must parse");
        source
            .execute_all(&declaration)
            .expect("source-staleness declaration must execute");
        assert!(source
            .emit_checked_exact_finite_expansion_unsat(source_evidence)
            .is_unknown());

        let mut roots = load_exact_finite_expansion(EXACT_FINITE_EXPANSION_UNSAT_SCRIPT);
        let root_evidence = exact_finite_expansion_evidence(&mut roots);
        roots.ctx.assertions.swap(1, 2);
        assert!(roots
            .emit_checked_exact_finite_expansion_unsat(root_evidence)
            .is_unknown());
    }

    #[test]
    fn exact_finite_expansion_declines_assumptions_and_incomplete_root_classes() {
        let mut assumed = load_exact_finite_expansion(EXACT_FINITE_EXPANSION_UNSAT_SCRIPT);
        assumed.begin_public_solve(false);
        let assumption = assumed.ctx.terms.mk_fresh_var("assumed", CoreSort::Bool);
        assumed.bind_unsat_query_assumptions(&[assumption]);
        assert!(assumed
            .try_authorize_current_query_exact_finite_expansion_unsat()
            .is_none());

        let mut satisfiable = load_exact_finite_expansion(
            "(set-logic BV) \
             (assert (forall ((x (_ BitVec 8))) \
               (or (bvult #x00 x) (= x #x00))))",
        );
        bind_empty_exact_finite_expansion_query(&mut satisfiable);
        assert!(satisfiable
            .try_authorize_current_query_exact_finite_expansion_unsat()
            .is_none());

        let mut mixed = load_exact_finite_expansion(&format!(
            "{EXACT_FINITE_EXPANSION_UNSAT_SCRIPT} \
             (assert (forall ((i Int)) (= i i)))"
        ));
        bind_empty_exact_finite_expansion_query(&mut mixed);
        assert!(mixed
            .try_authorize_current_query_exact_finite_expansion_unsat()
            .is_none());
    }

    #[test]
    fn exact_finite_expansion_rejects_forged_canonical_operator_owners() {
        for identity in ["=", "and", "bvult"] {
            let mut executor = load_exact_finite_expansion(EXACT_FINITE_EXPANSION_UNSAT_SCRIPT);
            let owner = executor
                .ctx
                .terms
                .mk_fresh_var(&format!("forged_{identity}_owner"), CoreSort::Bool);
            executor
                .ctx
                .register_symbol(identity.to_string(), owner, CoreSort::Bool);
            bind_empty_exact_finite_expansion_query(&mut executor);
            assert!(
                executor
                    .try_authorize_current_query_exact_finite_expansion_unsat()
                    .is_none(),
                "canonical `{identity}` must not receive builtin authority while declaration-owned"
            );
        }

        let mut scalar = load_exact_finite_expansion(
            "(set-logic ALL) \
             (declare-const c (_ BitVec 8)) \
             (assert (forall ((x (_ BitVec 8))) (= x x))) \
             (assert (= (+ (ubv_to_int c) 1) 2)) \
             (assert (= (+ (ubv_to_int c) 1) 3))",
        );
        let owner = scalar
            .ctx
            .terms
            .mk_fresh_var("forged_plus_owner", CoreSort::Int);
        scalar
            .ctx
            .register_symbol("+".to_string(), owner, CoreSort::Int);
        bind_empty_exact_finite_expansion_query(&mut scalar);
        assert!(scalar
            .try_authorize_current_query_exact_finite_expansion_unsat()
            .is_none());
    }

    #[test]
    fn exact_finite_expansion_rejects_duplicate_or_ill_sorted_binders_and_roots() {
        let mut duplicate = load_exact_finite_expansion(EXACT_FINITE_EXPANSION_UNSAT_SCRIPT);
        let TermData::Forall(vars, body, triggers) =
            duplicate.ctx.terms.get(duplicate.ctx.assertions[0]).clone()
        else {
            panic!("fixture starts with one finite forall");
        };
        let binder_sort = vars[0].1.clone();
        let malformed = duplicate.ctx.terms.mk_forall_with_triggers(
            vec![
                ("x".to_string(), binder_sort.clone()),
                ("x".to_string(), binder_sort),
            ],
            body,
            triggers,
        );
        duplicate.ctx.assertions[0] = malformed;
        bind_empty_exact_finite_expansion_query(&mut duplicate);
        assert!(duplicate
            .try_authorize_current_query_exact_finite_expansion_unsat()
            .is_none());

        let mut occurrence = load_exact_finite_expansion(EXACT_FINITE_EXPANSION_UNSAT_SCRIPT);
        let wrong_x = occurrence.ctx.terms.mk_var("x", CoreSort::Int);
        let zero = occurrence.ctx.terms.mk_int(0.into());
        let malformed_body = occurrence.ctx.terms.mk_eq(wrong_x, zero);
        let malformed = occurrence.ctx.terms.mk_forall(
            vec![(
                "x".to_string(),
                CoreSort::BitVec(ay_core::BitVecSort::new(8)),
            )],
            malformed_body,
        );
        occurrence.ctx.assertions[0] = malformed;
        bind_empty_exact_finite_expansion_query(&mut occurrence);
        assert!(occurrence
            .try_authorize_current_query_exact_finite_expansion_unsat()
            .is_none());

        let mut root_sort = load_exact_finite_expansion(EXACT_FINITE_EXPANSION_UNSAT_SCRIPT);
        let one = root_sort.ctx.terms.mk_int(1.into());
        root_sort.ctx.assertions.push(one);
        bind_empty_exact_finite_expansion_query(&mut root_sort);
        assert!(root_sort
            .try_authorize_current_query_exact_finite_expansion_unsat()
            .is_none());
    }

    #[test]
    fn exact_finite_expansion_explicit_proof_modes_decline() {
        let mut proof = load_exact_finite_expansion(EXACT_FINITE_EXPANSION_UNSAT_SCRIPT);
        proof.set_produce_proofs(true);
        bind_empty_exact_finite_expansion_query(&mut proof);
        assert!(proof
            .try_authorize_current_query_exact_finite_expansion_unsat()
            .is_none());

        let mut self_check = load_exact_finite_expansion(EXACT_FINITE_EXPANSION_UNSAT_SCRIPT);
        self_check.set_self_check(true);
        bind_empty_exact_finite_expansion_query(&mut self_check);
        assert!(self_check
            .try_authorize_current_query_exact_finite_expansion_unsat()
            .is_none());
    }

    #[test]
    fn exact_semantic_unsat_script_proof_requests_fail_closed() {
        for source in [EXACT_EXISTS_UNSAT_SCRIPT, EXACT_FORALL_EXISTS_UNSAT_SCRIPT] {
            let commands = ay_frontend::parse(&format!(
                "(set-option :produce-proofs true) {source} (check-sat) (get-proof)"
            ))
            .expect("proof-requesting exact semantic fixture must parse");
            let mut executor = Executor::new();
            let outputs = execute_authored_script(&mut executor, &commands);

            assert_eq!(outputs[0], "unknown");
            assert_eq!(
                outputs[1],
                "(error \"proof is not available, last result was unknown\")"
            );
            assert_eq!(
                executor.unknown_reason(),
                Some(UnknownReason::SelfCheckRejected)
            );
            assert!(executor.last_proof.is_none());
            assert!(executor.take_unsat_certificate().is_none());
        }

        // The authored forall/UF checker declines before constructing its
        // semantic token when proofs are requested. The ordinary quantified
        // pipeline may therefore supply its own precise incompleteness reason;
        // the end-to-end contract is the fail-closed verdict and the absence
        // of any proof or UNSAT certificate, not reuse of the older exact-
        // exists route's SelfCheckRejected diagnostic.
        let commands = ay_frontend::parse(&format!(
            "(set-option :produce-proofs true) {} (check-sat) (get-proof)",
            EXACT_FORALL_UF_GROUND_UNSAT_SCRIPT
        ))
        .expect("proof-requesting exact forall/UF fixture must parse");
        let mut executor = Executor::new();
        let outputs = execute_authored_script(&mut executor, &commands);

        assert_eq!(outputs[0], "unknown");
        assert_eq!(
            outputs[1],
            "(error \"proof is not available, last result was unknown\")"
        );
        assert!(executor.unknown_reason().is_some());
        assert!(executor.last_proof.is_none());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn exact_semantic_unsat_explicit_api_proof_request_fails_closed() {
        let commands = ay_frontend::parse(&format!(
            "{} (check-sat) (get-proof)",
            EXACT_FORALL_EXISTS_UNSAT_SCRIPT
        ))
        .expect("exact semantic API fixture must parse");
        let mut executor = Executor::new();
        executor.set_produce_proofs(true);

        let outputs = execute_authored_script(&mut executor, &commands);

        assert_eq!(outputs[0], "unknown");
        assert_eq!(
            outputs[1],
            "(error \"proof is not available, last result was unknown\")"
        );
        assert!(executor.last_proof.is_none());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn exact_semantic_unsat_self_check_requires_a_translated_proof() {
        let commands =
            ay_frontend::parse(&format!("{} (check-sat)", EXACT_FORALL_EXISTS_UNSAT_SCRIPT))
                .expect("exact semantic self-check fixture must parse");
        let mut executor = Executor::new();
        executor.set_self_check(true);

        let outputs = execute_authored_script(&mut executor, &commands);

        assert_eq!(outputs, vec!["unknown"]);
        assert_eq!(
            executor.unknown_reason(),
            Some(UnknownReason::SelfCheckRejected)
        );
        assert!(executor.last_proof.is_none());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn exact_semantic_unsat_proof_checked_api_requires_a_translated_proof() {
        let commands = ay_frontend::parse(&format!("{} (check-sat)", EXACT_EXISTS_UNSAT_SCRIPT))
            .expect("exact semantic proof-checked fixture must parse");
        let mut executor = Executor::new();
        executor.set_verification_level(crate::VerificationLevel::ProofChecked);

        let outputs = execute_authored_script(&mut executor, &commands);

        assert_eq!(outputs, vec!["unknown"]);
        assert_eq!(
            executor.unknown_reason(),
            Some(UnknownReason::SelfCheckRejected)
        );
        assert!(executor.last_proof.is_none());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn exact_semantic_unsat_strict_script_mode_requires_a_translated_proof() {
        let commands = ay_frontend::parse(&format!(
            "(set-option :check-proofs-strict true) {} (check-sat)",
            EXACT_FORALL_EXISTS_UNSAT_SCRIPT
        ))
        .expect("exact semantic strict-proof fixture must parse");
        let mut executor = Executor::new();

        let outputs = execute_authored_script(&mut executor, &commands);

        assert_eq!(outputs, vec!["unknown"]);
        assert_eq!(
            executor.unknown_reason(),
            Some(UnknownReason::SelfCheckRejected)
        );
        assert!(executor.last_proof.is_none());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn exact_semantic_unsat_best_effort_default_is_not_a_proof_requirement() {
        let commands =
            ay_frontend::parse(&format!("{} (check-sat)", EXACT_FORALL_EXISTS_UNSAT_SCRIPT))
                .expect("exact semantic best-effort fixture must parse");
        let mut executor = Executor::new();
        executor.set_best_effort_produce_proofs(100);

        let outputs = execute_authored_script(&mut executor, &commands);

        assert_eq!(outputs, vec!["unsat"]);
        assert_eq!(
            executor.last_command_unsat_admission,
            Some(CommandUnsatAdmission::CheckedExactForallExists)
        );
        assert!(executor.last_unsat_proof_reconstruction_suppressed);
        assert!(executor.last_proof.is_none());
    }

    #[test]
    fn changed_bound_assumptions_revoke_prechecked_exact_forall_exists_unsat() {
        let (mut executor, proposed) = prechecked_exact_forall_exists_unsat();
        let forged_assumption = executor.ctx.assertions[0];
        executor
            .unsat_query_epoch
            .as_mut()
            .expect("active query epoch")
            .assumptions = Some(vec![forged_assumption]);

        let published = executor.certify_unsat_for_publication(proposed, &[]);
        assert!(published.is_unknown());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn changed_declared_extension_revokes_consumable_exact_forall_exists_token() {
        let (mut executor, proposed) = prechecked_exact_forall_exists_unsat();
        assert!(executor
            .certify_unsat_for_publication(proposed, &[])
            .is_unsat());
        let forged_extension = executor.ctx.assertions[0];
        executor
            .unsat_query_epoch
            .as_mut()
            .expect("active query epoch")
            .declared_extension
            .push(forged_extension);

        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn missing_proof_cannot_admit_a_forged_sat_query() {
        let mut executor = Executor::new();
        let _satisfiable_root = satisfiable_boolean_assertion(&mut executor);
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);

        let result = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(result.is_unknown());
        assert!(executor.take_unsat_certificate().is_none());
        assert_eq!(
            executor.unknown_reason(),
            Some(UnknownReason::SelfCheckRejected)
        );
    }

    #[test]
    fn invalid_empty_proof_fails_closed() {
        let mut executor = Executor::new();
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        executor.last_proof = Some(Proof::new());

        let result = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(result.is_unknown());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn checked_sat_refutation_survives_missing_alethe_presentation() {
        let (mut executor, proposed) = independently_checked_boolean_contradiction();
        executor.last_proof = None;

        let published = executor.certify_unsat_for_publication(proposed, &[]);

        assert!(published.is_unsat());
        assert!(matches!(
            executor
                .last_unsat_certificate
                .as_ref()
                .map(|token| &token.0),
            Some(UnsatCertificateKind::CheckedSatRefutation { .. })
        ));
    }

    #[test]
    fn checked_sat_refutation_survives_structurally_invalid_alethe_presentation() {
        let (mut executor, proposed) = independently_checked_boolean_contradiction();
        // EmptyProof is a structural checker rejection, not a trust-family
        // presentation error. The exact-query sidecar remains authoritative.
        executor.last_proof = Some(Proof::new());

        let published = executor.certify_unsat_for_publication(proposed, &[]);

        assert!(published.is_unsat());
        assert!(matches!(
            executor
                .last_unsat_certificate
                .as_ref()
                .map(|token| &token.0),
            Some(UnsatCertificateKind::CheckedSatRefutation { .. })
        ));
    }

    #[test]
    fn checked_sat_refutation_cannot_replace_an_explicitly_required_proof() {
        #[derive(Clone, Copy, Debug)]
        enum RequiredProofMode {
            Artifact,
            SelfCheck,
            ProofChecked,
        }

        for mode in [
            RequiredProofMode::Artifact,
            RequiredProofMode::SelfCheck,
            RequiredProofMode::ProofChecked,
        ] {
            let (mut executor, proposed) = independently_checked_boolean_contradiction();
            executor.last_proof = None;
            match mode {
                RequiredProofMode::Artifact => executor.set_produce_proofs(true),
                RequiredProofMode::SelfCheck => executor.set_self_check(true),
                RequiredProofMode::ProofChecked => {
                    executor.set_verification_level(crate::VerificationLevel::ProofChecked)
                }
            }

            let published = executor.certify_unsat_for_publication(proposed, &[]);

            assert!(
                published.is_unknown(),
                "{mode:?} must require the translated strict proof"
            );
            assert!(executor.take_unsat_certificate().is_none());
        }
    }

    #[test]
    fn changed_assumption_slice_cannot_reuse_epoch() {
        let mut executor = Executor::new();
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let unexpected = executor.ctx.terms.true_term();

        let result = executor.certify_unsat_for_publication(SolveResult::unsat(), &[unexpected]);
        assert!(result.is_unknown());
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn only_authenticated_named_rewrites_extend_assumption_authority() {
        let mut executor = Executor::new();
        let authored = executor.ctx.terms.mk_var("authored", ay_core::Sort::Bool);
        let rewritten = executor.ctx.terms.mk_var("rewritten", ay_core::Sort::Bool);
        let generated = executor.ctx.terms.mk_var("generated", ay_core::Sort::Bool);

        executor.named_assert_rewrites.insert(rewritten, authored);

        assert!(executor.query_authorizes_assumption(rewritten, &[authored], &[]));
        assert!(!executor.query_authorizes_assumption(generated, &[authored], &[]));
    }

    #[test]
    fn discharged_trust_certificate_is_independent_not_strict() {
        let mut executor = Executor::new();
        let proposition = executor
            .ctx
            .terms
            .mk_var("trust_discharge_p", ay_core::Sort::Bool);
        let not_proposition = executor.ctx.terms.mk_not_raw(proposition);
        executor.ctx.assertions = vec![proposition, not_proposition];
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        assert!(executor
            .check_sat()
            .expect("contradictory authored units solve")
            .is_unsat());

        // Force the trust-discharge branch rather than the checked SAT sidecar
        // branch. The terminal trust conclusion is accepted only if the
        // independent discharge re-establishes this exact authored problem.
        executor.last_checked_sat_refutation = None;
        let mut trust_proof = Proof::new();
        trust_proof.add_rule_step(
            ay_core::AletheRule::Trust,
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        executor.last_proof = Some(trust_proof);

        let result = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(result.is_unsat());
        let certificate = executor
            .take_unsat_certificate()
            .expect("independent trust discharge mints a token");
        assert!(!certificate.strict_proof_verified());
        assert!(certificate.independently_verified());
        assert!(!certificate.exact_semantic_verified());
    }

    #[test]
    fn checked_sat_refutation_certificate_rejects_post_mint_source_mutation() {
        let mut executor = Executor::new();
        let _problem = strict_boolean_contradiction(&mut executor);
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let proposed = executor
            .check_sat()
            .expect("contradictory Boolean units must solve");
        assert!(proposed.is_unsat());
        assert!(executor.last_checked_sat_refutation.is_some());

        let mut trust_proof = Proof::new();
        trust_proof.add_rule_step(
            ay_core::AletheRule::Trust,
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        executor.last_proof = Some(trust_proof);
        let published = executor.certify_unsat_for_publication(proposed, &[]);
        assert!(published.is_unsat());
        assert!(executor.last_unsat_certificate.is_some());

        // Mutate the frontend directly so the cached query epoch and the
        // already-minted token remain present. Consumption must compare them to
        // the LIVE source stamp, not merely to each other.
        executor
            .ctx
            .process_command(&ay_frontend::Command::Push(1))
            .expect("direct frontend mutation must succeed");
        assert!(executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn proof_based_unsat_certificate_rejects_term_slot_reuse() {
        let mut executor = Executor::new();
        let checkpoint = executor.ctx.terms.rollback_checkpoint();
        let proposition = executor
            .ctx
            .terms
            .mk_fresh_var("proof_scope_root", ay_core::Sort::Bool);
        let not_proposition = executor.ctx.terms.mk_not_raw(proposition);
        executor.ctx.assertions = vec![proposition, not_proposition];
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);

        let proposed = executor
            .check_sat()
            .expect("contradictory Boolean units must solve");
        assert!(proposed.is_unsat());
        let published = executor.certify_unsat_for_publication(proposed, &[]);
        assert!(published.is_unsat());
        assert!(executor.last_unsat_certificate.is_some());

        // Deliberately violate the rollback API's external-TermId contract to
        // model a speculative caller retaining a certificate across rollback.
        // Recreating the same numeric slots must not let different terms inherit
        // the old proof authority.
        executor.ctx.terms.rollback_to(checkpoint);
        let replacement = executor
            .ctx
            .terms
            .mk_fresh_var("replacement_proof_scope_root", ay_core::Sort::Bool);
        let not_replacement = executor.ctx.terms.mk_not_raw(replacement);
        assert_eq!(
            replacement, proposition,
            "the canary must reuse the root slot"
        );
        assert_eq!(
            not_replacement, not_proposition,
            "the canary must reuse the negated-root slot"
        );

        assert!(
            executor.take_unsat_certificate().is_none(),
            "a new term entry cannot inherit a proof certificate from a reused TermId"
        );
    }

    #[test]
    fn satisfiable_authored_query_cannot_be_admitted_by_trust_fallback() {
        let mut executor = Executor::new();
        let proposition = executor
            .ctx
            .terms
            .mk_var("forged_unsat_guard_p", ay_core::Sort::Bool);
        executor.ctx.assertions = vec![proposition];
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);

        // Force the trust-family path with no checked SAT-resolution sidecar.
        // The authored query is satisfiable (`p = true`), so the dominant
        // fresh-SAT guard and, defensively, every later reconfirmation path must
        // refuse to turn this forged provisional UNSAT into a certificate.
        executor.last_checked_sat_refutation = None;
        let mut trust_proof = Proof::new();
        trust_proof.add_rule_step(
            ay_core::AletheRule::Trust,
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        executor.last_proof = Some(trust_proof);

        let result = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        assert!(result.is_unknown());
        assert!(executor.take_unsat_certificate().is_none());
        assert_eq!(
            executor.unknown_reason(),
            Some(UnknownReason::SelfCheckRejected)
        );
    }
}
