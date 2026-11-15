// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent replay for exact finite-quantifier SAT authority.
//!
//! Universal expansion stays restricted to the audited full-BV and guarded
//! single-Int routes. Existential expansion has a different semantic shape:
//! the canonical expander retains the complete guarded body at every point and
//! returns `None` unless every non-finite carrier is bounded, so standalone
//! success is an exact disjunction. A direct `not (exists ...)` root is replayed
//! by expanding only its single Int child and rebuilding the same shell.
//!
//! Producer evidence must still name the byte-identical ground replacement;
//! this module is an independent authored-syntax check, not blanket trust in
//! the expansion capability.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId, TermStore};

use super::super::preprocess::definition_fold_gate::capture_free_definitions;
use crate::ematching::contains_quantifier;
use crate::executor::quantifier_loop::ExactFiniteExpansionEvidence;
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};

impl Executor {
    /// Install exact finite-expansion SAT authority after all nested probes.
    ///
    /// The early preprocessing exit can solve a genuinely quantifier-free
    /// equivalent before E-matching exists. Re-authenticate that exact
    /// transformation only after all pre-restoration nested probes have
    /// finished, validate the final retained model against the complete
    /// expanded vector, and seal the grant to that model. Installing earlier
    /// would let a later certificate probe replace the model while leaving
    /// syntactic expansion evidence behind.
    pub(super) fn install_finite_expansion_if_sat(
        &mut self,
        result: &Result<SolveResult>,
        full_ematching_coverage: bool,
        original: Option<&[TermId]>,
        expansion: Option<&ExactFiniteExpansionEvidence>,
    ) {
        let (Ok(SolveResult::Sat), true, Some(original), Some(expansion)) =
            (result, full_ematching_coverage, original, expansion)
        else {
            return;
        };
        if self.try_finite_expansion_grant(original, expansion) {
            // Canonical equivalence plus exact-model validation over every
            // expanded root and every authored ground sibling is the complete
            // validation for this route. Running the generic post-restore
            // validator would skip the authored forall, mutate/replace the
            // sealed model in fallback probes, and discard the stronger typed
            // authority.
            self.defer_model_validation = false;
            self.last_model_validated = true;
        }
    }

    /// LAST-RESORT rescue for a ground solve that returned `Sat` and was then
    /// published as `Unknown(QuantifierUnhandled)` because no route owned it.
    ///
    /// A derived-bound finite expansion (#derived-expansion-evidence) can make
    /// a problem entirely ground AFTER the early `fully_expanded` exit is
    /// behind us. Every phase then sees zero quantifiers, classifies the ground
    /// result as `Sat`, and still reports the vanished binders as unhandled, so
    /// a decided query answers `unknown`.
    ///
    /// Running here, after every other phase, is what makes this safe in both
    /// directions. It is reached ONLY from that refusal, so it can never take a
    /// problem away from a more specific certificate, and it consults the same
    /// re-authentication as the ordinary route: canonical replay of every
    /// authored quantified root, a one-to-one record match, byte-identical
    /// replacement terms, and validation of the retained model against the
    /// whole expanded vector plus every authored ground sibling. A `false`
    /// return leaves the refusal exactly as it was.
    pub(super) fn rescue_unknown_with_finite_expansion(
        &mut self,
        ground_solve_was_sat: bool,
        full_ematching_coverage: bool,
        original: Option<&[TermId]>,
        expansion: Option<&ExactFiniteExpansionEvidence>,
    ) -> bool {
        let (true, true, Some(original), Some(expansion)) = (
            ground_solve_was_sat,
            full_ematching_coverage,
            original,
            expansion,
        ) else {
            return false;
        };
        // NO precedence guard here, unlike the already-`Sat` path. That guard
        // exists so this route cannot replace a better certificate's MODEL;
        // reaching the rescue means the verdict is ALREADY the fail-closed
        // `unknown`, so whatever other authority may be resident plainly did
        // not publish, and yielding to it would only preserve the refusal.
        if !self.install_exact_finite_expansion_sat_authority(original, expansion) {
            return false;
        }
        self.defer_model_validation = false;
        self.last_model_validated = true;
        self.last_unknown_reason = None;
        true
    }

    /// Shared body: yield to any other quantified-SAT authority, then
    /// re-authenticate and seal.
    fn try_finite_expansion_grant(
        &mut self,
        original: &[TermId],
        expansion: &ExactFiniteExpansionEvidence,
    ) -> bool {
        // LAST RESORT, never a preemption. Sealing a grant also marks the
        // retained model validated, which stops a later, more specific
        // certificate from installing its own. Measured: without this guard the
        // certified `cert_default_row_key` interpretation printed `-1` where its
        // certificate says `(- 1)`.
        if self.current_quantified_sat_authority(original).is_some() {
            return false;
        }
        self.install_exact_finite_expansion_sat_authority(original, expansion)
    }
}

pub(super) fn replay(terms: &mut TermStore, root: TermId) -> Option<TermId> {
    if let TermData::Not(inner) = terms.get(root).clone() {
        return replay_negated_existential(terms, inner);
    }
    replay_quantifier(terms, root)
}

/// [`replay`] after re-applying, FROM `source` ALONE, the two equivalences the
/// producer may have used before expanding (#source-derived-replay-bound).
///
/// Both are re-established here rather than imported, so the replay stays the
/// source theorem `scoped_standalone_finite_domain_replay` exists to protect.
/// `collect_conjunctive_ground_facts` reads only positive conjunctive-position
/// ground facts of the vector it is handed, and `source` IS an authored root
/// vector, so every fact it yields is asserted by the problem itself. No
/// producer state is consulted: the PRODUCER needs an extra
/// non-conjunctive-`forall` gate precisely because it works from
/// POST-E-MATCHING assertions carrying quantifier instances, and this sees no
/// instances at all.
///
/// 1. Aggregate DEFINITIONS (#defn-fold-under-forall). An asserted `v = t` with
///    `v` an Array/Datatype-sorted variable lets `v` be replaced by `t` inside
///    the binder, equals-for-equals. The producer does this before the
///    snapshot, so the public authored root still names `v` while the recorded
///    replacement was computed from `t` -- and without the fold the selector
///    and read chains never collapse, so the expansion cannot be reproduced.
///    Only the definitions the producer may fold are folded here: none whose
///    value mentions a variable spelled like a binder of `root`, which the
///    expander would substitute as that binder (#defn-fold-binder-capture).
/// 2. Entailed CONSTANTS. A guard bound that is a destructured datatype field
///    (`outer!fld_len`) rather than a literal is readable only from that table.
///
/// Byte-identical to [`replay`] when neither applies.
pub(super) fn replay_from_source(
    terms: &mut TermStore,
    root: TermId,
    source: &[TermId],
) -> Option<TermId> {
    if let Some(expanded) = replay(terms, root) {
        return Some(expanded);
    }
    let folded = fold_source_aggregate_definitions(terms, root, source);
    if let Some(expanded) = replay(terms, folded) {
        return Some(expanded);
    }
    let consts = super::super::entailed_consts::derive_entailed_consts(terms, source);
    if consts.is_empty() {
        return None;
    }
    let _source_derived = crate::skolemize::scoped_derived_consts(consts);
    replay(terms, folded)
}

/// `root` with every aggregate definition asserted in `source` folded in
/// (step 1 of [`replay_from_source`]); `root` itself when there is none.
fn fold_source_aggregate_definitions(
    terms: &mut TermStore,
    root: TermId,
    source: &[TermId],
) -> TermId {
    let facts = super::super::entailed_consts::collect_conjunctive_ground_facts(terms, source);
    let definitions = source_aggregate_definitions(terms, &facts);
    match capture_free_definitions(terms, root, &definitions) {
        definitions if definitions.is_empty() => root,
        definitions => crate::preprocess::VariableSubstitution::from_recorded_map(definitions)
            .apply_to_term(terms, root),
    }
}

impl Executor {
    /// The UNSAT twin of [`replay_from_source`] (#source-derived-unsat-replay):
    /// expand the quantified public `root` after re-deriving, FROM `source`
    /// ALONE, the same two equivalences — the aggregate-definition fold and the
    /// entailed constants.
    ///
    /// The exact finite-expansion UNSAT theorem needs strictly less than the
    /// SAT grant. SAT must show the expansion EQUIVALENT to the root; UNSAT
    /// only that the source ENTAILS it. Both facts hold for the same reason:
    /// `source` is the authored root vector, `collect_conjunctive_ground_facts`
    /// yields only its positive conjunctive-position ground facts, so every
    /// definition folded in and every constant read as a bound is true in
    /// every model of the problem. The expander instantiates the folded root
    /// at literal binder values and drops a guard only inside the range those
    /// constants bound, so every conjunct it emits holds in every such model.
    /// An inconsistent source makes the deriver return nothing, and the query
    /// is UNSAT then anyway.
    ///
    /// `admit_folded` sees the folded root BEFORE any substitution by binder
    /// name happens, so the caller can refuse a fold that brought a free
    /// variable spelled like a binder into the body; nothing is expanded when
    /// it declines. The fold already leaves out every definition whose value
    /// spells a binder of `root` (`capture_free_definitions`), so this is
    /// defense in depth. `None` unless the expansion is completely ground.
    pub(in crate::executor) fn source_derived_finite_expansion(
        &mut self,
        root: TermId,
        source: &[TermId],
        admit_folded: impl FnOnce(&TermStore, TermId) -> bool,
    ) -> Option<TermId> {
        let folded = fold_source_aggregate_definitions(&mut self.ctx.terms, root, source);
        if !admit_folded(&self.ctx.terms, folded) {
            return None;
        }
        let consts = super::super::entailed_consts::derive_entailed_consts(&self.ctx.terms, source);
        let _source_derived = crate::skolemize::scoped_derived_consts(consts);
        let (expanded, _) =
            crate::skolemize::finite_domain_expand_with_instances(&mut self.ctx.terms, folded)?;
        (!contains_quantifier(&self.ctx.terms, expanded)).then_some(expanded)
    }
}

/// Asserted `v = <term>` definitions with `v` an atomic `Var` of Array or
/// Datatype sort, drawn from conjunctive-position ground facts only.
///
/// Same discipline as the producer's `collect_ground_aggregate_definitions`:
/// `var = var` is skipped (orientation ambiguity), a value mentioning any
/// collected key is dropped (occurs check and no-chain rule in one test, so the
/// single pass terminates), and the first mapping per variable wins over a
/// `Vec` of candidates so the map is order-deterministic.
fn source_aggregate_definitions(terms: &TermStore, facts: &[TermId]) -> HashMap<TermId, TermId> {
    let mut candidates: Vec<(TermId, TermId)> = Vec::new();
    let mut keys: HashSet<TermId> = HashSet::default();
    for &fact in facts {
        let TermData::App(Symbol::Named(name), args) = terms.get(fact) else {
            continue;
        };
        if name != "=" || args.len() != 2 {
            continue;
        }
        let (x, y) = (args[0], args[1]);
        if !matches!(terms.sort(x), Sort::Array(_) | Sort::Datatype(_)) {
            continue;
        }
        let x_is_var = matches!(terms.get(x), TermData::Var(..));
        let y_is_var = matches!(terms.get(y), TermData::Var(..));
        let candidate = if x_is_var && !y_is_var {
            Some((x, y))
        } else if y_is_var && !x_is_var {
            Some((y, x))
        } else {
            None
        };
        let Some((v, e)) = candidate else {
            continue;
        };
        if contains_quantifier(terms, e) {
            continue;
        }
        keys.insert(v);
        candidates.push((v, e));
    }
    let mut definitions: HashMap<TermId, TermId> = HashMap::default();
    for (v, e) in candidates {
        if definitions.contains_key(&v) {
            continue;
        }
        if !mentions_any(terms, e, &keys) {
            definitions.insert(v, e);
        }
    }
    definitions
}

/// Whether `term` mentions any variable in `targets`, anywhere.
fn mentions_any(terms: &TermStore, term: TermId, targets: &HashSet<TermId>) -> bool {
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if targets.contains(&t) {
            return true;
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, th, el) => {
                stack.push(*c);
                stack.push(*th);
                stack.push(*el);
            }
            TermData::Let(bindings, body) => {
                stack.push(*body);
                for (_, value) in bindings {
                    stack.push(*value);
                }
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            _ => {}
        }
    }
    false
}

fn replay_negated_existential(terms: &mut TermStore, inner: TermId) -> Option<TermId> {
    let TermData::Exists(vars, body, _) = terms.get(inner).clone() else {
        return None;
    };
    if vars.len() != 1 || vars[0].1 != Sort::Int || contains_quantifier(terms, body) {
        return None;
    }
    let expanded = replay_quantifier(terms, inner)?;
    Some(terms.mk_not(expanded))
}

fn replay_quantifier(terms: &mut TermStore, root: TermId) -> Option<TermId> {
    let (vars, body, is_forall) = match terms.get(root).clone() {
        TermData::Forall(vars, body, _) => (vars, body, true),
        TermData::Exists(vars, body, _) => (vars, body, false),
        _ => return None,
    };
    if vars.is_empty() || contains_quantifier(terms, body) {
        return None;
    }
    if is_forall {
        let all_bv = vars.iter().all(|(_, sort)| matches!(sort, Sort::BitVec(_)));
        let guarded_single_int = vars.len() == 1 && vars[0].1 == Sort::Int;
        if !all_bv && !guarded_single_int {
            return None;
        }
    }
    let (expanded, _) = crate::skolemize::finite_domain_expand_with_instances(terms, root)?;
    if contains_quantifier(terms, expanded) {
        return None;
    }
    let (normalized, provenance) =
        crate::skolemize::skolemize_deep_with_provenance(terms, expanded, true);
    provenance
        .is_empty()
        .then_some(normalized.unwrap_or(expanded))
}

#[cfg(test)]
mod binder_capture_tests;

#[cfg(test)]
mod tests {
    use ay_core::term::Symbol;
    use num_bigint::BigInt;

    use super::*;

    fn bounded_exists(terms: &mut TermStore, vars: Vec<(String, Sort)>) -> TermId {
        let x = terms.mk_var(&vars[0].0, vars[0].1.clone());
        let zero = terms.mk_int(BigInt::from(0));
        let three = terms.mk_int(BigInt::from(3));
        let lower = terms.mk_le(zero, x);
        let upper = terms.mk_le(x, three);
        let predicate = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
        let body = terms.mk_and(vec![lower, upper, predicate]);
        terms.mk_exists(vars, body)
    }

    #[test]
    fn negated_single_int_exists_replays_byte_identically() {
        let mut terms = TermStore::new();
        let exists = bounded_exists(&mut terms, vec![("x".to_string(), Sort::Int)]);
        let root = terms.mk_not(exists);
        let canonical = replay(&mut terms, root).expect("narrow negated root must replay");
        let producer = crate::skolemize::expand_finite_domain_subterms(&mut terms, root);

        assert_eq!(canonical, producer);
        assert!(!contains_quantifier(&terms, canonical));
    }

    #[test]
    fn negated_exists_shell_declines_wrong_sort_multiple_binders_and_nesting() {
        let mut terms = TermStore::new();
        let bool_name = "b".to_string();
        let b = terms.mk_var(&bool_name, Sort::Bool);
        let bool_exists = terms.mk_exists(vec![(bool_name, Sort::Bool)], b);
        let bool_root = terms.mk_not(bool_exists);
        assert!(replay(&mut terms, bool_root).is_none());

        let two_vars = vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)];
        let multi_exists = bounded_exists(&mut terms, two_vars);
        let multi_root = terms.mk_not(multi_exists);
        assert!(replay(&mut terms, multi_root).is_none());

        let inner_name = "i".to_string();
        let inner_var = terms.mk_var(&inner_name, Sort::Int);
        let inner_body = terms.mk_eq(inner_var, inner_var);
        let inner = terms.mk_forall(vec![(inner_name, Sort::Int)], inner_body);
        let outer = terms.mk_exists(vec![("x".to_string(), Sort::Int)], inner);
        let nested_root = terms.mk_not(outer);
        assert!(replay(&mut terms, nested_root).is_none());
    }
}
