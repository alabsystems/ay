// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode schema validation for the collection SUBSET `TheoryLemmaKind`s.
//!
//! Two kinds live here, both universally valid and both re-derived from the
//! clause alone:
//!
//! * [`TheoryLemmaKind::SubsetReflexive`] — `(cl (X.subset a a))`.
//! * [`TheoryLemmaKind::SubsetElementInstance`] — the subset DEFINITION
//!   instantiated at one element term.
//!
//! WHY THESE ARE TAUTOLOGIES, AND WHY THE NAME IS TRUSTWORTHY. `set.subset`,
//! `map.subset` and `multiset.subset` are AY-extension predicates. They are
//! *declaration-activated*: `ay-frontend`'s `EXCLUDED_DECLARABLE_OP_NAMES`
//! keeps them user-declarable, but `declaration_activated_signature_ok` accepts
//! a `declare-fun` ONLY at the native collection signature
//! (`(Array ..) (Array ..) -> Bool`); `declare-const`, `define-fun(-rec)`,
//! datatype member names and every mismatched signature are rejected at
//! elaboration. A surviving application therefore always denotes the native
//! predicate, and a declaration at that signature is documented to *request*
//! exactly these semantics.
//!
//! This module does not take that on the frontend's word. Every schema below
//! ALSO re-derives the native shape from the clause: the operator must have
//! exactly two arguments, both must be array-sorted with the same sort, and
//! the carrier's element sort must be the one the schema's semantics needs
//! (`Bool` for the set membership carrier, `Int` for the multiset multiplicity
//! carrier). A two-argument `set.subset` over non-arrays — the shape a forged
//! declaration would have to take — is rejected here even if it ever reached
//! the checker.
//!
//! The schemas are deliberately exact. A lemma kind is a licence to believe a
//! clause with no derivation behind it, so a loose schema is a forging
//! surface: accepting `(X.subset a b)` for SYNTACTICALLY DIFFERENT `a` and `b`
//! would licence an arbitrary subset claim and let a refutation be built out
//! of nothing.

use ay_core::{ProofId, Sort, Symbol, TermData, TermId, TermStore};

use crate::ProofCheckError;

#[cfg(test)]
#[path = "subset_axiom_tests.rs"]
mod tests;

/// The three collection subset predicates AY interprets natively.
///
/// All three are reflexive and all three entail their element-wise definition,
/// which is the whole content of the two schemas in this module:
///
/// * `set.subset a b`      — `∀e. select(a,e) → select(b,e)`   (Bool carrier)
/// * `multiset.subset a b` — `∀e. select(a,e) ≤ select(b,e)`   (Int carrier)
/// * `map.subset a b`      — domain containment plus value agreement on the
///   contained keys. Its element-wise form needs the `map.dom` projection and
///   is NOT covered by [`validate_subset_element_instance`]; only reflexivity
///   is claimed for it here.
const SUBSET_OPS: [&str; 3] = ["set.subset", "map.subset", "multiset.subset"];

/// The subset predicate whose carrier element sort is `Bool` (membership).
const SET_SUBSET: &str = "set.subset";

/// The subset predicate whose carrier element sort is `Int` (multiplicity).
const MULTISET_SUBSET: &str = "multiset.subset";

/// Decode `(X.subset a b)` for one of the natively-interpreted subset
/// predicates, re-deriving the native collection signature from the term
/// itself: exactly two arguments, both array-sorted, both of the SAME array
/// sort, and the application Bool-sorted.
///
/// Returns the operator name alongside the operands so a caller can demand a
/// particular carrier element sort.
fn decode_subset_atom(terms: &TermStore, term: TermId) -> Option<(&'static str, TermId, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    let op = SUBSET_OPS.iter().find(|&&known| known == name)?;
    let [left, right] = args.as_slice() else {
        return None;
    };
    if !matches!(terms.sort(term), Sort::Bool) {
        return None;
    }
    // The native signature. A forged declaration cannot reach elaboration at
    // any other shape, and this re-check means the schema does not depend on
    // that frontend gate staying correct.
    if !matches!(terms.sort(*left), Sort::Array(_)) || terms.sort(*left) != terms.sort(*right) {
        return None;
    }
    Some((op, *left, *right))
}

/// The element sort of an array-sorted term, if it is one.
fn array_element_sort(terms: &TermStore, term: TermId) -> Option<&Sort> {
    match terms.sort(term) {
        Sort::Array(array_sort) => Some(&array_sort.element_sort),
        _ => None,
    }
}

/// Decode `(select a e)` with a well-sorted array operand.
fn decode_select(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if name != "select" {
        return None;
    }
    let [array, index] = args.as_slice() else {
        return None;
    };
    let Sort::Array(array_sort) = terms.sort(*array) else {
        return None;
    };
    // The read must be well-sorted at both ends, so a mis-sorted lookalike
    // cannot masquerade as the membership/count probe.
    if terms.sort(*index) != &array_sort.index_sort || terms.sort(term) != &array_sort.element_sort
    {
        return None;
    }
    Some((*array, *index))
}

/// Strip one `not`.
fn negated(terms: &TermStore, term: TermId) -> Option<TermId> {
    match terms.get(term) {
        TermData::Not(inner) => Some(*inner),
        _ => None,
    }
}

/// Flatten a unit clause whose single literal is an `or`.
///
/// The multiset lemma reaches the checker as `(cl (or ..))`; the set lemma
/// reaches it already flattened. Accepting both spellings of the SAME clause
/// widens nothing: the literal multiset the schema checks is identical.
fn flatten_clause_literals(terms: &TermStore, clause: &[TermId]) -> Vec<TermId> {
    if let [single] = clause {
        if let TermData::App(Symbol::Named(name), args) = terms.get(*single) {
            if name == "or" {
                return args.clone();
            }
        }
    }
    clause.to_vec()
}

fn reject(step_id: ProofId, reason: String) -> Result<(), ProofCheckError> {
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    })
}

/// Validate a [`TheoryLemmaKind::SubsetReflexive`] lemma: exactly
/// `(cl (X.subset a a))`.
///
/// `a ⊆ a` holds in every model of all three collection theories, with no side
/// condition on `a` whatsoever — which is exactly what makes the schema
/// checkable without any problem context. The load-bearing requirement is that
/// the two operands be the SAME term: `(X.subset a b)` for distinct `a` and
/// `b` is an arbitrary subset claim, and admitting it would licence a
/// refutation out of nothing.
///
/// Syntactic identity is demanded, not provable equality. Two operands the
/// problem merely proves equal are rejected fail-closed; that costs
/// completeness on a shape the solver does not emit and keeps the schema
/// decidable by inspection.
///
/// [`TheoryLemmaKind::SubsetReflexive`]: ay_core::TheoryLemmaKind::SubsetReflexive
pub(crate) fn validate_subset_reflexive(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let [literal] = clause else {
        return reject(
            step_id,
            format!(
                "subset-reflexive clause must be the single literal `(X.subset a a)`, \
                 got {} literals",
                clause.len()
            ),
        );
    };
    let Some((_, left, right)) = decode_subset_atom(terms, *literal) else {
        return reject(
            step_id,
            "subset-reflexive literal must be a POSITIVE application of `set.subset`, \
             `map.subset` or `multiset.subset` to two operands of one common array sort"
                .to_string(),
        );
    };
    if left != right {
        return reject(
            step_id,
            "subset-reflexive requires the two operands to be the SAME term; \
             a subset claim between DIFFERENT collections is not a tautology"
                .to_string(),
        );
    }
    Ok(())
}

/// Validate a [`TheoryLemmaKind::SubsetElementInstance`] lemma: the subset
/// definition instantiated at ONE element term.
///
/// Two exact sub-schemas, one per carrier. In both, `A`, `B` and `E` must be
/// the same terms throughout — the identity IS the content of the axiom, and
/// relaxing it would licence `A ⊆ B ⇒ e ∈ C` for an unrelated `C`.
///
/// (a) SET membership, over the `Array(I → Bool)` membership carrier:
///
/// ```text
/// (cl (not (set.subset A B)) (not (select A E)) (select B E))
/// ```
///
/// This is `A ⊆ B → (E ∈ A → E ∈ B)`, the defining property of ⊆.
///
/// (b) MULTISET multiplicity, over the `Array(I → Int)` count carrier:
///
/// ```text
/// (cl (not (multiset.subset A B)) (<= (select A E) (select B E)))
/// ```
///
/// This is `A ⊆ B → count(A, E) ≤ count(B, E)`, the defining property of
/// multiset inclusion.
///
/// Both are entailed by the subset atom alone, so the clause is valid under
/// every interpretation and needs no problem context.
///
/// `map.subset` is deliberately absent. Its element-wise definition is a
/// CONJUNCTION over the `map.dom` projection (domain containment plus value
/// agreement on contained keys), not the single implication above, so no
/// sub-schema here claims anything about it and a `map.subset` clause fails
/// closed.
///
/// [`TheoryLemmaKind::SubsetElementInstance`]: ay_core::TheoryLemmaKind::SubsetElementInstance
pub(crate) fn validate_subset_element_instance(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let literals = flatten_clause_literals(terms, clause);
    for literal in &literals {
        if !matches!(terms.sort(*literal), Sort::Bool) {
            return reject(
                step_id,
                format!(
                    "subset-element-instance literal has non-Bool sort {:?}; \
                     axiom clauses must be propositional",
                    terms.sort(*literal)
                ),
            );
        }
    }
    if matches_set_membership_instance(terms, &literals)
        || matches_multiset_count_instance(terms, &literals)
    {
        return Ok(());
    }
    reject(
        step_id,
        "subset-element-instance clause does not match either exact schema: \
         `(cl (not (set.subset A B)) (not (select A E)) (select B E))` over an \
         `Array(I -> Bool)` membership carrier, or \
         `(cl (not (multiset.subset A B)) (<= (select A E) (select B E)))` over an \
         `Array(I -> Int)` multiplicity carrier, with A, B and E identical throughout"
            .to_string(),
    )
}

/// Sub-schema (a): `(cl (not (set.subset A B)) (not (select A E)) (select B E))`.
///
/// Literal ORDER is free (the emitter and the SAT trace may permute a clause),
/// but the literal SET is exact: one negated subset atom, one negated read of
/// the subset operand, one positive read of the superset operand, all at one
/// index. Nothing else may be present.
fn matches_set_membership_instance(terms: &TermStore, literals: &[TermId]) -> bool {
    if literals.len() != 3 {
        return false;
    }
    for (subset_position, &subset_literal) in literals.iter().enumerate() {
        let Some(atom) = negated(terms, subset_literal) else {
            continue;
        };
        let Some((op, sub, sup)) = decode_subset_atom(terms, atom) else {
            continue;
        };
        // Membership is `select`, so the carrier must be Bool-valued. A
        // multiset (Int carrier) reaching this arm would make `(select A E)` a
        // non-Bool literal, but pinning the sort keeps the two sub-schemas
        // disjoint by construction rather than by accident.
        if op != SET_SUBSET || array_element_sort(terms, sub) != Some(&Sort::Bool) {
            continue;
        }
        let rest: Vec<TermId> = literals
            .iter()
            .enumerate()
            .filter(|&(position, _)| position != subset_position)
            .map(|(_, &literal)| literal)
            .collect();
        let [first, second] = rest.as_slice() else {
            continue;
        };
        // The remaining two literals are the antecedent and the consequent, in
        // either order.
        for (negative, positive) in [(*first, *second), (*second, *first)] {
            let Some(negative_atom) = negated(terms, negative) else {
                continue;
            };
            let (Some((sub_array, sub_index)), Some((sup_array, sup_index))) = (
                decode_select(terms, negative_atom),
                decode_select(terms, positive),
            ) else {
                continue;
            };
            if sub_array == sub && sup_array == sup && sub_index == sup_index {
                return true;
            }
        }
    }
    false
}

/// Sub-schema (b): `(cl (not (multiset.subset A B)) (<= (select A E) (select B E)))`.
fn matches_multiset_count_instance(terms: &TermStore, literals: &[TermId]) -> bool {
    if literals.len() != 2 {
        return false;
    }
    for (subset_position, &subset_literal) in literals.iter().enumerate() {
        let Some(atom) = negated(terms, subset_literal) else {
            continue;
        };
        let Some((op, sub, sup)) = decode_subset_atom(terms, atom) else {
            continue;
        };
        // Multiplicities are Int-valued; the `<=` below is integer comparison
        // of two counts, so a Bool (membership) carrier is out of schema.
        if op != MULTISET_SUBSET || array_element_sort(terms, sub) != Some(&Sort::Int) {
            continue;
        }
        let bound = literals[1 - subset_position];
        let TermData::App(Symbol::Named(comparison), comparison_args) = terms.get(bound) else {
            continue;
        };
        if comparison != "<=" {
            continue;
        }
        let [lesser, greater] = comparison_args.as_slice() else {
            continue;
        };
        // ORIENTATION IS LOAD-BEARING and is NOT searched: the count of the
        // SUBSET operand must be on the `<=`'s left. The mirror image
        // (`count(B,E) <= count(A,E)`) is the converse claim and is false.
        let (Some((sub_array, sub_index)), Some((sup_array, sup_index))) = (
            decode_select(terms, *lesser),
            decode_select(terms, *greater),
        ) else {
            continue;
        };
        if sub_array == sub && sup_array == sup && sub_index == sup_index {
            return true;
        }
    }
    false
}

/// Validate a [`TheoryLemmaKind::SubsetTransitive`] lemma:
/// `(cl (not (X.subset A B)) (not (X.subset B C)) (X.subset A C))`.
///
/// WHY IT IS A TAUTOLOGY. All three predicates order their carriers
/// POINTWISE — `set` by Boolean implication on the membership carrier,
/// `multiset` by `<=` on the multiplicity carrier, `map` by domain containment
/// plus value agreement on the contained keys — and every one of those orders
/// is transitive. (For `map`: `dom(A) ⊆ dom(B) ⊆ dom(C)` gives
/// `dom(A) ⊆ dom(C)`, and for `k ∈ dom(A)` we have `A[k] = B[k]` and, since
/// `k ∈ dom(B)`, `B[k] = C[k]`.) So no side condition on `A`, `B` or `C` is
/// needed and the clause is valid under every interpretation.
///
/// WHAT IS RE-DERIVED HERE. The CHAIN, which is the entire content of the
/// axiom. The clause must hold exactly three subset atoms over ONE operator at
/// ONE common array sort: two negated and one positive, with the positive
/// atom's operands being the two free ends of a path through a shared middle
/// term. A triple that does not connect — `(cl ¬(A⊆B) ¬(C⊆D) (A⊆D))` — would
/// licence an arbitrary subset claim, so it is rejected fail-closed.
///
/// Middle-term identity is SYNTACTIC. Two terms the problem merely proves
/// equal are refused; that costs completeness on a shape the reconstruction
/// does not emit and keeps the schema decidable by inspection.
///
/// [`TheoryLemmaKind::SubsetTransitive`]: ay_core::TheoryLemmaKind::SubsetTransitive
pub(crate) fn validate_subset_transitive(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let literals = flatten_clause_literals(terms, clause);
    if literals.len() != 3 {
        return reject(
            step_id,
            format!(
                "subset-transitive clause must be exactly three literals \
                 `(cl (not (X.subset A B)) (not (X.subset B C)) (X.subset A C))`, \
                 got {}",
                literals.len()
            ),
        );
    }
    for (conclusion_position, &conclusion_literal) in literals.iter().enumerate() {
        let Some((conclusion_op, left, right)) = decode_subset_atom(terms, conclusion_literal)
        else {
            continue;
        };
        let premises: Vec<TermId> = literals
            .iter()
            .enumerate()
            .filter(|&(position, _)| position != conclusion_position)
            .map(|(_, &literal)| literal)
            .collect();
        let [first, second] = premises.as_slice() else {
            continue;
        };
        // Both premises must be NEGATED atoms of the SAME operator; the whole
        // clause therefore lives in one collection theory at one array sort
        // (`decode_subset_atom` already pins both operands to one array sort).
        let (Some(first_atom), Some(second_atom)) =
            (negated(terms, *first), negated(terms, *second))
        else {
            continue;
        };
        let (Some((first_op, first_sub, first_sup)), Some((second_op, second_sub, second_sup))) = (
            decode_subset_atom(terms, first_atom),
            decode_subset_atom(terms, second_atom),
        ) else {
            continue;
        };
        if first_op != conclusion_op || second_op != conclusion_op {
            continue;
        }
        if terms.sort(first_sub) != terms.sort(left) || terms.sort(second_sub) != terms.sort(left) {
            continue;
        }
        // The two premises may appear in either order; the CHAIN is what must
        // hold. `left → middle → right` with a shared middle term.
        for (near, far) in [
            ((first_sub, first_sup), (second_sub, second_sup)),
            ((second_sub, second_sup), (first_sub, first_sup)),
        ] {
            if near.0 == left && far.1 == right && near.1 == far.0 {
                return Ok(());
            }
        }
    }
    reject(
        step_id,
        "subset-transitive clause does not match \
         `(cl (not (X.subset A B)) (not (X.subset B C)) (X.subset A C))`: it needs two \
         NEGATED and one POSITIVE application of ONE subset operator at one common \
         array sort, chained through a shared middle term"
            .to_string(),
    )
}

/// Work bound on one ground carrier's `store` chain. A longer chain simply
/// fails closed, which costs completeness and never soundness.
const MAX_GROUND_CARRIER_STORES: usize = 4096;

/// A ground collection carrier in normal form: a constant fill plus the
/// EFFECTIVE constant entries written over it.
#[derive(Clone)]
struct GroundCarrier {
    /// The constant every unlisted index takes.
    fill: TermId,
    /// `(index, value)` in outermost-wins order, indices pairwise distinct.
    entries: Vec<(TermId, TermId)>,
}

impl GroundCarrier {
    /// The carrier's value at `index`, which is the explicit entry when there
    /// is one and the fill otherwise.
    fn at(&self, index: TermId) -> TermId {
        self.entries
            .iter()
            .find(|&&(entry_index, _)| entry_index == index)
            .map_or(self.fill, |&(_, value)| value)
    }

    /// Every index the two carriers mention explicitly, without duplicates.
    fn mentioned_indices(&self, other: &Self) -> Vec<TermId> {
        let mut indices: Vec<TermId> = Vec::new();
        for &(index, _) in self.entries.iter().chain(other.entries.iter()) {
            if !indices.contains(&index) {
                indices.push(index);
            }
        }
        indices
    }
}

/// Decode a GROUND carrier: `((as const (Array I E)) d)` under a bounded,
/// cycle-free chain of `store`s at CONSTANT indices with CONSTANT values.
///
/// Everything is re-derived: each node must be a well-sorted array `store` at
/// the carrier's own sort, every index and value must be an interned
/// `TermData::Const` (so `TermId` identity IS value identity, the property the
/// pointwise decision below relies on), and the base must be a constant array
/// with a constant fill. A variable index, a symbolic value, a `lambda`
/// carrier or an over-long chain all return `None`.
///
/// The walk is OUTERMOST-FIRST and the first entry seen for an index wins,
/// which is exactly `store` semantics: an inner write to an already-overwritten
/// index is invisible.
fn decode_ground_carrier(terms: &TermStore, array: TermId) -> Option<GroundCarrier> {
    let Sort::Array(array_sort) = terms.sort(array) else {
        return None;
    };
    let expected = array_sort.as_ref().clone();
    let expected_array_sort = Sort::Array(Box::new(expected.clone()));

    let mut entries: Vec<(TermId, TermId)> = Vec::new();
    let mut seen: Vec<TermId> = Vec::new();
    let mut current = array;
    for _ in 0..=MAX_GROUND_CARRIER_STORES {
        if seen.contains(&current) || terms.sort(current) != &expected_array_sort {
            return None;
        }
        seen.push(current);
        if let Some(fill) = terms.get_const_array(current) {
            if !matches!(terms.get(fill), TermData::Const(_))
                || terms.sort(fill) != &expected.element_sort
            {
                return None;
            }
            return Some(GroundCarrier { fill, entries });
        }
        let TermData::App(Symbol::Named(symbol), args) = terms.get(current) else {
            return None;
        };
        let [base, index, value] = args.as_slice() else {
            return None;
        };
        if symbol != "store"
            || terms.sort(*base) != &expected_array_sort
            || terms.sort(*index) != &expected.index_sort
            || terms.sort(*value) != &expected.element_sort
            || !matches!(terms.get(*index), TermData::Const(_))
            || !matches!(terms.get(*value), TermData::Const(_))
        {
            return None;
        }
        // Outermost wins: only record an index not already written above.
        if !entries.iter().any(|&(seen_index, _)| seen_index == *index) {
            entries.push((*index, *value));
        }
        current = *base;
    }
    None
}

/// The Boolean value of an interned Bool constant.
fn bool_constant(terms: &TermStore, term: TermId) -> Option<bool> {
    match terms.get(term) {
        TermData::Const(ay_core::Constant::Bool(value)) => Some(*value),
        _ => None,
    }
}

/// The integer value of an interned Int constant.
fn int_constant(terms: &TermStore, term: TermId) -> Option<&num_bigint::BigInt> {
    match terms.get(term) {
        TermData::Const(ay_core::Constant::Int(value)) => Some(value),
        _ => None,
    }
}

/// Decide `sub ⊆ sup` EXACTLY for two ground carriers of `op`.
///
/// `Some(true)` / `Some(false)` are decisions; `None` means the pair is outside
/// the fragment this evaluator decides and the caller must fail closed.
///
/// SET (Bool carrier): `A ⊆ B` iff `∀i. A[i] → B[i]`. The explicit indices are
/// checked pointwise. For the residual (unlisted) indices both carriers take
/// their fills, so `fill(A) → fill(B)` is required as well — unconditionally,
/// even though a finite index sort fully covered by the explicit entries would
/// not need it. That is a deliberate one-sided approximation: demanding MORE
/// can only refuse a valid lemma, never admit an invalid one.
///
/// MULTISET (Int carrier): the same with `<=` on multiplicities.
///
/// `map.subset` is absent. Its order is domain containment plus value
/// agreement over the `map.dom` projection, NOT the pointwise order of the
/// carrier, so no decision here would be about the right relation.
fn decide_ground_subset(
    terms: &TermStore,
    op: &str,
    sub: &GroundCarrier,
    sup: &GroundCarrier,
) -> Option<bool> {
    let indices = sub.mentioned_indices(sup);
    match op {
        SET_SUBSET => {
            if !bool_constant(terms, sub.fill)?.le(&bool_constant(terms, sup.fill)?) {
                return Some(false);
            }
            for index in indices {
                let member = bool_constant(terms, sub.at(index))?;
                let contains = bool_constant(terms, sup.at(index))?;
                if member && !contains {
                    return Some(false);
                }
            }
            Some(true)
        }
        MULTISET_SUBSET => {
            if int_constant(terms, sub.fill)? > int_constant(terms, sup.fill)? {
                return Some(false);
            }
            for index in indices {
                if int_constant(terms, sub.at(index))? > int_constant(terms, sup.at(index))? {
                    return Some(false);
                }
            }
            Some(true)
        }
        _ => None,
    }
}

/// An EXPLICIT witness index at which `sub ⊆ sup` fails, if one is listed.
///
/// A negative conclusion needs an index the containment actually violates.
/// Only indices the carriers MENTION qualify: a violation that exists solely
/// among the residual indices would need the index sort's cardinality to be
/// larger than the explicit entry count, which this validator does not
/// establish, so that case fails closed.
fn ground_subset_explicit_witness(
    terms: &TermStore,
    op: &str,
    sub: &GroundCarrier,
    sup: &GroundCarrier,
) -> bool {
    sub.mentioned_indices(sup)
        .into_iter()
        .any(|index| match op {
            SET_SUBSET => {
                bool_constant(terms, sub.at(index)) == Some(true)
                    && bool_constant(terms, sup.at(index)) == Some(false)
            }
            MULTISET_SUBSET => {
                match (
                    int_constant(terms, sub.at(index)),
                    int_constant(terms, sup.at(index)),
                ) {
                    (Some(member), Some(contains)) => member > contains,
                    _ => false,
                }
            }
            _ => false,
        })
}

/// Whether `carrier` is the pointwise BOTTOM of the set order — empty
/// everywhere — so that it is a subset of ABSOLUTELY ANY collection.
fn is_everywhere_empty_set(terms: &TermStore, carrier: &GroundCarrier) -> bool {
    bool_constant(terms, carrier.fill) == Some(false)
        && carrier
            .entries
            .iter()
            .all(|&(_, value)| bool_constant(terms, value) == Some(false))
}

/// Whether `carrier` is the pointwise TOP of the set order — full everywhere —
/// so that ABSOLUTELY ANY collection is a subset of it.
fn is_everywhere_full_set(terms: &TermStore, carrier: &GroundCarrier) -> bool {
    bool_constant(terms, carrier.fill) == Some(true)
        && carrier
            .entries
            .iter()
            .all(|&(_, value)| bool_constant(terms, value) == Some(true))
}

/// One `operand := ground` replacement licensed by a clause-carried binding.
struct GroundBinding {
    operand: TermId,
    ground: GroundCarrier,
}

/// Validate a [`TheoryLemmaKind::SubsetGroundEval`] lemma.
///
/// The clause is ONE subset atom, positive or negated, plus zero or more
/// BINDING literals `(not (= v g))` in which `v` is one of that atom's two
/// operands and `g` is a ground carrier (see [`decode_ground_carrier`]).
/// Nothing else may be present.
///
/// SOUNDNESS. Take any valuation and suppose it falsifies the clause. Every
/// binding literal is then false, so each `(= v g)` is TRUE and `v` and `g`
/// denote the same collection; by congruence the conclusion atom has the same
/// truth value under the substitution `v := g` as it does without it. The
/// substituted atom is decided EXACTLY by [`decide_ground_subset`] (or, where
/// an operand stays unbound, by a bound of the set order that holds for every
/// value of it), and the decision agrees with the conclusion's polarity — so
/// the conclusion is true under that valuation, contradicting the assumption.
/// The clause therefore has no falsifying valuation.
///
/// Everything a decision needs is re-derived from the clause here: the
/// operator, the native array signature, the carrier normal forms, and the
/// pointwise comparison. A binding whose `v` is not an operand, a second
/// binding for the same operand, a non-ground right-hand side, an unbound
/// operand the decision needs, a polarity the decision contradicts, or any
/// extra literal all fail closed.
///
/// [`TheoryLemmaKind::SubsetGroundEval`]: ay_core::TheoryLemmaKind::SubsetGroundEval
pub(crate) fn validate_subset_ground_eval(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let literals = flatten_clause_literals(terms, clause);
    for literal in &literals {
        if !matches!(terms.sort(*literal), Sort::Bool) {
            return reject(
                step_id,
                format!(
                    "subset-ground-eval literal has non-Bool sort {:?}; \
                     axiom clauses must be propositional",
                    terms.sort(*literal)
                ),
            );
        }
    }

    // Exactly one literal must be the CONCLUSION: a subset atom, or the
    // negation of one. Everything else must be a binding.
    let mut conclusion: Option<(usize, bool, &'static str, TermId, TermId)> = None;
    for (position, &literal) in literals.iter().enumerate() {
        let decoded = decode_subset_atom(terms, literal)
            .map(|(op, sub, sup)| (true, op, sub, sup))
            .or_else(|| {
                negated(terms, literal)
                    .and_then(|atom| decode_subset_atom(terms, atom))
                    .map(|(op, sub, sup)| (false, op, sub, sup))
            });
        let Some((polarity, op, sub, sup)) = decoded else {
            continue;
        };
        if conclusion.is_some() {
            return reject(
                step_id,
                "subset-ground-eval clause carries more than one subset atom; \
                 exactly one literal may be the conclusion"
                    .to_string(),
            );
        }
        conclusion = Some((position, polarity, op, sub, sup));
    }
    let Some((conclusion_position, claims_subset, op, sub_operand, sup_operand)) = conclusion
    else {
        return reject(
            step_id,
            "subset-ground-eval clause has no subset atom to decide".to_string(),
        );
    };

    // Every remaining literal must be `(not (= operand ground))` for a
    // DISTINCT operand of the conclusion atom.
    let mut bindings: Vec<GroundBinding> = Vec::new();
    for (position, &literal) in literals.iter().enumerate() {
        if position == conclusion_position {
            continue;
        }
        let Some(equality) = negated(terms, literal) else {
            return reject(
                step_id,
                "subset-ground-eval clause carries a literal that is neither the \
                 conclusion nor a negated ground binding `(not (= v g))`"
                    .to_string(),
            );
        };
        let TermData::App(Symbol::Named(name), args) = terms.get(equality) else {
            return reject(
                step_id,
                "subset-ground-eval binding literal must negate an equality".to_string(),
            );
        };
        let ([left, right], "=") = (args.as_slice(), name.as_str()) else {
            return reject(
                step_id,
                "subset-ground-eval binding literal must negate a BINARY equality".to_string(),
            );
        };
        // Either orientation is admissible; the operand side is whichever one
        // IS an operand of the conclusion atom.
        let bound = [(*left, *right), (*right, *left)]
            .into_iter()
            .find(|&(operand, _)| operand == sub_operand || operand == sup_operand);
        let Some((operand, ground_term)) = bound else {
            return reject(
                step_id,
                "subset-ground-eval binding does not pin either operand of the \
                 conclusion's subset atom"
                    .to_string(),
            );
        };
        if bindings.iter().any(|existing| existing.operand == operand) {
            return reject(
                step_id,
                "subset-ground-eval clause binds one operand twice".to_string(),
            );
        }
        let Some(ground) = decode_ground_carrier(terms, ground_term) else {
            return reject(
                step_id,
                "subset-ground-eval binding's right-hand side is not a GROUND collection \
                 carrier (a constant array under a finite chain of stores at constant \
                 indices with constant values)"
                    .to_string(),
            );
        };
        bindings.push(GroundBinding { operand, ground });
    }

    // An operand is ground either because a binding pins it or because the
    // operand written into the clause already IS a ground carrier.
    let ground_for = |operand: TermId| -> Option<GroundCarrier> {
        bindings
            .iter()
            .find(|binding| binding.operand == operand)
            .map(|binding| binding.ground.clone())
            .or_else(|| decode_ground_carrier(terms, operand))
    };
    let sub_ground = ground_for(sub_operand);
    let sup_ground = ground_for(sup_operand);

    match (claims_subset, &sub_ground, &sup_ground) {
        // Both sides ground: decide exactly.
        (true, Some(sub), Some(sup)) if decide_ground_subset(terms, op, sub, sup) == Some(true) => {
            return Ok(());
        }
        // A negative claim needs a witness the carriers actually list, and the
        // pointwise decision must agree that containment fails.
        (false, Some(sub), Some(sup))
            if decide_ground_subset(terms, op, sub, sup) == Some(false)
                && ground_subset_explicit_witness(terms, op, sub, sup) =>
        {
            return Ok(());
        }
        // Only the SUBSET side is ground. `∅ ⊆ B` holds for every `B`, and
        // that is the only universally valid case: the set order's bottom.
        (true, Some(sub), None) if op == SET_SUBSET && is_everywhere_empty_set(terms, sub) => {
            return Ok(());
        }
        // Only the SUPERSET side is ground. `A ⊆ full` holds for every `A`.
        (true, None, Some(sup)) if op == SET_SUBSET && is_everywhere_full_set(terms, sup) => {
            return Ok(());
        }
        // A negative claim with an unbound operand is never universally valid:
        // the unbound side can always be chosen to make containment hold.
        _ => {}
    }

    reject(
        step_id,
        "subset-ground-eval clause is not decided: the conclusion's polarity must be \
         established by an EXACT pointwise decision over ground `set`/`multiset` \
         carriers (with an explicitly listed witness index for a negative claim), or, \
         with one operand unbound, by the set order's bottom/top"
            .to_string(),
    )
}

/// The CHECKER'S OWN matcher for the subset schemas.
///
/// Producers call this instead of re-implementing the schema, so there is
/// exactly one description of what qualifies and it lives on the checking
/// side. A `Some` answer is a hint only: the returned kind is re-validated by
/// `validate_subset_reflexive` / `validate_subset_element_instance` /
/// `validate_subset_transitive` / `validate_subset_ground_eval` when the
/// proof is checked, so a matcher bug can cost completeness but cannot admit
/// an unchecked clause.
#[must_use]
pub fn recognize_subset_theory_lemma(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<ay_core::TheoryLemmaKind> {
    use ay_core::TheoryLemmaKind;

    if validate_subset_reflexive(terms, ProofId(0), clause).is_ok() {
        return Some(TheoryLemmaKind::SubsetReflexive);
    }
    if validate_subset_element_instance(terms, ProofId(0), clause).is_ok() {
        return Some(TheoryLemmaKind::SubsetElementInstance);
    }
    if validate_subset_transitive(terms, ProofId(0), clause).is_ok() {
        return Some(TheoryLemmaKind::SubsetTransitive);
    }
    if validate_subset_ground_eval(terms, ProofId(0), clause).is_ok() {
        return Some(TheoryLemmaKind::SubsetGroundEval);
    }
    None
}
