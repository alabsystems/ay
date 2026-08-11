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

/// The CHECKER'S OWN matcher for the subset schemas.
///
/// Producers call this instead of re-implementing the schema, so there is
/// exactly one description of what qualifies and it lives on the checking
/// side. A `Some` answer is a hint only: the returned kind is re-validated by
/// [`validate_subset_reflexive`] / [`validate_subset_element_instance`] when
/// the proof is checked, so a matcher bug can cost completeness but cannot
/// admit an unchecked clause.
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
    None
}
