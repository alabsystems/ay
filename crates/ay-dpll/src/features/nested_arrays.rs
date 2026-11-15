// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Nested-array detection that sees through datatype carriers.
//!
//! `detect_sort_theory` flags an array whose index or element sort is or
//! contains an array, but it can only look inside an INLINE `Sort::Datatype`.
//! A `declare-datatype` carrier arrives as a nominal `Sort::Uninterpreted`
//! identity, so `(Array (_ BitVec 32) Row)` with
//! `(declare-datatype Row ((mk_row (cells (Array (_ BitVec 32) (_ BitVec 32))))))`
//! read as flat. 997e86097 had already pinned the rule this broke: "the public
//! wrong-UNSAT quarantine must not be bypassable merely by wrapping the inner
//! array in a tuple/record carrier". Measured at ad60a0707: the record-boxed
//! twin of `repros/abv-nested-array-quantified-unsat-quarantine.smt2` published
//! `unsat` with `unsat_admission=discharged-trust` behind a bare
//! `(step t0 (cl) :rule hole)`, while the directly nested original is withheld
//! (#nested-array-quarantine-datatype-fields).
//!
//! This pass resolves declared carriers through the field sorts the declaring
//! layer registers in the store (`TermStore::datatype_field_sorts`). A sort
//! CARRIES a nested array when some array reachable from it — through array
//! index/element sorts, `Seq` elements, or datatype fields — has an index or
//! element sort that itself reaches an array. That covers `(Array I Row)` with
//! an array field in `Row`, and also a lone `Row` value whose field is such an
//! array: datatype injectivity turns `(not (= r1 r2))` into a disequality
//! between the field arrays exactly as an outer array's extensionality does.
//! A record whose only arrays are flat stays flat.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{term::TermData, Sort, TermId, TermStore};

use super::StaticFeatures;

impl StaticFeatures {
    /// Whether any term or quantifier-bound variable visited by `collect`
    /// has a sort that carries a nested array.
    pub(super) fn visited_sorts_carry_nested_array<'a>(
        terms: &'a TermStore,
        visited: &HashSet<TermId>,
    ) -> bool {
        let mut checked: HashSet<&'a Sort> = HashSet::default();
        let mut carries = |sort: &'a Sort| {
            // Scalar sorts cannot reach an array; skip them before hashing.
            matches!(
                sort,
                Sort::Array(_) | Sort::Seq(_) | Sort::Datatype(_) | Sort::Uninterpreted(_)
            ) && checked.insert(sort)
                && sort_carries_nested_array(terms, sort)
        };
        visited.iter().any(|&id| {
            carries(terms.sort(id))
                || match terms.get(id) {
                    TermData::Forall(bound, _, _) | TermData::Exists(bound, _, _) => {
                        bound.iter().any(|(_, sort)| carries(sort))
                    }
                    _ => false,
                }
        })
    }
}

impl StaticFeatures {
    /// Whether `sort` is an array or reaches one through `Seq` elements or
    /// datatype fields, declared carriers included.
    ///
    /// The same walk `has_nested_arrays` uses, exported for a consumer that
    /// must know a sort is array-free: the nested-array quarantine's
    /// array-to-UF abstraction keeps a sort unchanged only when this is false,
    /// so a declared carrier cannot smuggle an array past it either.
    pub(crate) fn sort_reaches_array(terms: &TermStore, sort: &Sort) -> bool {
        sort_reaches_array(terms, sort)
    }
}

/// Whether some array reachable from `sort` nests an array.
fn sort_carries_nested_array(terms: &TermStore, sort: &Sort) -> bool {
    let mut expanded = HashSet::default();
    let mut work = vec![sort];
    while let Some(current) = work.pop() {
        if let Sort::Array(array) = current {
            if sort_reaches_array(terms, &array.index_sort)
                || sort_reaches_array(terms, &array.element_sort)
            {
                return true;
            }
            // Neither side reaches any array, so nothing below can nest one.
            continue;
        }
        push_components(terms, current, &mut expanded, &mut work);
    }
    false
}

/// Whether `sort` is an array or reaches one through `Seq` elements or
/// datatype fields.
fn sort_reaches_array(terms: &TermStore, sort: &Sort) -> bool {
    let mut expanded = HashSet::default();
    let mut work = vec![sort];
    while let Some(current) = work.pop() {
        if matches!(current, Sort::Array(_)) {
            return true;
        }
        push_components(terms, current, &mut expanded, &mut work);
    }
    false
}

/// Push the component sorts of a non-array `sort`. Each inline schema and
/// each registered carrier is expanded at most once per walk (`true` keys an
/// inline schema), which bounds the walk by the size of the declarations and
/// terminates on recursive carriers. An inline schema may share its name with
/// a registered carrier; both field lists are walked so neither can hide an
/// array.
fn push_components<'a>(
    terms: &'a TermStore,
    sort: &'a Sort,
    expanded: &mut HashSet<(bool, &'a str)>,
    work: &mut Vec<&'a Sort>,
) {
    let name = match sort {
        Sort::Seq(element) => {
            work.push(element.as_ref());
            return;
        }
        Sort::Datatype(datatype) => {
            if expanded.insert((true, datatype.name.as_str())) {
                for constructor in &datatype.constructors {
                    work.extend(constructor.fields.iter().map(|field| &field.sort));
                }
            }
            datatype.name.as_str()
        }
        Sort::Uninterpreted(name) => name.as_str(),
        _ => return,
    };
    if expanded.insert((false, name)) {
        work.extend(terms.datatype_field_sorts(name).into_iter().flatten());
    }
}

#[cfg(test)]
mod tests;
