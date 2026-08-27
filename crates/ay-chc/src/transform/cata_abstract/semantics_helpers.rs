// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

// Textually included by `cata_abstract` to keep recurrence expression helpers
// in the parent module's private namespace.

fn func_app(name: String, sort: ChcSort, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::FuncApp(name, sort, args.into_iter().map(Arc::new).collect())
}

/// Universally-true facts about one catamorphism value.
fn cata_min_facts(kind: &CataKind, value: &ChcExpr, n_ctors: usize) -> Vec<ChcExpr> {
    match kind {
        CataKind::Size | CataKind::Height => {
            vec![ChcExpr::ge(value.clone(), ChcExpr::int(1))]
        }
        CataKind::IntSum => Vec::new(),
        CataKind::CtorCount(_) => vec![ChcExpr::ge(value.clone(), ChcExpr::int(0))],
        CataKind::RootDisc => vec![
            ChcExpr::ge(value.clone(), ChcExpr::int(0)),
            ChcExpr::lt(value.clone(), ChcExpr::int(n_ctors.max(1) as i64)),
        ],
        // `min`/`max` have no universally-useful *small* bound: their only
        // universal fact is `min ≤ SENTINEL` / `max ≥ SENTINEL`, but emitting
        // that giant constant per tuple (×2 columns) floods the obligation's
        // LIA+ite search with large-magnitude bounds that make the datatype+UF
        // executor diverge (measured), for zero invariant value. Withhold it —
        // dropping a true fact only weakens the abstraction, which is sound.
        CataKind::Min | CataKind::Max => Vec::new(),
        // The sortedness fold is Boolean, encoded as `0/1`.
        CataKind::Sorted => vec![
            ChcExpr::ge(value.clone(), ChcExpr::int(0)),
            ChcExpr::le(value.clone(), ChcExpr::int(1)),
        ],
    }
}

/// Nested-`ite` integer minimum of a non-empty term list.
fn min_expr(mut terms: Vec<ChcExpr>) -> ChcExpr {
    let mut acc = terms.remove(0);
    for t in terms {
        acc = ChcExpr::ite(ChcExpr::le(acc.clone(), t.clone()), acc, t);
    }
    acc
}

/// Nested-`ite` integer maximum of a non-empty term list.
fn max_expr(mut terms: Vec<ChcExpr>) -> ChcExpr {
    let mut acc = terms.remove(0);
    for t in terms {
        acc = ChcExpr::ite(ChcExpr::ge(acc.clone(), t.clone()), acc, t);
    }
    acc
}

/// Is `expr` a constructor application of an *element-free leaf* — a
/// constructor with no `Int` and no recursive `Adt` fields (e.g. `nil`)?
///
/// Such a subtree is the `+∞`/`-∞` identity of `min`/`max` (and is vacuously
/// sorted), so it must be EXCLUDED from a parent's `Min`/`Max`/`Sorted`
/// recurrence rather than folded in through the finite `±1e9` sentinel. Folding
/// the sentinel in CLAMPS any real element above it: a singleton `[x]` with
/// `x > sentinel` would be mis-mined (`min = sentinel`) and deemed unsorted
/// (`x ≤ sentinel` fails) — a spurious model that makes the abstract `insert`
/// fail to preserve sortedness (Z3 confirmed: with the sentinel the L5 abstract
/// of the tip2015 sort proofs is `unsat`; excluding the leaf ⇒ `sat`). Exclusion
/// is EXACT (`min(cons(x,nil)) = min(x, +∞) = x`) so the per-clause obligation
/// still discharges. Only a STATIC leaf term is excluded — a variable tail's
/// `min` column is free (never the sentinel literal), so it never clamps.
fn is_empty_leaf_term(registry: &DtRegistry, expr: &ChcExpr) -> bool {
    if let ChcExpr::FuncApp(name, sort, _) = expr {
        if let Some(sort_name) = registry.adt_sort_name(sort) {
            if let Some(ctor) = registry.ctor(sort_name, name) {
                return ctor
                    .fields
                    .iter()
                    .all(|f| !matches!(f.kind, FieldKind::Int | FieldKind::Adt(_)));
            }
        }
    }
    false
}

/// Ascending-sortedness recurrence RHS shared by [`recurrence_rhs`] and
/// [`ctor_recurrence`]. `int_head` is the (ADT-free) head element if the
/// constructor carries one; `rest_mins` / `rest_sorteds` are the `min` and
/// `sorted` values of the recursive fields. Returns `None` (recurrence
/// withheld — sound under-constraint) when a head element exists but no `min`
/// column backs the comparison.
fn sorted_recurrence_rhs(
    int_head: Option<ChcExpr>,
    rest_mins: Option<Vec<ChcExpr>>,
    rest_sorteds: Vec<ChcExpr>,
) -> Option<ChcExpr> {
    // No recursive field ⇒ leaf/empty ⇒ vacuously sorted.
    if rest_sorteds.is_empty() {
        return Some(ChcExpr::int(1));
    }
    // Every recursive field must itself be sorted (`sorted_i = 1`).
    let all_sub_sorted = ChcExpr::and_all(
        rest_sorteds
            .into_iter()
            .map(|s| ChcExpr::eq(s, ChcExpr::int(1))),
    );
    // Head ≤ min(rest), when the constructor has a head element.
    let head_ok = match int_head {
        None => ChcExpr::Bool(true),
        Some(head) => {
            let mins = rest_mins?; // need the Min column to express this
            if mins.is_empty() {
                ChcExpr::Bool(true)
            } else {
                ChcExpr::le(head, min_expr(mins))
            }
        }
    };
    Some(ChcExpr::ite(
        ChcExpr::and(head_ok, all_sub_sorted),
        ChcExpr::int(1),
        ChcExpr::int(0),
    ))
}

fn sum_exprs(mut terms: Vec<ChcExpr>) -> ChcExpr {
    match terms.len() {
        0 => ChcExpr::int(0),
        1 => terms.remove(0),
        _ => {
            let mut acc = terms.remove(0);
            for term in terms {
                acc = ChcExpr::add(acc, term);
            }
            acc
        }
    }
}
