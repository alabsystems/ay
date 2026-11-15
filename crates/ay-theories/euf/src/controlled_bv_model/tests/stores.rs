// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod parity;
mod refusal;
mod resources;

struct StoreFixture {
    terms: TermStore,
    roots: Vec<TermId>,
    assignments: Vec<(TermId, bool)>,
    stores: [TermId; 3],
    reads: [TermId; 3],
    index: TermId,
    written: TermId,
}

fn literals(terms: &mut TermStore, sort: &Sort) -> [TermId; 2] {
    match sort {
        Sort::Bool => [terms.mk_bool(false), terms.mk_bool(true)],
        Sort::BitVec(bits) => [
            terms.mk_bitvec(
                (num_bigint::BigInt::from(1u8) << bits.width) - 1u8,
                bits.width,
            ),
            terms.mk_bitvec(0u8.into(), bits.width),
        ],
        _ => panic!("fixture supports only Bool/BV"),
    }
}

fn store_fixture(index_sort: Sort, cell_sort: Sort) -> StoreFixture {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(index_sort.clone(), cell_sort.clone());
    let base = terms.mk_var("store_base", array_sort.clone());
    let alias = terms.mk_var("store_alias", array_sort.clone());
    let indices = literals(&mut terms, &index_sort);
    let cells = literals(&mut terms, &cell_sort);
    let index = terms.mk_var("pinned_index", index_sort);
    let written = terms.mk_var("pinned_written", cell_sort.clone());
    let first = terms.mk_app(
        Symbol::named("store"),
        [base, indices[0], cells[0]],
        array_sort.clone(),
    );
    let duplicate = terms.mk_app(
        Symbol::named("store"),
        [base, index, written],
        array_sort.clone(),
    );
    let newest = terms.mk_app(
        Symbol::named("store"),
        [first, indices[0], cells[1]],
        array_sort.clone(),
    );
    let reads = [first, newest, alias].map(|array| {
        terms.mk_app(
            Symbol::named("select"),
            [array, indices[0]],
            cell_sort.clone(),
        )
    });
    let default = terms.mk_app(Symbol::named("default"), [base], cell_sort);
    let constant = terms.mk_app(Symbol::named("const-array"), [cells[0]], array_sort);
    let bindings = [
        (index, indices[0]),
        (written, cells[0]),
        (alias, newest),
        (reads[0], cells[0]),
        (reads[1], cells[1]),
        (reads[2], cells[1]),
        (default, cells[0]),
    ];
    let mut roots = vec![
        first, duplicate, newest, reads[0], reads[1], reads[2], default, constant,
    ];
    let assignments = bind(&mut terms, &bindings, &mut roots);
    let false_value = terms.mk_bool(false);
    roots.push(false_value);
    StoreFixture {
        terms,
        roots,
        assignments,
        stores: [first, duplicate, newest],
        reads,
        index,
        written,
    }
}

fn bind(
    terms: &mut TermStore,
    pairs: &[(TermId, TermId)],
    roots: &mut Vec<TermId>,
) -> Vec<(TermId, bool)> {
    let mut assignments = Vec::new();
    for &(left, right) in pairs {
        let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
        roots.push(equality);
        assignments.push((equality, true));
        if matches!(terms.sort(left), Sort::Bool) {
            if let TermData::Const(Constant::Bool(value)) = terms.get(right) {
                assignments.push((left, *value));
            }
        }
    }
    assignments
}

fn legacy(source: &mut EufSolver<'_>, roots: &[TermId]) -> EufModel {
    source.scope_model_to_roots(roots);
    source.extract_model()
}

fn refuse_arena(terms: &TermStore) {
    // Malformed raw graph preparation is intentionally not run through the
    // legacy solver; validate its paid whole-arena kernel before graph lookup.
    let source = EufSolver::new(terms);
    let mut poll = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(100_000_000, &mut poll);
    assert!(matches!(
        shape::arena(&source, &mut work),
        Err(QueryError::Exhausted)
    ));
    assert!(matches!(work.charge(0), Err(QueryError::Exhausted)));
}
