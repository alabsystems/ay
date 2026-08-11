// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::alias_index::AuthoredIndex;
use super::alias_select::{
    add_array_alias_support, add_select_congruence, add_transitivity, ArrayBindingSupport,
};
use super::*;

const MAX_SCALAR_ALIAS_WORK: usize = 512;

struct ScalarConflict {
    root: TermId,
    equality: TermId,
    left: TermId,
    right: TermId,
}

#[derive(Clone, Copy)]
struct SelectBinding {
    root: TermId,
    select: TermId,
    array: TermId,
    index: TermId,
}

struct ReadPairSearch<'a> {
    authored: &'a [TermId],
    authored_index: &'a AuthoredIndex,
    conflict: &'a ScalarConflict,
    left_reads: &'a [SelectBinding],
    right_reads: &'a [SelectBinding],
}

pub(super) fn try_reconstruct(
    exec: &mut Executor,
    proof: &mut Proof,
    authored: &[TermId],
    authored_index: &AuthoredIndex,
) -> bool {
    let mut work = 0_usize;
    for &root in authored {
        let Some(conflict) = decode_scalar_conflict(&exec.ctx.terms, root) else {
            continue;
        };
        let Some(left_reads) =
            select_bindings(&exec.ctx.terms, authored_index, conflict.left, &mut work)
        else {
            if work > MAX_SCALAR_ALIAS_WORK {
                return false;
            }
            continue;
        };
        let Some(right_reads) =
            select_bindings(&exec.ctx.terms, authored_index, conflict.right, &mut work)
        else {
            if work > MAX_SCALAR_ALIAS_WORK {
                return false;
            }
            continue;
        };
        let search = ReadPairSearch {
            authored,
            authored_index,
            conflict: &conflict,
            left_reads: &left_reads,
            right_reads: &right_reads,
        };
        if try_read_pairs(exec, proof, &search, &mut work) {
            return true;
        }
        if work > MAX_SCALAR_ALIAS_WORK {
            return false;
        }
    }
    false
}

fn decode_scalar_conflict(terms: &TermStore, root: TermId) -> Option<ScalarConflict> {
    let TermData::Not(equality) = terms.get(root) else {
        return None;
    };
    let equality = *equality;
    let (left, right) = decode_eq_local(terms, equality)?;
    if left == right
        || terms.sort(left) != terms.sort(right)
        || matches!(terms.sort(left), Sort::Array(_))
    {
        return None;
    }
    Some(ScalarConflict {
        root,
        equality,
        left,
        right,
    })
}

fn well_sorted_select(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if name != "select" || args.len() != 2 {
        return None;
    }
    let (array, index) = (args[0], args[1]);
    let Sort::Array(array_sort) = terms.sort(array) else {
        return None;
    };
    (terms.sort(index) == &array_sort.index_sort && terms.sort(term) == &array_sort.element_sort)
        .then_some((array, index))
}

fn select_bindings(
    terms: &TermStore,
    authored_index: &AuthoredIndex,
    scalar: TermId,
    work: &mut usize,
) -> Option<Vec<SelectBinding>> {
    let mut selected = Vec::new();
    for &(root, target) in authored_index.scalar_bindings(scalar)? {
        charge_work(work)?;
        let Some((array, index)) = well_sorted_select(terms, target) else {
            continue;
        };
        selected.push(SelectBinding {
            root,
            select: target,
            array,
            index,
        });
    }
    Some(selected)
}

fn charge_work(work: &mut usize) -> Option<()> {
    *work = (*work).saturating_add(1);
    (*work <= MAX_SCALAR_ALIAS_WORK).then_some(())
}

fn try_read_pairs(
    exec: &mut Executor,
    proof: &mut Proof,
    search: &ReadPairSearch<'_>,
    work: &mut usize,
) -> bool {
    for &left_read in search.left_reads {
        for &right_read in search.right_reads {
            if charge_work(work).is_none() {
                return false;
            }
            if left_read.root == right_read.root
                || left_read.index != right_read.index
                || left_read.array == right_read.array
            {
                continue;
            }
            let (Some(left_arrays), Some(right_arrays)) = (
                search.authored_index.array_bindings(left_read.array),
                search.authored_index.array_bindings(right_read.array),
            ) else {
                continue;
            };
            for &left_array in left_arrays {
                for &right_array in right_arrays {
                    if charge_work(work).is_none() {
                        return false;
                    }
                    if left_array.0 == right_array.0 {
                        continue;
                    }
                    let Some(candidate) = build_candidate(
                        exec,
                        search.authored_index,
                        search.conflict,
                        [left_read, right_read],
                        [left_array, right_array],
                    ) else {
                        continue;
                    };
                    if exec.commit_if_strictly_checked(proof, candidate, search.authored) {
                        return true;
                    }
                }
            }
        }
    }
    false
}

fn build_candidate(
    exec: &mut Executor,
    authored_index: &AuthoredIndex,
    conflict: &ScalarConflict,
    reads: [SelectBinding; 2],
    arrays: [(TermId, TermId); 2],
) -> Option<Proof> {
    let mut candidate = Proof::new();
    let array_assumes = [
        candidate.add_assume(arrays[0].0, None),
        candidate.add_assume(arrays[1].0, None),
    ];
    let scalar_assumes = [
        candidate.add_assume(reads[0].root, None),
        candidate.add_assume(reads[1].root, None),
    ];
    let conflict_assume = candidate.add_assume(conflict.root, None);
    let (array_equality, array_support) = add_array_alias_support(
        exec,
        &mut candidate,
        authored_index,
        (reads[0].array, reads[1].array),
        [
            ArrayBindingSupport {
                root: arrays[0].0,
                chain: arrays[0].1,
                assume: array_assumes[0],
            },
            ArrayBindingSupport {
                root: arrays[1].0,
                chain: arrays[1].1,
                assume: array_assumes[1],
            },
        ],
    )?;
    let select_equality = exec.ctx.terms.mk_app(
        Symbol::named("="),
        [reads[0].select, reads[1].select],
        Sort::Bool,
    );
    let select_support = add_select_congruence(
        exec,
        &mut candidate,
        array_equality,
        array_support,
        select_equality,
    )?;
    let supports = [
        (reads[0].root, scalar_assumes[0]),
        (select_equality, select_support),
        (reads[1].root, scalar_assumes[1]),
    ];
    let scalar_support = add_transitivity(
        &mut exec.ctx.terms,
        &mut candidate,
        conflict.equality,
        &supports,
    )?;
    candidate.add_resolution(
        Vec::new(),
        conflict.equality,
        scalar_support,
        conflict_assume,
    );
    Some(candidate)
}
