// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::*;

fn app(terms: &mut TermStore, op: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(op), args, sort)
}

fn contradiction(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    let equality = app(terms, "=", &[left, right], Sort::Bool);
    terms.mk_not_raw(equality)
}

fn fixture(width: u32) -> (TermStore, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let key = terms.mk_var("base", Sort::bitvec(width));
    let x = terms.mk_var("x", Sort::bitvec(8));
    let array = app(
        &mut terms,
        "const-array",
        &[x],
        Sort::array(Sort::bitvec(width), Sort::bitvec(8)),
    );
    (terms, array, key, x)
}

#[test]
fn sparse_array_modular_wraparound_and_last_write_are_exact() {
    for width in [9, 64, 128] {
        let (mut terms, array, base, x) = fixture(width);
        let sort = terms.sort(array).clone();
        let y = terms.mk_var("y", Sort::bitvec(8));
        let last = terms.mk_bitvec((num_bigint::BigInt::from(1) << width) - 1, width);
        let one = terms.mk_bitvec(1.into(), width);
        let before = app(&mut terms, "bvadd", &[base, last], Sort::bitvec(width));
        let wrapped = app(&mut terms, "bvadd", &[one, before], Sort::bitvec(width));
        let different = app(&mut terms, "bvadd", &[base, one], Sort::bitvec(width));
        let array = app(&mut terms, "store", &[array, base, x], sort.clone());
        let array = app(&mut terms, "store", &[array, wrapped, y], sort.clone());
        let array = app(&mut terms, "store", &[array, different, x], sort);
        let read = app(&mut terms, "select", &[array, base], Sort::bitvec(8));
        let root = contradiction(&mut terms, read, y);
        let evidence =
            authenticate_bool_bv_unsat_query(&terms, &[root], None).expect("exact wrapped read");
        assert!(evidence.is_current_for(&terms, &[root]));
        assert!(
            !evidence.used_exact_finite_arrays(),
            "no full-domain enumeration"
        );
        let wrong = contradiction(&mut terms, read, x);
        assert!(authenticate_bool_bv_unsat_query(&terms, &[wrong], None).is_err());
    }
}

#[test]
fn sparse_array_symbolic_aliases_require_both_branches() {
    let (mut terms, array, i, x) = fixture(9);
    let j = terms.mk_var("other", Sort::bitvec(9));
    let y = terms.mk_var("y", Sort::bitvec(8));
    let sort = terms.sort(array).clone();
    let written = app(&mut terms, "store", &[array, j, y], sort);
    let read = app(&mut terms, "select", &[written, i], Sort::bitvec(8));
    let aliases = app(&mut terms, "=", &[i, j], Sort::Bool);
    let expected = terms.mk_ite_raw(aliases, y, x);
    let root = contradiction(&mut terms, read, expected);
    authenticate_bool_bv_unsat_query(&terms, &[root], None).expect("exact alias mux");
    let wrong = contradiction(&mut terms, read, x);
    assert!(authenticate_bool_bv_unsat_query(&terms, &[wrong], None).is_err());
}

#[test]
fn sparse_array_validates_overwritten_values_and_unsupported_base() {
    for bad_base in [false, true] {
        let (mut terms, array, key, x) = fixture(64);
        let sort = terms.sort(array).clone();
        let bad = if bad_base {
            app(&mut terms, "unsupported-array-node", &[], sort.clone())
        } else {
            let malformed = app(&mut terms, "bvadd", &[x], Sort::bitvec(8));
            app(&mut terms, "store", &[array, key, malformed], sort.clone())
        };
        let overwritten = app(&mut terms, "store", &[bad, key, x], sort);
        let read = app(&mut terms, "select", &[overwritten, key], Sort::bitvec(8));
        let root = contradiction(&mut terms, read, x);
        assert!(
            authenticate_bool_bv_unsat_query(&terms, &[root], None).is_err(),
            "no validation through discarded children"
        );
    }
}

#[test]
fn sparse_array_store_budget_and_cancellation_refuse() {
    let (mut terms, mut array, key, x) = fixture(64);
    let sort = terms.sort(array).clone();
    for _ in 0..65 {
        array = app(&mut terms, "store", &[array, key, x], sort.clone());
    }
    let read = app(&mut terms, "select", &[array, key], Sort::bitvec(8));
    let root = contradiction(&mut terms, read, x);
    let error = authenticate_bool_bv_unsat_query(&terms, &[root], None).expect_err("store limit");
    assert!(matches!(
        error,
        BoolBvUnsatAuthenticationError::ResourceLimit { .. }
    ));
    let mut polls = 0;
    let mut progress = || {
        polls += 1;
        polls < 12
    };
    let mut lowerer = ProofProducingLowerer::new(&terms, Instant::now() + Duration::from_secs(3));
    lowerer.keep_going = Some(&mut progress);
    assert!(lowerer.lower(root).is_err());
    assert!(lowerer.cancelled);
}

#[test]
fn source_bound_array_reads_keep_the_arbitrary_base_and_last_write() {
    for width in [9, 64, 128] {
        let (mut terms, _, key, value) = fixture(width);
        let sort = Sort::array(Sort::bitvec(width), Sort::bitvec(8));
        let base = terms.mk_var("initial_memory", sort.clone());
        let store = app(&mut terms, "store", &[base, key, value], sort);
        let read = app(&mut terms, "select", &[store, key], Sort::bitvec(8));
        let root = contradiction(&mut terms, read, value);
        let proof = authenticate_bool_bv_unsat_query(&terms, &[root], None).unwrap();
        assert!(proof.used_uninterpreted_leaves());
        let wrong = terms.mk_var("wrong_value", Sort::bitvec(8));
        let mutation = contradiction(&mut terms, read, wrong);
        assert!(matches!(
            authenticate_bool_bv_unsat_query(&terms, &[mutation], None),
            Err(BoolBvUnsatAuthenticationError::UnsupportedFragment { .. })
        ));
    }
}

#[test]
fn source_bound_array_satisfiable_abstraction_is_not_a_source_sat_verdict() {
    let (mut terms, _, key, _) = fixture(64);
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let base = terms.mk_var("initial_memory", sort);
    let alias = terms.mk_var("other_index", Sort::bitvec(64));
    let left = app(&mut terms, "select", &[base, key], Sort::bitvec(8));
    let right = app(&mut terms, "select", &[base, alias], Sort::bitvec(8));
    // Different indices can read different bytes. Keep SAT abstractions
    // inconclusive rather than surfacing their assignments as source models.
    let root = contradiction(&mut terms, left, right);
    assert!(matches!(
        authenticate_bool_bv_unsat_query(&terms, &[root], None),
        Err(BoolBvUnsatAuthenticationError::UnsupportedFragment { .. })
    ));
}

#[test]
fn calling_frame_store_capacity_preserves_subtracted_addresses_and_last_write() {
    for width in [9, 64, 128] {
        for count in [33, 40, 48, 64] {
            let (mut terms, mut array, base, x) = fixture(width);
            let sort = terms.sort(array).clone();
            let y = terms.mk_var("last_value", Sort::bitvec(8));
            for offset in 0..count {
                let literal = terms.mk_bitvec(offset.into(), width);
                let key = app(&mut terms, "bvadd", &[base, literal], Sort::bitvec(width));
                let value = if offset == count - 1 { y } else { x };
                array = app(&mut terms, "store", &[array, key, value], sort.clone());
            }
            let displacement = terms.mk_bitvec(32.into(), width);
            let frame = app(
                &mut terms,
                "bvsub",
                &[base, displacement],
                Sort::bitvec(width),
            );
            let last = terms.mk_bitvec((count + 31).into(), width);
            let alias = app(&mut terms, "bvadd", &[frame, last], Sort::bitvec(width));
            let read = app(&mut terms, "select", &[array, alias], Sort::bitvec(8));
            let root = contradiction(&mut terms, read, y);
            let evidence = authenticate_bool_bv_unsat_query(&terms, &[root], None)
                .unwrap_or_else(|error| panic!("width={width}, writes={count}: {error:?}"));
            assert!(evidence.is_current_for(&terms, &[root]));
            let wrong = contradiction(&mut terms, read, x);
            assert!(authenticate_bool_bv_unsat_query(&terms, &[wrong], None).is_err());
        }
    }
}

#[test]
fn source_bound_array_read_congruence_uses_the_same_array_and_index_premise() {
    for width in [9, 64, 128] {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::bitvec(width), Sort::bitvec(8));
        let array = terms.mk_var("memory", sort.clone());
        let other = terms.mk_var("other_memory", sort);
        let i = terms.mk_var("i", Sort::bitvec(width));
        let j = terms.mk_var("j", Sort::bitvec(width));
        let left = app(&mut terms, "select", &[array, i], Sort::bitvec(8));
        let right = app(&mut terms, "select", &[array, j], Sort::bitvec(8));
        let indices_equal = app(&mut terms, "=", &[i, j], Sort::Bool);
        let values_differ = contradiction(&mut terms, left, right);
        let root = app(
            &mut terms,
            "and",
            &[indices_equal, values_differ],
            Sort::Bool,
        );
        let evidence = authenticate_bool_bv_unsat_query(&terms, &[root], None)
            .expect("equal indices of one array must have equal values");
        assert!(evidence.is_current_for(&terms, &[root]));
        assert!(!evidence.used_exact_finite_arrays());
        let foreign = app(&mut terms, "select", &[other, j], Sort::bitvec(8));
        let wrong = contradiction(&mut terms, left, foreign);
        let mutant = app(&mut terms, "and", &[indices_equal, wrong], Sort::Bool);
        assert!(
            authenticate_bool_bv_unsat_query(&terms, &[mutant], None).is_err(),
            "distinct arrays must not acquire a shared-value premise"
        );
        assert!(
            authenticate_bool_bv_unsat_query(&terms, &[values_differ], None).is_err(),
            "dropping the index-equality premise must retain a satisfiable choice"
        );
    }
}

#[test]
fn source_bound_array_read_congruence_clause_requires_both_premises() {
    for width in [9, 64, 128] {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::bitvec(width), Sort::bitvec(8));
        let array = terms.mk_var("memory", sort.clone());
        let other = terms.mk_var("other_memory", sort);
        let i = terms.mk_var("i", Sort::bitvec(width));
        let j = terms.mk_var("j", Sort::bitvec(width));
        let left = app(&mut terms, "select", &[array, i], Sort::bitvec(8));
        let right = app(&mut terms, "select", &[array, j], Sort::bitvec(8));
        let foreign = app(&mut terms, "select", &[other, j], Sort::bitvec(8));
        let indices_differ = contradiction(&mut terms, i, j);
        let values_equal = app(&mut terms, "=", &[left, right], Sort::Bool);
        let foreign_equal = app(&mut terms, "=", &[left, foreign], Sort::Bool);
        assert!(
            recognize_bv_bitblast(&terms, &[indices_differ, values_equal]),
            "array functionality is a valid clause at width {width}"
        );
        assert!(
            !recognize_bv_bitblast(&terms, &[values_equal]),
            "distinct indices may have distinct values"
        );
        assert!(
            !recognize_bv_bitblast(&terms, &[indices_differ, foreign_equal]),
            "equal indices do not equate reads from distinct arrays"
        );
    }
}

#[test]
fn source_bound_array_read_congruence_keeps_modular_offset_guards_exact() {
    for width in [9, 64, 128] {
        let mut terms = TermStore::new();
        let array = terms.mk_var("memory", Sort::array(Sort::bitvec(width), Sort::bitvec(8)));
        let i = terms.mk_var("i", Sort::bitvec(width));
        let j = terms.mk_var("j", Sort::bitvec(width));
        let equal = app(&mut terms, "=", &[i, j], Sort::Bool);
        let mut differences = Vec::new();
        for offset in [1, 7, 17] {
            let constant = terms.mk_bitvec(offset.into(), width);
            let a = app(&mut terms, "bvadd", &[i, constant], Sort::bitvec(width));
            let b = app(&mut terms, "bvadd", &[j, constant], Sort::bitvec(width));
            let left = app(&mut terms, "select", &[array, a], Sort::bitvec(8));
            let right = app(&mut terms, "select", &[array, b], Sort::bitvec(8));
            differences.push(contradiction(&mut terms, left, right));
        }
        let different = app(&mut terms, "or", &differences, Sort::Bool);
        let root = app(&mut terms, "and", &[equal, different], Sort::Bool);
        authenticate_bool_bv_unsat_query(&terms, &[root], None)
            .expect("equal bases preserve every equal offset, including modular wraparound");
        assert!(
            authenticate_bool_bv_unsat_query(&terms, &[different], None).is_err(),
            "offset sharing cannot invent equality between independent bases"
        );
    }
}

#[test]
fn source_bound_array_read_congruence_proves_zero_offset_alias() {
    let mut terms = TermStore::new();
    let array = terms.mk_var("memory", Sort::array(Sort::bitvec(64), Sort::bitvec(8)));
    let i = terms.mk_var("i", Sort::bitvec(64));
    let zero = terms.mk_bitvec(0.into(), 64);
    let alias = app(&mut terms, "bvadd", &[i, zero], Sort::bitvec(64));
    let left = app(&mut terms, "select", &[array, i], Sort::bitvec(8));
    let right = app(&mut terms, "select", &[array, alias], Sort::bitvec(8));
    let root = contradiction(&mut terms, left, right);
    authenticate_bool_bv_unsat_query(&terms, &[root], None)
        .expect("syntactic index spelling cannot remove array functionality");
}

#[test]
fn sparse_consistency_builders_run_only_after_existing_admission() {
    use std::cell::Cell;
    let terms = TermStore::new();
    let deadline = || Instant::now() + Duration::from_secs(30);
    let left = BvExpr::add(BvExpr::leaf("left", 64), BvExpr::const_val(1, 64));
    let right = BvExpr::add(BvExpr::leaf("right", 64), BvExpr::const_val(2, 64));
    let value = || {
        BvExpr::eq(
            BvExpr::leaf("value_left", 8),
            BvExpr::leaf("value_right", 8),
        )
    };
    // This is the actual fallback constraint shape. The marker is inside
    // the same builder that performs the recursive index clones.
    let built = Cell::new(false);
    let build = || {
        built.set(true);
        BvExpr::or(
            BvExpr::not(BvExpr::eq(left.clone(), right.clone())),
            value(),
        )
    };
    let mut lowerer = ProofProducingLowerer::new(&terms, deadline());
    let nodes = lowerer
        .count_bv_nodes(&left)
        .unwrap()
        .saturating_add(lowerer.count_bv_nodes(&right).unwrap())
        .saturating_add(6);
    let limit = super::super::MAX_PROOF_PRODUCING_CONSTRUCTED_EXPR_NODES;
    lowerer.constructed_expr_nodes = limit - nodes + 1;
    let before = lowerer.constructed_expr_nodes;
    let mut constraints = Vec::new();
    assert!(lowerer
        .push_sparse_read_constraint(&mut constraints, nodes, &build)
        .is_err());
    assert!(
        !built.get(),
        "exhaustion must precede both recursive clones"
    );
    assert!(constraints.is_empty() && lowerer.resource_exhausted);
    assert_eq!(lowerer.constructed_expr_nodes, before, "no reset or refund");

    let mut oversized = ProofProducingLowerer::new(&terms, deadline());
    assert!(oversized
        .push_sparse_read_constraint(&mut constraints, usize::MAX, &build)
        .is_err());
    assert!(!built.get() && constraints.is_empty() && oversized.resource_exhausted);

    let mut exact = ProofProducingLowerer::new(&terms, deadline());
    exact.constructed_expr_nodes = limit - nodes;
    exact
        .push_sparse_read_constraint(&mut constraints, nodes, &build)
        .unwrap();
    assert!(built.get() && constraints.len() == 1);
    assert_eq!(exact.constructed_expr_nodes, limit);
    assert_eq!(exact.count_bv_nodes(&constraints[0]).unwrap(), nodes);

    built.set(false);
    let mut stop = || false;
    let mut cancelled = ProofProducingLowerer::new(&terms, deadline());
    cancelled.keep_going = Some(&mut stop);
    let mut withheld = Vec::new();
    assert!(cancelled
        .push_sparse_read_constraint(&mut withheld, nodes, &build)
        .is_err());
    assert!(!built.get() && withheld.is_empty() && cancelled.cancelled);
    assert!(
        !cancelled.resource_exhausted,
        "cancellation is not cap exhaustion"
    );
    assert_eq!(cancelled.constructed_expr_nodes, 0);
}
