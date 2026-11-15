// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod fixtures;
use fixtures::*;

#[test]
fn original_two_root_bv129_reads_recover_distinct_high_bits_before_validation() {
    let mut f = Fixture::new();
    let h = f.terms.mk_var("h", Sort::Bool);
    let b = f.terms.mk_var("b", f.array_sort());
    let y = f.terms.mk_var("y", Sort::bitvec(129));
    let other_value = f.terms.mk_ite_raw(h, f.high, f.next);
    let other_store = f.store(f.base, f.key, other_value);
    let other_read = f.read(b, f.key);
    let query_eq = f.terms.mk_app(Symbol::named("="), [f.out, y], Sort::Bool);
    let query = f.terms.mk_not_raw(query_eq);
    let reads = [f.read, other_read];
    let definitions = [
        (f.out, f.read),
        (y, other_read),
        (f.array, f.store),
        (b, other_store),
    ];
    let mut model = model();
    model.bool_overrides.extend([(f.guard, true), (h, false)]);
    for read in reads {
        model.values.insert(read, BigInt::from(0u8));
    }
    Executor::recover_substituted_bv_bool_values(&f.terms, &definitions, &mut model);
    let high: BigInt = BigInt::from(1u8) << 128usize;
    assert_eq!(model.values.get(&f.out), Some(&high));
    assert_eq!(model.values.get(&y), Some(&(&high + 1)));
    for (read, output) in [(f.read, f.out), (other_read, y)] {
        assert_eq!(model.values.get(&read), model.values.get(&output));
    }
    assert_eq!(
        ay_bv::evaluate_bv_assertion(&f.terms, query, &model),
        Some(true)
    );

    let source_a = f
        .terms
        .mk_app(Symbol::named("="), [f.array, f.store], Sort::Bool);
    let source_b = f
        .terms
        .mk_app(Symbol::named("="), [b, other_store], Sort::Bool);
    let source = [source_a, source_b, query];
    assert!(ay_bv::validate_bv_assertions(&f.terms, &source, &model).is_ok());
    let mut arrays = Executor::extract_array_model_from_bv_model(
        &f.terms,
        &model,
        &source,
        &definitions.iter().map(|&(from, _)| from).collect(),
    );
    Executor::populate_array_models_from_substitutions(&f.terms, &model, &definitions, &mut arrays);
    for (array, expected) in [(f.array, high.clone()), (b, &high + 1)] {
        assert!(!arrays.is_withheld(&array));
        let interp = &arrays.array_values[&array];
        assert_eq!(
            interp.default.as_deref(),
            Some(format_bitvec(&BigInt::from(0u8), 129).as_str())
        );
        assert_eq!(lookup(interp, "#x07"), format_bitvec(&expected, 129));
    }
}

#[test]
fn array_alias_expansion_schedules_scalar_guard_key_and_payload_dependencies() {
    let mut f = Fixture::new();
    let alias = f.terms.mk_var("alias", f.array_sort());
    let key = f.terms.mk_var("key", Sort::bitvec(8));
    let payload = f.terms.mk_var("payload", Sort::bitvec(129));
    let value = f.terms.mk_ite_raw(f.guard, payload, f.next);
    let store = f.store(f.base, key, value);
    let truth = f.terms.true_term();
    let mut substitutions = vec![
        (f.out, f.read),
        (f.array, alias),
        (alias, store),
        (f.guard, truth),
        (key, f.key),
        (payload, f.high),
    ];
    for _ in 0..2 {
        let mut bits = model();
        bits.values.extend([
            (f.read, BigInt::from(0u8)),
            (key, BigInt::from(99u8)),
            (payload, BigInt::from(0u8)),
        ]);
        bits.bool_overrides.insert(f.guard, false);
        Executor::recover_substituted_bv_bool_values(&f.terms, &substitutions, &mut bits);
        assert_eq!(bits.values.get(&f.out), Some(&(BigInt::from(1u8) << 128)));
        assert_eq!(bits.bool_overrides.get(&f.guard), Some(&true));
        substitutions.reverse();
    }
}

#[test]
fn unknown_overlapping_store_key_and_malformed_definition_never_use_old_read_bits() {
    for change in 0..5 {
        let mut f = Fixture::new();
        let unknown = f.terms.mk_var("unknown_key", Sort::bitvec(8));
        let mut args = vec![f.base, f.key, f.high];
        let mut symbol = Symbol::named("store");
        match change {
            0 => args[1] = unknown,
            1 => args[1] = f.terms.true_term(),
            2 => args[2] = f.terms.true_term(),
            3 => symbol = Symbol::indexed("store", vec![1]),
            4 => {
                args.pop();
            }
            _ => unreachable!(),
        }
        let definition = f.terms.mk_app(symbol, args, f.array_sort());
        let defs = [(f.array, definition)].into_iter().collect();
        let mut recovery = Recovery::new(&f.terms, &defs);
        let plan = recovery
            .plan(f.read, &mut HashSet::default())
            .expect("closed syntax census");
        let mut bits = model();
        bits.values.insert(f.read, BigInt::from(2u8));
        let mut memo = BvEvalMemo::default();
        assert!(recovery
            .seed(&plan, &mut bits, &mut memo, &defs.keys().copied().collect())
            .is_none());
        assert!(!memo.bv.contains_key(&f.read));
        assert_eq!(bits.values.get(&f.read), Some(&BigInt::from(2u8)));
    }
}

#[test]
fn free_base_alias_requires_one_consistent_existing_semantic_index_value() {
    for mode in 0..3 {
        let mut f = Fixture::new();
        let free = f.terms.mk_var("free", f.array_sort());
        let zero = f.terms.mk_bitvec(BigInt::from(0u8), 8);
        let added = f
            .terms
            .mk_app(Symbol::named("bvadd"), [f.key, zero], Sort::bitvec(8));
        let first = f.read(free, f.key);
        let second = f.read(free, added);
        let mut bits = model();
        bits.values.insert(f.read, BigInt::from(0u8));
        if mode != 2 {
            bits.values.insert(first, BigInt::from(9u8));
        }
        if mode == 1 {
            bits.values.insert(second, BigInt::from(10u8));
        }
        Executor::recover_substituted_bv_bool_values(
            &f.terms,
            &[(f.out, f.read), (f.array, free)],
            &mut bits,
        );
        if mode == 0 {
            assert_eq!(bits.values.get(&f.out), Some(&BigInt::from(9u8)));
        } else {
            assert!(!bits.values.contains_key(&f.out));
        }
    }
}

#[test]
fn bool_reads_publish_the_same_exact_definition_value_as_the_recovered_variable() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(8), Sort::Bool);
    let base = terms.mk_app(
        Symbol::named("const-array"),
        [terms.false_term()],
        sort.clone(),
    );
    let array = terms.mk_var("array", sort.clone());
    let output = terms.mk_var("output", Sort::Bool);
    let key = terms.mk_bitvec(BigInt::from(7u8), 8);
    let store = terms.mk_app(Symbol::named("store"), [base, key, terms.true_term()], sort);
    let read = terms.mk_app(Symbol::named("select"), [array, key], Sort::Bool);
    let mut bits = model();
    bits.bool_overrides.insert(read, false);
    Executor::recover_substituted_bv_bool_values(
        &terms,
        &[(output, read), (array, store)],
        &mut bits,
    );
    assert_eq!(bits.bool_overrides.get(&read), Some(&true));
    assert_eq!(bits.bool_overrides.get(&output), Some(&true));
}

#[test]
fn known_miss_can_resolve_a_read_without_pretending_the_whole_array_is_complete() {
    let mut f = Fixture::new();
    let unknown = f.terms.mk_var("unknown_value", Sort::bitvec(129));
    let other_key = f.terms.mk_bitvec(BigInt::from(8u8), 8);
    let store = f.store(f.base, other_key, unknown);
    let defs = [(f.array, store)].into_iter().collect();
    let mut recovery = Recovery::new(&f.terms, &defs);
    let plan = recovery.plan(f.read, &mut HashSet::default()).unwrap();
    let mut bits = model();
    recovery
        .seed(
            &plan,
            &mut bits,
            &mut BvEvalMemo::default(),
            &defs.keys().copied().collect(),
        )
        .unwrap();
    assert_eq!(bits.values.get(&f.read), Some(&BigInt::from(0u8)));
    assert!(
        Executor::build_store_chain_interp(&f.terms, &bits, store, &mut ArrayModel::default())
            .is_none()
    );
}

#[test]
fn cache_scope_is_refreshed_before_correcting_stale_compound_read_entries() {
    let mut f = Fixture::new();
    let one = f.terms.mk_bitvec(BigInt::from(1u8), 129);
    let add = f
        .terms
        .mk_app(Symbol::named("bvadd"), [f.read, one], Sort::bitvec(129));
    let defs = [(f.array, f.store)].into_iter().collect();
    let mut recovery = Recovery::new(&f.terms, &defs);
    let plan = recovery.plan(add, &mut HashSet::default()).unwrap();
    let mut bits = model();
    bits.bool_overrides.insert(f.guard, true);
    bits.values.insert(f.read, BigInt::from(0u8));
    let mut memo = BvEvalMemo::default();
    memo.bv
        .extend([(f.read, BigInt::from(0u8)), (add, BigInt::from(1u8))]);
    recovery
        .seed(&plan, &mut bits, &mut memo, &defs.keys().copied().collect())
        .unwrap();
    assert_eq!(
        Executor::evaluate_bv_expr_with_bools(
            &f.terms,
            add,
            &bits.values,
            &bits.bool_overrides,
            &mut memo
        ),
        Some((BigInt::from(1u8) << 128) + 1)
    );
}

#[test]
fn cyclic_wrong_sort_dead_definitions_and_shared_budget_refuse_without_retry_refunds() {
    let mut f = Fixture::new();
    let alias = f.terms.mk_var("alias", f.array_sort());
    for defs in [
        vec![(f.array, alias), (alias, f.array)],
        vec![(f.array, f.high)],
        vec![(f.array, TermId(u32::MAX))],
    ] {
        let defs = defs.into_iter().collect();
        let mut recovery = Recovery::new(&f.terms, &defs);
        assert!(recovery.plan(f.read, &mut HashSet::default()).is_none());
    }
    let defs = [(f.array, f.store)].into_iter().collect();
    let mut measured = Recovery::new(&f.terms, &defs);
    measured.plan(f.read, &mut HashSet::default()).unwrap();
    let used = MAX_WORK - measured.remaining;
    assert!(used > 1);
    for allowance in [used - 1, used] {
        let mut recovery = Recovery::new(&f.terms, &defs);
        recovery.remaining = allowance;
        let result = recovery.plan(f.read, &mut HashSet::default());
        assert_eq!(result.is_some(), allowance == used);
        if result.is_none() {
            assert_eq!(recovery.remaining, 0);
            assert!(recovery.plan(f.read, &mut HashSet::default()).is_none());
        }
    }
    let mut measured = Recovery::new(&f.terms, &defs);
    let plan = measured.plan(f.read, &mut HashSet::default()).unwrap();
    let mut bits = model();
    bits.bool_overrides.insert(f.guard, true);
    measured
        .seed(
            &plan,
            &mut bits,
            &mut BvEvalMemo::default(),
            &HashSet::default(),
        )
        .unwrap();
    let total = MAX_WORK - measured.remaining;
    assert!(total > used);
    for allowance in [total - 1, total] {
        let mut recovery = Recovery::new(&f.terms, &defs);
        recovery.remaining = allowance;
        let plan = recovery.plan(f.read, &mut HashSet::default()).unwrap();
        let mut bits = model();
        bits.bool_overrides.insert(f.guard, true);
        let result = recovery.seed(
            &plan,
            &mut bits,
            &mut BvEvalMemo::default(),
            &HashSet::default(),
        );
        assert_eq!(result.is_some(), allowance == total);
        assert_eq!(bits.values.contains_key(&f.read), allowance == total);
    }
}

#[test]
fn array_definition_aliases_share_the_same_exact_full_syntax_depth_bound() {
    for aliases in [495, 496] {
        let mut f = Fixture::new();
        let mut defs = HashMap::default();
        let mut definition = f.store;
        for index in 0..aliases {
            let alias = f.terms.mk_var(format!("alias_{index}"), f.array_sort());
            defs.insert(alias, definition);
            definition = alias;
        }
        defs.insert(f.array, definition);
        let mut recovery = Recovery::new(&f.terms, &defs);
        let plan = recovery.plan(f.read, &mut HashSet::default());
        // read depth0, a depth1, aliases, store, ITE and leaf: the
        // 495-alias deepest leaf is499; 496 aliases reach forbidden500.
        assert_eq!(plan.is_some(), aliases == 495);
        if let Some(plan) = plan {
            let mut bits = model();
            bits.bool_overrides.insert(f.guard, true);
            recovery
                .seed(
                    &plan,
                    &mut bits,
                    &mut BvEvalMemo::default(),
                    &HashSet::default(),
                )
                .unwrap();
            assert_eq!(
                bits.values.get(&f.read),
                Some(&(BigInt::from(1u8) << 128usize))
            );
        }
    }
}
