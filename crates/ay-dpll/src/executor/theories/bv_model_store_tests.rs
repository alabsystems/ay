// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Data-only recovery tests. Reconstructed arrays are candidates, not SAT seals.

use super::*;
use ay_core::term::Symbol;

fn bv(terms: &mut TermStore, value: u32) -> TermId {
    terms.mk_bitvec(BigInt::from(value), 8)
}

fn constant(terms: &mut TermStore, value: TermId) -> TermId {
    terms.mk_app(
        Symbol::named("const-array"),
        vec![value],
        Sort::array(Sort::bitvec(8), terms.sort(value).clone()),
    )
}

fn raw_store(terms: &mut TermStore, base: TermId, index: TermId, value: TermId) -> TermId {
    // Recovery must see every authored store, including shadowed and no-op
    // writes that the normal builder would simplify out of these controls.
    terms.mk_app(
        Symbol::named("store"),
        vec![base, index, value],
        terms.sort(base).clone(),
    )
}

fn model() -> BvModel {
    BvModel {
        values: HashMap::default(),
        bool_overrides: HashMap::default(),
        term_to_bits: HashMap::default(),
    }
}

fn lookup<'a>(interp: &'a ArrayInterpretation, index: &str) -> &'a str {
    interp
        .stores
        .iter()
        .find(|(key, _)| key == index)
        .map(|(_, value)| value.as_str())
        .or(interp.default.as_deref())
        .expect("complete interpretation")
}

#[test]
fn recovered_boolean_guards_drive_both_callers_not_stale_compound_bits() {
    let mut terms = TermStore::new();
    let guard = terms.mk_var("g", Sort::Bool);
    let one = bv(&mut terms, 1);
    let two = bv(&mut terms, 2);
    let seven = bv(&mut terms, 7);
    let nine = bv(&mut terms, 9);
    let index = terms.mk_ite(guard, one, two);
    let value = terms.mk_ite(guard, seven, nine);
    let base = constant(&mut terms, nine);
    let store = raw_store(&mut terms, base, index, value);
    let target = terms.mk_var("target", terms.sort(store).clone());
    let alias = terms.mk_var("alias", terms.sort(store).clone());
    let definition = terms.mk_eq_coerce_no_ite_expand(target, store);
    for choice in [false, true] {
        let mut bits = model();
        bits.bool_overrides.insert(guard, choice);
        for term in [index, value, nine] {
            bits.values.insert(term, BigInt::from(0u8));
        }
        let key = if choice { "#x01" } else { "#x02" };
        let expected = if choice { "#x07" } else { "#x09" };
        let mut arrays = Executor::extract_array_model_from_bv_model(
            &terms,
            &bits,
            &[definition],
            &HashSet::default(),
        );
        assert!(!arrays.read_conflicted.contains(&target));
        assert_eq!(lookup(&arrays.array_values[&target], key), expected);
        assert_eq!(lookup(&arrays.array_values[&target], "#x03"), "#x09");
        let mut stale_target = arrays.array_values[&target].clone();
        stale_target.default = Some("#x00".into());
        stale_target.stores.clear();
        arrays.array_values.insert(store, stale_target);
        Executor::populate_array_models_from_substitutions(
            &terms,
            &bits,
            &[(alias, target), (target, store)],
            &mut arrays,
        );
        for term in [target, alias] {
            assert!(!arrays.read_conflicted.contains(&term));
            assert_eq!(lookup(&arrays.array_values[&term], key), expected);
            assert_eq!(lookup(&arrays.array_values[&term], "#x03"), "#x09");
        }
    }
}

#[test]
fn boolean_cells_and_defaults_are_structural_and_selected_branch_only() {
    let mut terms = TermStore::new();
    let guard = terms.mk_var("guard", Sort::Bool);
    let unavailable = terms.mk_var("unavailable", Sort::Bool);
    let truth = terms.mk_bool(true);
    let not_guard = terms.mk_not(guard);
    let value = terms.mk_ite_raw(guard, not_guard, unavailable);
    let base = constant(&mut terms, truth);
    let index = bv(&mut terms, 3);
    let store = raw_store(&mut terms, base, index, value);
    let mut bits = model();
    bits.bool_overrides.insert(guard, true);
    bits.bool_overrides.insert(value, true);
    bits.bool_overrides.insert(not_guard, true);
    bits.bool_overrides.insert(truth, false);
    let interp =
        Executor::build_store_chain_interp(&terms, &bits, store, &mut ArrayModel::default())
            .expect("only the selected branch needs an assignment");
    assert_eq!(lookup(&interp, "#x03"), "false");
    assert_eq!(lookup(&interp, "#x04"), "true");
    bits.bool_overrides.insert(guard, false);
    assert!(
        Executor::build_store_chain_interp(&terms, &bits, store, &mut ArrayModel::default(),)
            .is_none()
    );
}

#[test]
fn every_unresolved_cell_refuses_even_when_shadowed_or_cached() {
    let mut terms = TermStore::new();
    let zero = bv(&mut terms, 0);
    let one = bv(&mut terms, 1);
    let unknown = terms.mk_var("unknown", Sort::bitvec(8));
    let guard = terms.mk_var("guard", Sort::Bool);
    let guarded = terms.mk_ite(guard, one, zero);
    let base = constant(&mut terms, zero);
    let missing_value = raw_store(&mut terms, base, zero, unknown);
    let shadowed = raw_store(&mut terms, missing_value, zero, one);
    let missing_key = raw_store(&mut terms, base, unknown, one);
    let missing_guard = raw_store(&mut terms, base, zero, guarded);
    let mut bits = model();
    bits.values.insert(guarded, BigInt::from(1u8));
    for (case, store) in [
        ("missing-value", missing_value),
        ("shadowed-missing-value", shadowed),
        ("missing-key", missing_key),
        ("missing-guard", missing_guard),
    ] {
        let target = terms.mk_var(format!("target_{}", store.0), terms.sort(store).clone());
        let definition = terms.mk_eq_coerce_no_ite_expand(target, store);
        let arrays = Executor::extract_array_model_from_bv_model(
            &terms,
            &bits,
            &[definition],
            &HashSet::default(),
        );
        assert!(arrays.read_conflicted.contains(&target));
        assert!(!arrays.array_values.contains_key(&target));
        let mut arrays = ArrayModel::default();
        Executor::populate_array_models_from_substitutions(
            &terms,
            &bits,
            &[(target, store)],
            &mut arrays,
        );
        // A recorded substitution retains a typed pending-definition reason,
        // rather than claiming that a committed read actually disagreed. It
        // must STILL withhold a complete array, including after stale cache
        // rows are supplied. The direct extraction check above stays hard.
        assert!(arrays.is_withheld(&target), "{case}");
        assert!(!arrays.read_conflicted.contains(&target), "{case}");
        let pending = arrays.pending_definitions[&target];
        assert!(pending.matches_current(&terms), "{case}");
        assert_eq!(pending.source(), target, "{case}");
        assert_eq!(pending.target(), store, "{case}");
        assert!(!arrays.array_values.contains_key(&target), "{case}");
        assert!(
            Executor::resolve_substitution_target_interp(&terms, &bits, store, &mut arrays,)
                .is_none(),
            "incomplete RHS cannot be total: {case}"
        );
        let stale = ArrayInterpretation {
            default: Some("#x5a".into()),
            stores: vec![("#x00".into(), "#x5a".into())],
            index_sort: Some(Sort::bitvec(8)),
            element_sort: Some(Sort::bitvec(8)),
        };
        arrays.array_values.insert(target, stale.clone());
        arrays.array_values.insert(store, stale.clone());
        Executor::populate_array_models_from_substitutions(
            &terms,
            &bits,
            &[(target, store)],
            &mut arrays,
        );
        assert!(arrays.is_withheld(&target), "{case}");
        assert_eq!(
            arrays.pending_definitions.get(&target),
            Some(&pending),
            "{case}"
        );
        assert!(!arrays.read_conflicted.contains(&target), "{case}");
        assert_eq!(
            arrays.array_values.get(&target),
            Some(&stale),
            "retained source DATA: {case}"
        );
        assert!(
            Executor::resolve_substitution_target_interp(&terms, &bits, target, &mut arrays,)
                .is_none(),
            "pending source has no usable total fallback: {case}"
        );
        assert!(
            Executor::resolve_substitution_target_interp(&terms, &bits, store, &mut arrays,)
                .is_none(),
            "a compound RHS cache cannot skip unresolved cells: {case}"
        );
    }
}

#[test]
fn outermost_store_and_first_existing_base_entry_win_without_losing_default() {
    let mut terms = TermStore::new();
    let base = terms.mk_var("base", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
    let one = bv(&mut terms, 1);
    let seven = bv(&mut terms, 7);
    let nine = bv(&mut terms, 9);
    let inner = raw_store(&mut terms, base, one, seven);
    let outer = raw_store(&mut terms, inner, one, nine);
    let original = ArrayInterpretation {
        index_sort: Some(Sort::bitvec(8)),
        element_sort: Some(Sort::bitvec(8)),
        default: Some("#x33".into()),
        stores: vec![
            ("#x01".into(), "#x02".into()),
            ("#x04".into(), "#x05".into()),
            ("#x04".into(), "#x06".into()),
        ],
    };
    let mut arrays = ArrayModel::default();
    arrays.array_values.insert(base, original.clone());
    let interp = Executor::build_store_chain_interp(&terms, &model(), outer, &mut arrays)
        .expect("all cells resolve");
    assert_eq!(lookup(&interp, "#x01"), "#x09");
    assert_eq!(lookup(&interp, "#x04"), "#x05");
    assert_eq!(lookup(&interp, "#x08"), "#x33");
    assert_eq!(arrays.array_values[&base].stores, original.stores);
    assert_eq!(arrays.array_values[&base].default, original.default);
}

#[test]
fn primitive_base_choice_is_published_but_partial_or_opaque_bases_refuse() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let base = terms.mk_var("base", sort.clone());
    let zero = bv(&mut terms, 0);
    let one = bv(&mut terms, 1);
    let store = raw_store(&mut terms, base, zero, one);
    let mut arrays = ArrayModel::default();
    let interp = Executor::build_store_chain_interp(&terms, &model(), store, &mut arrays)
        .expect("explicit free-base model choice");
    assert_eq!(arrays.array_values[&base].default.as_deref(), Some("#x00"));
    assert_eq!(interp.default, arrays.array_values[&base].default);
    arrays.read_conflicted.insert(base);
    assert!(Executor::build_store_chain_interp(&terms, &model(), store, &mut arrays).is_none());
    arrays.read_conflicted.clear();
    arrays.array_values.get_mut(&base).unwrap().default = None;
    assert!(Executor::build_store_chain_interp(&terms, &model(), store, &mut arrays).is_none());
    let opaque = terms.mk_app(Symbol::named("opaque"), vec![], sort);
    let opaque_store = raw_store(&mut terms, opaque, zero, one);
    assert!(
        Executor::build_store_chain_interp(&terms, &model(), opaque_store, &mut arrays).is_none()
    );
}

#[test]
fn a_later_known_nonzero_source_base_definition_is_resolved_before_inheritance() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let target = terms.mk_var("target_first", sort.clone());
    let base = terms.mk_var("base_later", sort);
    let zero = bv(&mut terms, 0);
    let one = bv(&mut terms, 1);
    let nine = bv(&mut terms, 9);
    let constant = constant(&mut terms, nine);
    let store = raw_store(&mut terms, base, zero, one);
    let def_target = terms.mk_eq_coerce_no_ite_expand(target, store);
    let def_base = terms.mk_eq_coerce_no_ite_expand(base, constant);
    for assertions in [[def_target, def_base], [def_base, def_target]] {
        let arrays = Executor::extract_array_model_from_bv_model(
            &terms,
            &model(),
            &assertions,
            &HashSet::default(),
        );
        assert!(!arrays.read_conflicted.contains(&target));
        assert_eq!(lookup(&arrays.array_values[&target], "#x00"), "#x01");
        assert_eq!(lookup(&arrays.array_values[&target], "#x01"), "#x09");
        assert_eq!(arrays.array_values[&base].default.as_deref(), Some("#x09"));
    }
}

#[test]
fn failed_base_definition_withholds_earlier_dependents_and_substitution_aliases() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let target = terms.mk_var("target", sort.clone());
    let base = terms.mk_var("base", sort.clone());
    let alias = terms.mk_var("alias", sort);
    let zero = bv(&mut terms, 0);
    let unknown = terms.mk_var("unknown", Sort::bitvec(8));
    let constant = constant(&mut terms, zero);
    let bad_base = raw_store(&mut terms, constant, unknown, zero);
    let store = raw_store(&mut terms, base, zero, zero);
    let def_target = terms.mk_eq_coerce_no_ite_expand(target, store);
    let def_base = terms.mk_eq_coerce_no_ite_expand(base, bad_base);
    for assertions in [[def_target, def_base], [def_base, def_target]] {
        let mut arrays = Executor::extract_array_model_from_bv_model(
            &terms,
            &model(),
            &assertions,
            &HashSet::default(),
        );
        assert!(arrays.read_conflicted.contains(&target));
        assert!(arrays.read_conflicted.contains(&base));
        Executor::populate_array_models_from_substitutions(
            &terms,
            &model(),
            &[(alias, target)],
            &mut arrays,
        );
        assert!(arrays.read_conflicted.contains(&alias));
        assert!(!arrays.array_values.contains_key(&alias));
    }
}

#[test]
fn exactly_five_hundred_stores_fit_but_a_truncated_prefix_never_publishes() {
    let mut terms = TermStore::new();
    let zero = bv(&mut terms, 0);
    let mut store = constant(&mut terms, zero);
    // Raw applications retain the exact chain even when every key repeats.
    for depth in 1..=501 {
        store = terms.mk_app(
            Symbol::named("store"),
            vec![store, zero, zero],
            terms.sort(store).clone(),
        );
        if depth >= 500 {
            let mut arrays = ArrayModel::default();
            assert_eq!(
                Executor::build_store_chain_interp(&terms, &model(), store, &mut arrays).is_some(),
                depth == 500
            );
            let target = terms.mk_var(format!("target_{depth}"), terms.sort(store).clone());
            Executor::populate_array_models_from_substitutions(
                &terms,
                &model(),
                &[(target, store)],
                &mut arrays,
            );
            assert_eq!(arrays.is_withheld(&target), depth == 501);
            if depth == 501 {
                assert!(!arrays.array_values.contains_key(&target));
                assert_eq!(arrays.pending_definitions[&target].target(), store);
            }
        }
    }
}

#[test]
fn malformed_store_metadata_and_noncanonical_leaf_values_refuse() {
    let mut terms = TermStore::new();
    let zero = bv(&mut terms, 0);
    let truth = terms.mk_bool(true);
    let base = constant(&mut terms, zero);
    let sort = terms.sort(base).clone();
    let wrong_key = terms.mk_app(
        Symbol::named("store"),
        vec![base, truth, zero],
        sort.clone(),
    );
    let wrong_value = terms.mk_app(
        Symbol::named("store"),
        vec![base, zero, truth],
        sort.clone(),
    );
    let indexed = terms.mk_app(
        Symbol::indexed("store", vec![0]),
        vec![base, zero, zero],
        sort.clone(),
    );
    let wrong_const = terms.mk_app(Symbol::named("const-array"), vec![truth], sort);
    let malformed_base = raw_store(&mut terms, wrong_const, zero, zero);
    for store in [wrong_key, wrong_value, indexed, malformed_base] {
        assert!(Executor::build_store_chain_interp(
            &terms,
            &model(),
            store,
            &mut ArrayModel::default()
        )
        .is_none());
    }
    let variable = terms.mk_var("value", Sort::bitvec(8));
    let store = raw_store(&mut terms, base, zero, variable);
    for invalid in [BigInt::from(-1), BigInt::from(256u32)] {
        let mut bits = model();
        bits.values.insert(variable, invalid);
        assert!(Executor::build_store_chain_interp(
            &terms,
            &bits,
            store,
            &mut ArrayModel::default()
        )
        .is_none());
    }
}

fn select(terms: &mut TermStore, array: TermId, index: TermId) -> TermId {
    terms.mk_app(Symbol::named("select"), vec![array, index], Sort::bitvec(8))
}

/// #defined-array-read-pins: a candidate read committed on a
/// store-defined array at an index the chain does not store to must
/// survive into the built interpretation (via the terminal base),
/// not revert to the base default. Regression for the QF_ABV dwp
/// mem-generation witnesses, where byte loads through
/// `mem_k = store(mem_{k-1}, …)` chains evaluated to the default
/// and the soundness gate rejected genuine candidates.
#[test]
fn defined_array_read_pins_propagate_to_terminal_base() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let base = terms.mk_var("base", arr_sort.clone());
    let mid = terms.mk_var("mid", arr_sort.clone());
    let top = terms.mk_var("top", arr_sort);
    let one = bv(&mut terms, 1);
    let two = bv(&mut terms, 2);
    let five = bv(&mut terms, 5);
    let aa = bv(&mut terms, 0xAA);
    let bb = bv(&mut terms, 0xBB);
    let mid_def = {
        let store = raw_store(&mut terms, base, one, aa);
        terms.mk_eq_coerce_no_ite_expand(mid, store)
    };
    let top_def = {
        let store = raw_store(&mut terms, mid, two, bb);
        terms.mk_eq_coerce_no_ite_expand(top, store)
    };
    let sel_top = select(&mut terms, top, five);
    let mut bits = model();
    bits.values.insert(sel_top, BigInt::from(0x7Fu8));
    bits.values.insert(five, BigInt::from(5u8));
    let arrays = Executor::extract_array_model_from_bv_model(
        &terms,
        &bits,
        &[mid_def, top_def],
        &HashSet::default(),
    );
    assert!(!arrays.read_conflicted.contains(&top));
    assert_eq!(lookup(&arrays.array_values[&top], "#x05"), "#x7f");
    assert_eq!(lookup(&arrays.array_values[&top], "#x01"), "#xaa");
    assert_eq!(lookup(&arrays.array_values[&top], "#x02"), "#xbb");
    assert_eq!(lookup(&arrays.array_values[&mid], "#x05"), "#x7f");
    assert_eq!(lookup(&arrays.array_values[&base], "#x05"), "#x7f");
}

/// #model-true-array-equality: a var<->var array equality the
/// candidate makes true at a nested position aligns both sides to
/// one interpretation. A genuine in-assertion read on the free
/// side outranks the defined side's inherited pin; gap pins merge.
#[test]
fn model_true_nested_array_equality_adopts_authoritative_interp() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let base = terms.mk_var("base", arr_sort.clone());
    let defined = terms.mk_var("defined", arr_sort.clone());
    let free = terms.mk_var("free", arr_sort);
    let one = bv(&mut terms, 1);
    let five = bv(&mut terms, 5);
    let six = bv(&mut terms, 6);
    let aa = bv(&mut terms, 0xAA);
    let def = {
        let store = raw_store(&mut terms, base, one, aa);
        terms.mk_eq_coerce_no_ite_expand(defined, store)
    };
    let eq = terms.mk_eq_coerce_no_ite_expand(free, defined);
    let truth = terms.mk_bool(true);
    let falsity = terms.mk_bool(false);
    let carrier = terms.mk_ite_raw(eq, truth, falsity);
    let sel_base5 = select(&mut terms, base, five);
    let sel_free5 = select(&mut terms, free, five);
    let sel_free6 = select(&mut terms, free, six);
    // The free side's conflicting cell is read by an asserted term,
    // making it a genuine read the completion must honor.
    let ff = bv(&mut terms, 0xFF);
    let read_assert = terms.mk_eq_coerce_no_ite_expand(sel_free5, ff);
    let mut bits = model();
    bits.bool_overrides.insert(eq, true);
    bits.values.insert(sel_base5, BigInt::from(0x70u8));
    bits.values.insert(sel_free5, BigInt::from(0xFFu8));
    bits.values.insert(sel_free6, BigInt::from(0x66u8));
    bits.values.insert(five, BigInt::from(5u8));
    bits.values.insert(six, BigInt::from(6u8));
    let arrays = Executor::extract_array_model_from_bv_model(
        &terms,
        &bits,
        &[def, carrier, read_assert],
        &HashSet::default(),
    );
    assert_eq!(lookup(&arrays.array_values[&free], "#x01"), "#xaa");
    assert_eq!(lookup(&arrays.array_values[&free], "#x05"), "#xff");
    assert_eq!(lookup(&arrays.array_values[&defined], "#x05"), "#xff");
    assert_eq!(lookup(&arrays.array_values[&free], "#x06"), "#x66");
    assert_eq!(lookup(&arrays.array_values[&defined], "#x06"), "#x66");
}

#[test]
fn protected_conflicts_dominate_pending_definitions_even_after_the_rhs_becomes_complete() {
    let mut terms = TermStore::new();
    let zero = bv(&mut terms, 0);
    let one = bv(&mut terms, 1);
    let unknown = terms.mk_var("unknown", Sort::bitvec(8));
    let base = constant(&mut terms, zero);
    let store = raw_store(&mut terms, base, one, unknown);
    let target = terms.mk_var("target", terms.sort(store).clone());
    let mut bits = model();
    let mut pending = ArrayModel::default();
    Executor::populate_array_models_from_substitutions(
        &terms,
        &bits,
        &[(target, store)],
        &mut pending,
    );
    let original = pending.pending_definitions[&target];
    assert!(pending.is_withheld(&target));
    assert!(!pending.read_conflicted.contains(&target));
    bits.values.insert(unknown, BigInt::from(7u8));
    // Discriminating opposite: the SAME RHS now really is reconstructible.
    // A later protected conflict must dominate this newly complete DATA.
    assert!(Executor::resolve_substitution_target_interp(
        &terms,
        &bits,
        store,
        &mut pending.clone(),
    )
    .is_some());
    for conflict in [target, store] {
        let mut arrays = pending.clone();
        arrays.read_conflicted.insert(conflict);
        Executor::populate_array_models_from_substitutions(
            &terms,
            &bits,
            &[(target, store)],
            &mut arrays,
        );
        assert!(arrays.read_conflicted.contains(&conflict));
        assert!(arrays.read_conflicted.contains(&target));
        assert!(arrays.is_withheld(&target));
        assert_eq!(arrays.pending_definitions.get(&target), Some(&original));
        assert!(!arrays.array_values.contains_key(&target));
        assert!(!arrays.discharge_array_definition(&terms, target, store));
        assert!(
            Executor::resolve_substitution_target_interp(&terms, &bits, target, &mut arrays,)
                .is_none()
        );
    }
}
