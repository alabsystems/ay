// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pins for the counter-only exemption from the prune veto: the exact
//! grammar both ways, the real mints it names, and the prune it restores.
//! The BV-LIA bridge's own producers are pinned beside them
//! (`theories::combined::bv_lia_aux_vars`).

#![allow(clippy::panic)]

use super::*;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermStore};
use ay_frontend::parse;

/// Exactly `prefix + non-empty all-digit tail`, for exactly the listed
/// prefixes.
#[test]
fn only_the_exact_counter_spellings_are_exempt() {
    for exempt in [
        "__ay_overload_0",
        "__ay_overload_42",
        "__ay_ext_diff!19",
        "__ay_eqdv!28",
        "__ay_bv_lia_cong_14",
        "__ay_bv_lia_i_9",
    ] {
        assert!(is_counter_only_internal_name(exempt), "{exempt}");
    }
    for vetoed in [
        "__ay_overload_",
        "__ay_overload_7x",
        "__ay_overload_-1",
        "__ay_ext_diff!",
        "__ay_ext_diff_1_2",
        "__ay_ext_diff!19!3",
        "__ay_eqdv!",
        "__ay_eqdv!3x",
        "__ay_eqdv_p3",
        "__ay_bv_lia_cong_",
        "__ay_bv_lia_cong!14",
        "__ay_bv_lia_cong_k4_w64_14",
        "__ay_bv_lia_i4_w64_9",
        "__ay_zerodiv_div_56",
        "__ay_ite_def_12",
        "__ay_map_dom!m!7",
        "__ay_sk_x!3",
    ] {
        assert!(!is_counter_only_internal_name(vetoed), "{vetoed}");
    }
}

/// Two datatypes sharing a field name, the second's selector applied to a
/// non-variable term (a constant of the record sort is flattened into field
/// variables instead), and a pile of unnamed scratch: the arena an enclosing
/// solve hands a probe.
fn overloaded_field_executor() -> (Executor, Vec<TermId>) {
    let commands = parse(
        "(set-logic ALL)
         (declare-datatype CounterInner ((mkCounterInner (cn_len Int))))
         (declare-datatype CounterOuter ((mkCounterOuter (cn_len Int))))
         (declare-fun counter_outer (Int) CounterOuter)
         (assert (= (cn_len (counter_outer 0)) 1))",
    )
    .expect("fixture parses");
    let mut executor = Executor::new();
    executor.execute_all(&commands).expect("fixture executes");
    let roots = executor.ctx.assertions.clone();
    let a = executor.ctx.terms.mk_var("counter_scratch_a", Sort::Int);
    for index in 0..64 {
        let scratch = executor.ctx.terms.mk_app(
            Symbol::named(format!("counter_scratch_{index}")),
            [a],
            Sort::Bool,
        );
        let _negated = executor.ctx.terms.mk_not_raw(scratch);
    }
    (executor, roots)
}

fn internal_names(store: &TermStore) -> Vec<String> {
    (0..store.len())
        .filter_map(|index| {
            let id = TermId(u32::try_from(index).expect("arena index fits u32"));
            match store.get(id) {
                TermData::Var(name, _) => Some(name.clone()),
                TermData::App(Symbol::Named(name), _) => Some(name.to_string()),
                _ => None,
            }
        })
        .filter(|name| name.starts_with(INTERNAL_SYMBOL_MARKER))
        .collect()
}

/// DRIFT GUARD against the producers the allow-list names. If either mint
/// changes its spelling, this fails instead of the exemption silently dying
/// (or, worse, silently covering a different mint).
#[test]
fn the_exempt_spellings_are_what_the_real_mints_produce() {
    assert_eq!(
        ARRAY_EXT_WITNESS_SPELLING,
        crate::executor::theories::ARRAY_EXT_WITNESS_PREFIX
    );
    let minted = TermStore::new().mk_internal_symbol("ext_diff");
    assert!(is_counter_only_internal_name(&minted), "{minted}");
    assert_eq!(
        EQ_DIFF_VARIABLE_SPELLING,
        format!("__ay_{}!", crate::preprocess::EQ_DIFF_VARIABLE_PURPOSE)
    );
    let minted = TermStore::new().mk_internal_symbol(crate::preprocess::EQ_DIFF_VARIABLE_PURPOSE);
    assert!(is_counter_only_internal_name(&minted), "{minted}");

    let (executor, _roots) = overloaded_field_executor();
    let names = internal_names(&executor.ctx.terms);
    assert!(
        names
            .iter()
            .any(|name| name.starts_with(PRIVATE_DECLARATION_IDENTITY_PREFIX)),
        "the overloaded selector must carry a private core identity: {names:?}"
    );
    assert!(
        names
            .iter()
            .filter(|name| name.bytes().any(|byte| byte.is_ascii_digit()))
            .all(|name| is_counter_only_internal_name(name)),
        "every digit-bearing internal name this fixture mints is counter-only: {names:?}"
    );
    assert!(!carries_name_encoded_term_ids(&executor.ctx.terms));
}

/// THE RESTORED PRUNE: an overloaded datatype field no longer hands the probe
/// the enclosing arena.
#[test]
fn an_overloaded_datatype_field_does_not_veto_the_prune() {
    let (mut executor, roots) = overloaded_field_executor();
    let witness_name = executor.ctx.terms.mk_internal_symbol("ext_diff");
    let _witness = executor.ctx.terms.mk_var(witness_name, Sort::Int);
    let before = executor.ctx.terms.len();
    let probe_ctx = executor
        .pruned_isolated_probe_context(&roots)
        .expect("the probe context builds");
    assert!(
        probe_ctx.terms.len() + 128 <= before,
        "counter-only names must not veto pruning: {before} -> {}",
        probe_ctx.terms.len()
    );
}

/// THE RESTORED PRUNE for the BV-LIA bridge and the equality-difference
/// pass: an arena holding their counter-spelled variables is pruned.
#[test]
fn bv_lia_and_difference_variables_do_not_veto_the_prune() {
    use crate::executor::theories::bv_lia_aux_vars::{mint_bv_lia_aux_var, BvLiaAuxVar};
    let (mut executor, roots) = overloaded_field_executor();
    let terms = &mut executor.ctx.terms;
    let _slack = mint_bv_lia_aux_var(terms, BvLiaAuxVar::CongruenceSlack, Sort::Int);
    let _residue = mint_bv_lia_aux_var(terms, BvLiaAuxVar::ResidueVector, Sort::bitvec(8));
    let name = terms.mk_internal_symbol(crate::preprocess::EQ_DIFF_VARIABLE_PURPOSE);
    let _difference = terms.mk_var(name, Sort::Int);
    let before = terms.len();
    let probe_ctx = executor
        .pruned_isolated_probe_context(&roots)
        .expect("the probe context builds");
    assert!(
        probe_ctx.terms.len() + 128 <= before,
        "counter-only names must not veto pruning: {before} -> {}",
        probe_ctx.terms.len()
    );
}

/// The equality-difference PASS itself, not only its purpose constant, leaves
/// an arena the prune accepts: a guarded var-var network rewritten to one
/// `__ay_eqdv!{n}`.
#[test]
fn the_eq_diffvar_pass_leaves_a_prunable_arena() {
    use crate::preprocess::{EqDiffVar, PreprocessingPass};
    let mut terms = TermStore::new();
    let g = terms.mk_var("g", Sort::Bool);
    let h = terms.mk_var("h", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let not_g = terms.mk_not(g);
    let not_h = terms.mk_not(h);
    let eq_xy = terms.mk_eq(x, y);
    let eq_yx = terms.mk_eq(y, x);
    let guarded_xy = terms.mk_or(vec![not_g, eq_xy]);
    let guarded_yx = terms.mk_or(vec![not_h, eq_yx]);
    let mut assertions = vec![guarded_xy, guarded_yx];
    assert!(EqDiffVar::new().apply(&mut terms, &mut assertions));
    let names = internal_names(&terms);
    assert!(
        names
            .iter()
            .any(|name| name.starts_with(EQ_DIFF_VARIABLE_SPELLING)),
        "{names:?}"
    );
    assert!(!carries_name_encoded_term_ids(&terms), "{names:?}");
}

/// THE VETO IS KEPT for everything outside the exact grammar, including a
/// near miss of an exempt prefix and the BV-LIA slack's former `TermId`
/// spelling.
#[test]
fn a_near_miss_spelling_still_vetoes_the_prune() {
    for near_miss in [
        "__ay_ext_diff_1_2",
        "__ay_overload_7x",
        "__ay_eqdv!3x",
        "__ay_bv_lia_cong_k4_w64_14",
        "__ay_bv_lia_i4_w64_9",
    ] {
        let (mut executor, roots) = overloaded_field_executor();
        let _var = executor.ctx.terms.mk_var(near_miss, Sort::Int);
        let before = executor.ctx.terms.len();
        let probe_ctx = executor
            .pruned_isolated_probe_context(&roots)
            .expect("the probe context builds");
        assert_eq!(
            probe_ctx.terms.len(),
            before,
            "`{near_miss}` is not a proven counter spelling and must veto the prune"
        );
    }
}
