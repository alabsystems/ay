// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pins for the BV-LIA auxiliary-variable spelling: the exact grammar both
//! ways, and each producer in `combined` checked against the arena-prune veto.
//! The Int-blast lane's vectors are pinned in `int_blast`'s own tests.

use super::super::{collect_int_facts, push_bv2nat_range, BvLiaBitblastTranslator};
use super::*;
use crate::executor::quantifier_loop::result_mapping::carries_name_encoded_term_ids;
use crate::executor::Executor;
use ay_core::term::TermData;
use ay_frontend::parse;

fn bv_lia_names(terms: &TermStore) -> Vec<String> {
    (0..terms.len())
        .filter_map(|index| {
            let id = TermId(u32::try_from(index).expect("arena index fits u32"));
            match terms.get(id) {
                TermData::Var(name, _) if name.starts_with("__ay_bv_lia") => Some(name.clone()),
                _ => None,
            }
        })
        .collect()
}

/// Every kind's minted name, and nothing else in the family, matches the
/// grammar the prune's allow-list reads.
#[test]
fn the_grammar_is_exactly_what_the_minter_spells() {
    let mut terms = TermStore::new();
    for kind in BvLiaAuxVar::ALL {
        let _var = mint_bv_lia_aux_var(&mut terms, kind, Sort::Int);
    }
    let names = bv_lia_names(&terms);
    assert_eq!(names.len(), BvLiaAuxVar::ALL.len(), "{names:?}");
    for (kind, name) in BvLiaAuxVar::ALL.iter().zip(&names) {
        assert!(name.starts_with(kind.prefix()), "{kind:?}: {name}");
        assert!(is_bv_lia_aux_var_name(name), "{name}");
    }
    assert!(!carries_name_encoded_term_ids(&terms), "{names:?}");
    for vetoed in [
        "__ay_bv_lia_cong",
        "__ay_bv_lia_cong_",
        "__ay_bv_lia_cong!14",
        "__ay_bv_lia_cong_k4_w64_14",
        "__ay_bv_lia_i4_w64_9",
        "__ay_bv_lia_q7_w8_3",
        "__ay_bv_lia_ib2_w16_5",
        "__ay_bv_lia_ir2_w16_5",
        "__ay_bv_lia_i_4_9",
        "__ay_bv_lia_q_3x",
        "__ay_bv_lia_x_3",
    ] {
        assert!(!is_bv_lia_aux_var_name(vetoed), "{vetoed}");
    }
}

/// `push_bv2nat_congruence` (through `push_bv2nat_range`, the int2bv path the
/// deductive-checks obligation takes): the slack of `bv2nat(int2bv_8 x) = x - 256 k`.
#[test]
fn the_bv2nat_congruence_slack_does_not_veto_the_prune() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let bv = terms.mk_int2bv(8, x);
    let nat = terms.mk_bv2nat(bv);
    let mut out = Vec::new();
    push_bv2nat_range(&mut terms, &mut out, bv, nat);
    let names = bv_lia_names(&terms);
    assert!(
        names
            .iter()
            .any(|name| name.starts_with("__ay_bv_lia_cong_")),
        "the congruence slack is minted: {names:?}"
    );
    assert!(!carries_name_encoded_term_ids(&terms), "{names:?}");
}

/// `int_residue_var` mints the residue vector AND, through
/// `push_residue_congruence`, its slack: neither may veto the prune.
#[test]
fn the_residue_vector_and_its_slack_do_not_veto_the_prune() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let facts = collect_int_facts(&terms, &[]);
    let assertions = {
        let mut translator = BvLiaBitblastTranslator::new(&mut terms, &facts);
        let _residue = translator.int_residue_var(x, 8);
        translator.into_range_assertions()
    };
    assert_ne!(assertions, [] as [TermId; 0]);
    let names = bv_lia_names(&terms);
    for prefix in ["__ay_bv_lia_i_", "__ay_bv_lia_cong_"] {
        assert!(
            names.iter().any(|name| name.starts_with(prefix)),
            "{prefix}: {names:?}"
        );
    }
    assert!(!carries_name_encoded_term_ids(&terms), "{names:?}");
}

/// The residue bridge's Euclidean form `e = bv2nat(int2bv(8, e)) + 256 k`,
/// minted into the executor's live arena when nothing bounds `e`.
#[test]
fn the_euclidean_quotient_does_not_veto_the_prune() {
    let commands = parse(
        "(set-logic ALL)
         (declare-const e Int)
         (assert (= (bv2nat ((_ int2bv 8) e)) 3))",
    )
    .expect("fixture parses");
    let mut executor = Executor::new();
    executor.execute_all(&commands).expect("fixture executes");
    let roots = executor.ctx.assertions.clone();
    let bridge = executor.collect_bv_lia_residue_bridge_assertions(&roots);
    assert_ne!(bridge, [] as [TermId; 0]);
    let names = bv_lia_names(&executor.ctx.terms);
    assert!(
        names.iter().any(|name| name.starts_with("__ay_bv_lia_q_")),
        "the unbounded source takes the Euclidean form: {names:?}"
    );
    assert!(
        !carries_name_encoded_term_ids(&executor.ctx.terms),
        "{names:?}"
    );
}
