// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{FpConstruction, FpSolver};
use ay_core::TermStore;
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

fn fixture(width: u32) -> (TermStore, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(width));
    let b = terms.mk_var("b", Sort::bitvec(width));
    let guard = terms.mk_app(Symbol::named("bvslt"), [a, b], Sort::Bool);
    (terms, a, b, guard)
}

#[test]
fn ordinary_none_or_external_tseitin_names_never_authorize_closed_bv_guards() {
    let (terms, _, _, guard) = fixture(64);
    let end = Instant::now() + Duration::from_secs(20);
    let mut stop = |_| Instant::now() >= end;
    let mut ordinary = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    ordinary.try_encode_bool_condition(guard).unwrap();
    let ordinary = ordinary.finish().unwrap();
    // DR-47: an unlinked External guard is its exact comparator over the
    // shared operand bits, not a gap.
    assert!(!ordinary.has_encoding_gap);
    assert_eq!(ordinary.pending_condition_links.len(), 0);
    assert_ne!(ordinary.cache.bv_term_bits.len(), 0);
    let mut names = BTreeMap::new();
    names.insert(guard, 77);
    let mut linked =
        FpConstruction::new(FpSolver::new_with_tseitin(&terms, &names), &mut stop).unwrap();
    linked.try_encode_bool_condition(guard).unwrap();
    let result = linked.finish().unwrap();
    assert!(!result.has_encoding_gap);
    assert_eq!(result.pending_condition_links.len(), 1);
    assert_eq!(result.pending_condition_links[0].1, 77);
    assert_eq!(result.cache.bv_term_bits.len(), 0);
}

#[test]
fn seeded_tseitin_names_link_their_guards_and_refuse_every_unnamed_one() {
    let (terms, _, _, guard) = fixture(64);
    let end = Instant::now() + Duration::from_secs(20);
    let mut stop = |_| Instant::now() >= end;
    let unnamed = BTreeMap::new();
    // DR-47 twin: an External map that lacks the guard encodes its circuit.
    let external = FpSolver::new_with_tseitin(&terms, &unnamed);
    let mut external = FpConstruction::new(external, &mut stop).unwrap();
    external.try_encode_bool_condition(guard).unwrap();
    assert!(!external.finish().unwrap().has_encoding_gap);
    // A seeding caller left this guard unnamed, i.e. refused it (a guard below
    // a binder): no circuit over a bound variable's bits, the gap stays.
    let mut seeded = FpSolver::new_with_seeded_tseitin(&terms, &unnamed);
    ay_core::TheorySolver::reset(&mut seeded);
    assert!(seeded.condition_namespace == ConditionNamespace::SeededExternal);
    let mut seeded = FpConstruction::new(seeded, &mut stop).unwrap();
    seeded.try_encode_bool_condition(guard).unwrap();
    let refused = seeded.finish().unwrap();
    assert!(refused.has_encoding_gap);
    assert_eq!(refused.cache.bv_term_bits.len(), 0);
    // A seeded name links exactly as an External one does.
    let mut names = BTreeMap::new();
    names.insert(guard, 77);
    let linked = FpSolver::new_with_seeded_tseitin(&terms, &names);
    let mut linked = FpConstruction::new(linked, &mut stop).unwrap();
    linked.try_encode_bool_condition(guard).unwrap();
    let result = linked.finish().unwrap();
    assert!(!result.has_encoding_gap);
    assert_eq!(result.pending_condition_links.len(), 1);
    assert_eq!(result.pending_condition_links[0].1, 77);
    assert_eq!(result.cache.bv_term_bits.len(), 0);
}

#[test]
fn closed_cache_import_and_ordinary_reset_do_not_transfer_private_authority() {
    let (terms, _, _, guard) = fixture(32);
    let end = Instant::now() + Duration::from_secs(20);
    let mut stop = |_| Instant::now() >= end;
    let mut closed = FpConstruction::new_closed_data(&terms, &mut stop).unwrap();
    closed.try_encode_bool_condition(guard).unwrap();
    let output = closed.finish().unwrap();
    assert!(!output.has_encoding_gap);
    let mut imported = FpSolver::new(&terms);
    imported.import_cache(output.cache);
    assert!(imported.condition_namespace == ConditionNamespace::External);
    ay_core::TheorySolver::reset(&mut imported);
    assert!(imported.condition_namespace == ConditionNamespace::External);
    let mut ordinary = FpConstruction::new(imported, &mut stop).unwrap();
    ordinary.try_encode_bool_condition(guard).unwrap();
    // DR-47 authority (External), not an imported closed-data permission.
    assert!(!ordinary.finish().unwrap().has_encoding_gap);
}

#[test]
fn closed_fp_reinterpretation_and_comparator_export_the_same_full_word_bits() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut stop = |_| Instant::now() >= end;
    for (width, e, s) in [(32, 8, 24), (64, 11, 53)] {
        let (mut terms, a, b, guard) = fixture(width);
        let fp = terms.mk_app(
            Symbol::indexed("to_fp", vec![e, s]),
            [a],
            Sort::FloatingPoint(e, s),
        );
        let mut closed = FpConstruction::new_closed_data(&terms, &mut stop).unwrap();
        let decomposed = closed.try_get_fp(fp).unwrap();
        closed.try_encode_bool_condition(guard).unwrap();
        let output = closed.finish().unwrap();
        assert!(!output.has_encoding_gap);
        assert_eq!(output.pending_condition_links.len(), 0);
        let a_bits = &output.cache.bv_term_bits[&a];
        assert_eq!(a_bits.len(), width as usize);
        assert_eq!(output.cache.bv_term_bits[&b].len(), width as usize);
        assert_eq!(&a_bits[..s as usize - 1], decomposed.significand.as_slice());
        assert_eq!(
            &a_bits[s as usize - 1..width as usize - 1],
            decomposed.exponent.as_slice()
        );
        assert_eq!(a_bits[width as usize - 1], decomposed.sign);
    }
}

#[test]
fn malformed_max_extract_indices_refuse_before_overflow_or_bv_cloning() {
    let (mut terms, a, _, _) = fixture(32);
    let invalid = terms.mk_app(
        Symbol::indexed("extract", vec![u32::MAX, 0]),
        [a],
        Sort::bitvec(1),
    );
    let zero = terms.mk_bitvec(0u8.into(), 1);
    let guard = terms.mk_app(Symbol::named("bvult"), [invalid, zero], Sort::Bool);
    let end = Instant::now() + Duration::from_secs(20);
    let mut stop = |_| Instant::now() >= end;
    let mut closed = FpConstruction::new_closed_data(&terms, &mut stop).unwrap();
    closed.try_encode_bool_condition(guard).unwrap();
    let output = closed.finish().unwrap();
    assert!(output.has_encoding_gap);
    assert_eq!(output.cache.bv_term_bits.len(), 0);
}

#[test]
fn closed_comparator_owner_refusal_stays_sticky_and_final_drop_can_veto() {
    let (terms, _, _, guard) = fixture(64);
    let end = Instant::now() + Duration::from_secs(20);
    let enabled = std::cell::Cell::new(true);
    let mut stop =
        |p: crate::FpBuildProgress| Instant::now() >= end || (enabled.get() && p.variables >= 64);
    let mut closed = FpConstruction::new_closed_data(&terms, &mut stop).unwrap();
    assert!(closed.try_encode_bool_condition(guard).is_err());
    enabled.set(false);
    assert!(closed.try_encode_bool_condition(guard).is_err());
    assert!(closed.finish().is_err());
    let finals = std::cell::Cell::new(0);
    let mut stop = |p: crate::FpBuildProgress| {
        if p.stage == FpBuildStage::Finalize {
            finals.set(finals.get() + 1);
        }
        Instant::now() >= end || finals.get() == 2
    };
    let mut closed = FpConstruction::new_closed_data(&terms, &mut stop).unwrap();
    closed.try_encode_bool_condition(guard).unwrap();
    assert!(closed.finish().is_err());
    assert_eq!(finals.get(), 2);
}
