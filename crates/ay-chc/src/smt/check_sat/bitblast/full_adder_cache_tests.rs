// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

//! Exercise structural cache helpers without entering check_sat or a SAT solver.

use super::*;
use crate::smt::context::PersistentBvCache;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_bv::BvSolver;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::{CnfClause, CnfLit};
use std::sync::Arc;

#[path = "../../../../../ay-theories/bv/src/tests/division_carry/cnf.rs"]
mod cnf;

struct Terms {
    x: TermId,
    y: TermId,
    sum: TermId,
    atom: TermId,
    next_sum: TermId,
    next_atom: TermId,
}

fn terms(ctx: &mut SmtContext, padding: usize) -> Terms {
    for index in 0..padding {
        let _ = ctx.convert_expr(&ChcExpr::var(ChcVar::new(
            format!("unrelated_{index}"),
            ChcSort::BitVec(4),
        )));
    }
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(4)));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(4)));
    let sum = ChcExpr::Op(ChcOp::BvAdd, vec![Arc::new(x.clone()), Arc::new(y.clone())]);
    let atom = ChcExpr::Op(
        ChcOp::BvULt,
        vec![Arc::new(sum.clone()), Arc::new(x.clone())],
    );
    let next_sum = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![Arc::new(sum.clone()), Arc::new(x.clone())],
    );
    // Extract is outside the structural signature grammar. This is a fresh
    // cube atom over retained arithmetic, with the original cacheable atom.
    let next_atom = ChcExpr::eq(
        ChcExpr::Op(ChcOp::BvExtract(3, 3), vec![Arc::new(next_sum.clone())]),
        ChcExpr::BitVec(1, 1),
    );
    Terms {
        x: ctx.convert_expr(&x),
        y: ctx.convert_expr(&y),
        sum: ctx.convert_expr(&sum),
        atom: ctx.convert_expr(&atom),
        next_sum: ctx.convert_expr(&next_sum),
        next_atom: ctx.convert_expr(&next_atom),
    }
}

fn fixes(bits: &[CnfLit], value: u64) -> Vec<CnfLit> {
    bits.iter()
        .enumerate()
        .map(|(index, &lit)| if value & (1 << index) != 0 { lit } else { -lit })
        .collect()
}

fn assert_complete_models(
    cache: &PersistentBvCache,
    restored: &BvSolver<'_>,
    old_clauses: &[CnfClause],
    words: [&[CnfLit]; 4],
    predicates: [CnfLit; 2],
) {
    assert!(cache.clauses.starts_with(old_clauses));
    assert!(cache.clauses.len() > old_clauses.len());
    assert_eq!(cache.next_var, restored.num_vars() + 1);
    assert_eq!(&cache.mux_cache, restored.mux_cache());
    let circuit = cnf::Circuit::from_clauses(cache.next_var - 1, &cache.clauses);
    for a in 0..16 {
        for b in 0..16 {
            let model = circuit.propagate(&[fixes(words[0], a), fixes(words[1], b)].concat());
            let sum = (a + b) & 15;
            let next = (sum + a) & 15;
            assert_eq!(cnf::word_value(&model, words[2]), sum);
            assert_eq!(cnf::word_value(&model, words[3]), next);
            assert_eq!(cnf::bit_value(&model, predicates[0]), sum < a);
            assert_eq!(cnf::bit_value(&model, predicates[1]), next & 8 != 0);
        }
    }
}

fn assert_mux_extension(
    restored: &BvSolver<'_>,
    old_mux: &FxHashMap<(CnfLit, CnfLit, CnfLit), CnfLit>,
    old_next: u32,
) {
    for (key, output) in old_mux {
        assert_eq!(restored.mux_cache().get(key), Some(output));
    }
    for (key, output) in restored.mux_cache() {
        if !old_mux.contains_key(key) {
            assert!(
                output.unsigned_abs() >= old_next,
                "new gates cannot reuse old IDs"
            );
        }
    }
}

#[test]
#[serial_test::serial]
fn structural_restore_keeps_carry_mux_definitions_and_extends_the_full_circuit() {
    let mut first = SmtContext::new();
    let old = terms(&mut first, 0);
    let mut solver = BvSolver::new(&first.terms);
    let old_predicate = solver.bitblast_predicate(old.atom).expect("BV predicate");
    let x_bits = solver.get_term_bits(old.x).expect("x bits").to_vec();
    let y_bits = solver.get_term_bits(old.y).expect("y bits").to_vec();
    let sum_bits = solver.get_term_bits(old.sum).expect("sum bits").to_vec();
    let old_mux = solver.mux_cache().clone();
    assert!(
        !old_mux.is_empty(),
        "the addition must emit carry MUX gates"
    );
    let old_clauses = solver.clauses().to_vec();
    let old_next = solver.num_vars() + 1;
    let mut memo = FxHashMap::default();
    let mut cache = PersistentBvCache::default();
    let signature = first.bv_cache_signature(&mut cache.keys, [old.atom], &mut memo);
    assert_eq!(signature.len(), 1);
    first.capture_cached_bv_state(
        &mut cache,
        &solver,
        signature.clone(),
        &mut memo,
        old_clauses.clone(),
    );
    assert_eq!(cache.clauses, old_clauses);
    assert_eq!(cache.mux_cache, old_mux);
    assert_eq!(cache.next_var, old_next);

    let mut second = SmtContext::new();
    let new = terms(&mut second, 32);
    assert_ne!(old.x, new.x);
    assert_ne!(old.sum, new.sum);
    let roots = [new.atom, new.next_atom];
    let mut current_memo = FxHashMap::default();
    assert_eq!(
        second.bv_cache_signature(&mut cache.keys, roots, &mut current_memo),
        signature
    );
    let mut restored = BvSolver::new(&second.terms);
    second.restore_cached_bv_state(
        &mut cache,
        &mut restored,
        second.bv_subterm_closure(&roots),
        &mut current_memo,
    );
    assert_eq!(restored.get_term_bits(new.x), Some(x_bits.as_slice()));
    assert_eq!(restored.get_term_bits(new.y), Some(y_bits.as_slice()));
    assert_eq!(restored.get_term_bits(new.sum), Some(sum_bits.as_slice()));
    assert_eq!(restored.num_vars() + 1, old_next);
    assert_eq!(restored.mux_cache(), &old_mux);
    assert!(
        restored.clauses().is_empty(),
        "retained CNF lives in the cache"
    );

    // Remove only the arithmetic result memo to force the actual gate-cache
    // path. Rebuilding it must hit the saved carry MUX keys, not just the term.
    let mut term_bits = restored.term_to_bits().clone();
    assert!(term_bits.remove(&new.sum).is_some());
    restored.set_term_to_bits(term_bits);
    assert_eq!(restored.ensure_term_bits(new.sum), Some(sum_bits.clone()));
    assert_eq!(restored.num_vars() + 1, old_next);
    assert_eq!(restored.clauses(), []);
    assert_eq!(restored.mux_cache(), &old_mux);
    assert_eq!(restored.bitblast_predicate(new.atom), Some(old_predicate));

    let new_predicate = restored
        .bitblast_predicate(new.next_atom)
        .expect("new BV atom");
    let next_bits = restored
        .get_term_bits(new.next_sum)
        .expect("new sum bits")
        .to_vec();
    assert!(restored.num_vars() + 1 > old_next);
    assert!(next_bits.iter().any(|lit| lit.unsigned_abs() >= old_next));
    assert_mux_extension(&restored, &old_mux, old_next);
    let delta = restored.take_clauses();
    assert_ne!(delta, [] as [ay_core::CnfClause; 0]);
    // The real caller replays/recaptures old clauses followed by the new delta.
    // capture_cached_bv_state takes this complete circuit, not delta alone.
    let mut complete = cache.clauses.clone();
    complete.extend(delta);
    second.capture_cached_bv_state(
        &mut cache,
        &restored,
        signature,
        &mut current_memo,
        complete,
    );
    assert_complete_models(
        &cache,
        &restored,
        &old_clauses,
        [&x_bits, &y_bits, &sum_bits, &next_bits],
        [old_predicate, new_predicate],
    );
}
