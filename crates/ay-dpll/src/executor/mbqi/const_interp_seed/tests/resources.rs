// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

#[test]
fn all_heads_share_work_and_large_map_probes_are_precharged() {
    let mut exec = prepared(true);
    pin_fixture(&mut exec);
    let roots = exec.ctx.assertions.clone();
    let declarations = bindings(&exec);
    let refs: Vec<_> = declarations.iter().collect();
    let deadline = ay_core::time::Instant::now() + Duration::from_secs(2);
    let mut work = 20_000;
    assert!(build(&mut exec, &roots, &refs, &mut work, deadline).is_some());
    let used = 20_000 - work;
    assert!(used > 6, "not one unmetered read per head");
    let mut insufficient = used - 1;
    assert!(build(&mut exec, &roots, &refs, &mut insufficient, deadline).is_none());
    assert!(exec.const_interp_cert_witness_state.is_none());
    exec.last_model
        .as_mut()
        .unwrap()
        .bv_model
        .as_mut()
        .unwrap()
        .values
        .reserve(32_768);
    assert!(
        seed(&mut exec).is_none(),
        "worst-case map probing is not hidden by a small selected set"
    );
    assert!(build(&mut exec, &roots, &vec![refs[0]; 33], &mut 20_000, deadline).is_none());
}

#[test]
fn depth_fanout_and_malformed_original_nodes_refuse_before_observation() {
    assert_eq!(flat(&Sort::bitvec(0)), None);
    assert_eq!(flat(&Sort::bitvec(65)), None);
    let mut exec = prepared(true);
    pin_fixture(&mut exec);
    let root = exec.ctx.assertions[0];
    let mut deep = root;
    for _ in 0..=MAX_DEPTH {
        deep = exec
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [deep], Sort::Bool);
    }
    let wide = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), vec![root; 8_000], Sort::Bool);
    let a = term(&mut exec, "a");
    let short_index = exec.ctx.terms.mk_bitvec(BigInt::from(0), 8);
    let malformed_select =
        exec.ctx
            .terms
            .mk_app(Symbol::named("select"), [a, short_index], Sort::bitvec(8));
    let malformed_uf = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [], Sort::bitvec(8));
    let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0), 8);
    for bad in [deep, wide, malformed_select, malformed_uf] {
        let bad = if flat(exec.ctx.terms.sort(bad)) == Some(FlatSort::Bool) {
            bad
        } else {
            exec.ctx
                .terms
                .mk_app(Symbol::named("="), [bad, zero], Sort::Bool)
        };
        let mut roots = exec.ctx.assertions.clone();
        roots.push(bad);
        let declarations = bindings(&exec);
        assert!(build(
            &mut exec,
            &roots,
            &declarations.iter().collect::<Vec<_>>(),
            &mut 20_000,
            ay_core::time::Instant::now() + Duration::from_secs(2)
        )
        .is_none());
    }
}

#[test]
fn lexical_sharing_is_not_a_term_only_groundness_cache() {
    let mut exec = prepared(true);
    pin_fixture(&mut exec);
    let point = term(&mut exec, "(f true x)");
    let fill = term(&mut exec, "fill");
    let body = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [point, fill], Sort::Bool);
    let bound = exec
        .ctx
        .terms
        .mk_forall(vec![("x".to_string(), Sort::bitvec(8))], body);
    let declarations = bindings(&exec);
    let refs: Vec<_> = declarations.iter().collect();
    let mut work = 20_000;
    let mut never = || false;
    let mut budget = Budget {
        remaining: &mut work,
        deadline: ay_core::time::Instant::now() + Duration::from_secs(2),
        stopped: false,
        stop: &mut never,
    };
    let mut selected = vec![None; 6];
    census(
        &exec,
        &[bound],
        &refs,
        &mut selected,
        &mut Vec::new(),
        &mut budget,
    )
    .unwrap();
    assert_eq!(
        selected[2], None,
        "the shared UF point depends on the lexical binder"
    );
    assert_eq!(
        selected[5], None,
        "the bound x is not the declaration's observation"
    );
    census(
        &exec,
        &[bound, body],
        &refs,
        &mut selected,
        &mut Vec::new(),
        &mut budget,
    )
    .unwrap();
    assert_eq!(
        selected[2],
        Some(point),
        "the same TermId is ground only in the later scope"
    );
}

#[test]
fn pre_cancel_interior_stop_deadline_and_retained_memory_never_install() {
    let mut exec = prepared(true);
    pin_fixture(&mut exec);
    let flag = Arc::new(AtomicBool::new(true));
    exec.set_interrupt(flag.clone());
    assert!(seed(&mut exec).is_none());
    flag.store(false, Ordering::Relaxed);
    // A new decision owns its own attempt; the seed itself never rearms one.
    exec.begin_external_decision_query(false);
    pin_fixture(&mut exec);
    assert!(
        seed(&mut exec).is_some(),
        "only the test's fresh decision renews the attempt"
    );
    let roots = exec.ctx.assertions.clone();
    let declarations = bindings(&exec);
    let refs: Vec<_> = declarations.iter().collect();
    let mut calls = 0;
    assert!(build_with_stop(
        &mut exec,
        &roots,
        &refs,
        &mut 20_000,
        ay_core::time::Instant::now() + Duration::from_secs(2),
        &mut || {
            calls += 1;
            calls == 9
        }
    )
    .is_none());
    assert_eq!(
        calls, 9,
        "an observed one-shot stop is not polled again or demoted"
    );
    assert!(exec.const_interp_cert_witness_state.is_none());
    assert!(build(
        &mut exec,
        &roots,
        &refs,
        &mut 20_000,
        ay_core::time::Instant::now()
    )
    .is_none());
    exec.record_evaluation_stop(crate::executor_types::UnknownOrigin::MemoryBudget);
    assert!(seed(&mut exec).is_none());
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(crate::executor_types::UnknownOrigin::MemoryBudget)
    );
}

#[test]
fn stale_or_foreign_declarations_refuse_before_literal_materialization() {
    let mut exec = prepared(true);
    pin_fixture(&mut exec);
    let roots = exec.ctx.assertions.clone();
    let declarations = bindings(&exec);
    let mut other = prepared(true);
    pin_fixture(&mut other);
    let other_roots = other.ctx.assertions.clone();
    let before = other.ctx.terms.len();
    assert!(build(
        &mut other,
        &other_roots,
        &declarations.iter().collect::<Vec<_>>(),
        &mut 20_000,
        ay_core::time::Instant::now() + Duration::from_secs(2)
    )
    .is_none());
    assert_eq!(other.ctx.terms.len(), before);
    exec.execute_all(&ay_frontend::parse("(push 1)").unwrap())
        .unwrap();
    assert!(build(
        &mut exec,
        &roots,
        &declarations.iter().collect::<Vec<_>>(),
        &mut 20_000,
        ay_core::time::Instant::now() + Duration::from_secs(2)
    )
    .is_none());
}
