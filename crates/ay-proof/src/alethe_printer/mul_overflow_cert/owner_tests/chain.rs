// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::chain::Chain;
use super::super::proof::Proof;
use super::super::term::Sort;
use super::EmissionProgress;
use std::cell::Cell;

fn run_projection(p: &mut Proof<'_>) -> Option<super::super::chain::ChainResult> {
    let x = p.t.var("x", Sort::Bool);
    let chain = Chain {
        bounds: vec![vec![x], vec![x]],
        ..Chain::default()
    };
    chain.run(p)
}

#[test]
fn chain_projection_uses_the_original_owner_without_retry() {
    let calls = Cell::new(0);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    let mut p = Proof::new_with_progress(
        "t1.mo".into(),
        "@w".into(),
        EmissionProgress::with_caller(&mut accepting),
    );
    let healthy = run_projection(&mut p).expect("both input states are reachable");
    assert_eq!(healthy.outputs.len(), 1);
    assert_eq!(healthy.finals.as_slice(), &[] as &[u32]);
    assert!(calls.get() > 1);
    for stop_at in 1..=calls.get() {
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let mut candidate = Proof::new_with_progress("t1.mo".into(), "@w".into(), owner.clone());
        assert!(run_projection(&mut candidate).is_none());
        assert_eq!(seen.get(), stop_at);
        let remaining = candidate.budget;
        assert!(run_projection(&mut candidate).is_none());
        assert_eq!(candidate.budget, remaining);
        assert_eq!(seen.get(), stop_at);
        assert!(owner.refused());
    }
}
