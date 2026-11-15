// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn map_vector_and_arc_conversion_have_an_exact_preallocation_allowance() {
    let token = CancellationToken::new();
    let count = 3;
    let bytes = 2 * count * std::mem::size_of::<QuantifiedChcClauseOrigin>() + 64;
    let exact = Control::with_limits(&token, count, bytes);
    assert!(reserve(count, &exact).is_ok());
    let short = Control::with_limits(&token, count, bytes - 1);
    assert!(reserve(count, &short).is_err());
    assert!(short.poll().is_err());
    let short_work = Control::with_limits(&token, count - 1, bytes);
    assert!(reserve(count, &short_work).is_err());
    assert!(short_work.poll().is_err());
    let fresh = Control::with_limits(&token, count, bytes);
    assert!(reserve(count, &fresh).is_ok());
}

#[test]
fn every_origin_publication_poll_refuses_without_a_partial_map() {
    let source = duplicate_source(false);
    let token = CancellationToken::new();
    let setup = Control::new(Instant::now() + Duration::from_secs(60), &token);
    let census = copy::Census::new(&source, &setup).unwrap();
    let plan = plan::plans(&source, &setup).unwrap().remove(0);
    let selected = plan::cone(&source, &plan, &census.definitions, &setup).unwrap();
    let obligations = rows(&source);
    let obligation = &obligations[0];
    let live = Control::new(Instant::now() + Duration::from_secs(60), &token);
    assert!(seal(
        &source,
        &plan,
        &selected,
        obligation.problem(),
        obligation.id().clause_origins().to_vec(),
        &live
    )
    .is_ok());
    let calls = live.calls.get();
    assert!(calls > 3 && calls < 100);
    for stop in 1..=calls {
        let control = Control::new(Instant::now() + Duration::from_secs(60), &token);
        control.stop_at.set(Some(stop));
        assert!(seal(
            &source,
            &plan,
            &selected,
            obligation.problem(),
            obligation.id().clause_origins().to_vec(),
            &control
        )
        .is_err());
        control.stop_at.set(None);
        assert!(control.poll().is_err());
    }
    assert_eq!(rows(&source)[0].id(), obligation.id());
}
