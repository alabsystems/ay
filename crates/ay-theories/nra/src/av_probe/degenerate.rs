// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Degenerate cases, hand-built, that a random sweep may under-sample.
#[cfg(test)]
fn assert_degenerate_half_lines(a1: &Anum, a2: &Anum) {
    let lower_open = nonempty(DecidedInterval::from_bounds(
        AEnd::NegInf,
        true,
        end(a1),
        true,
        Just::of(1).unwrap(),
    ));
    let upper_open = nonempty(DecidedInterval::from_bounds(
        end(a2),
        true,
        AEnd::PosInf,
        true,
        Just::of(2).unwrap(),
    ));
    let lower_closed = nonempty(DecidedInterval::from_bounds(
        AEnd::NegInf,
        true,
        end(a1),
        false,
        Just::of(1).unwrap(),
    ));
    let upper_closed = nonempty(DecidedInterval::from_bounds(
        end(a2),
        false,
        AEnd::PosInf,
        true,
        Just::of(2).unwrap(),
    ));

    let set = IntervalSet::normalize(vec![lower_open.clone(), upper_open.clone()]).unwrap();
    assert_eq!(
        set.len(),
        2,
        "an open/open pair at a shared algebraic point was wrongly merged"
    );
    assert_eq!(set.contains(a1), Some(false));
    assert_eq!(set.contains(a2), Some(false));

    let set = IntervalSet::normalize(vec![lower_closed.clone(), upper_open.clone()]).unwrap();
    assert_eq!(set.len(), 1, "adjacent closed/open pair not merged");
    assert_eq!(set.contains(a1), Some(true));
    let set = IntervalSet::normalize(vec![lower_open.clone(), upper_closed.clone()]).unwrap();
    assert_eq!(set.len(), 1);
    assert_eq!(set.contains(a2), Some(true));
    let set = IntervalSet::normalize(vec![lower_closed.clone(), upper_closed.clone()]).unwrap();
    assert_eq!(set.len(), 1);

    let lower_set = IntervalSet::normalize(vec![lower_closed.clone()]).unwrap();
    let upper_set = IntervalSet::normalize(vec![upper_closed.clone()]).unwrap();
    let intersection = lower_set.intersect(&upper_set).unwrap();
    assert!(
        !intersection.is_empty(),
        "LOST the singleton {{a}} — a conflict that should not exist"
    );
    assert_eq!(intersection.len(), 1);
    assert_eq!(intersection.contains(a1), Some(true));
    let justification = intersection.justification().unwrap();
    assert!(
        justification.lits().contains(&1) && justification.lits().contains(&2),
        "justification dropped a side"
    );

    let lower_open_set = IntervalSet::normalize(vec![lower_open]).unwrap();
    let upper_open_set = IntervalSet::normalize(vec![upper_open]).unwrap();
    assert!(
        lower_open_set
            .intersect(&upper_open_set)
            .unwrap()
            .is_empty(),
        "(-inf,a) n (a,inf) is not empty"
    );

    let complement = lower_set.complement().unwrap();
    assert_eq!(complement.contains(a1), Some(false));
    assert_eq!(
        complement.complement().unwrap().same_set_as(&lower_set),
        Some(true)
    );
}

#[cfg(test)]
fn assert_degenerate_infinities(a1: &Anum) {
    let full = IntervalSet::full(Just::none());
    assert!(full.complement().unwrap().is_empty());
    assert!(IntervalSet::empty()
        .complement()
        .unwrap()
        .same_set_as(&full)
        .unwrap());
    assert!(
        DecidedInterval::from_bounds(AEnd::NegInf, false, end(a1), true, Just::none()).is_none()
    );
    assert!(
        DecidedInterval::from_bounds(end(a1), true, AEnd::PosInf, false, Just::none()).is_none()
    );
    assert!(
        DecidedInterval::from_bounds(AEnd::PosInf, true, end(a1), true, Just::none())
            .expect("infinities are ordered")
            .into_interval()
            .is_none()
    );
    assert!(
        DecidedInterval::from_bounds(end(a1), true, AEnd::NegInf, true, Just::none())
            .expect("infinities are ordered")
            .into_interval()
            .is_none()
    );
}

#[test]
fn av_degenerate_cases() {
    let a1 = sq(10);
    let a2 = sq_via(10, 5, 3, 4);
    assert_eq!(a1.cmp_anum(&a2), Some(Ordering::Equal));

    for (lo, hi) in [(&a1, &a2), (&a2, &a1), (&a1, &a1)] {
        assert!(
            DecidedInterval::from_bounds(end(lo), true, end(hi), true, Just::none())
                .expect("equal endpoints are comparable")
                .into_interval()
                .is_none(),
            "(a,a) not proved empty",
        );
        assert!(
            DecidedInterval::from_bounds(end(lo), true, end(hi), false, Just::none())
                .expect("equal endpoints are comparable")
                .into_interval()
                .is_none(),
            "(a,a] not proved empty",
        );
        assert!(
            DecidedInterval::from_bounds(end(lo), false, end(hi), true, Just::none())
                .expect("equal endpoints are comparable")
                .into_interval()
                .is_none(),
            "[a,a) not proved empty",
        );
    }

    let singleton = DecidedInterval::from_bounds(end(&a1), false, end(&a2), false, Just::none())
        .expect("equal endpoints are comparable")
        .into_interval()
        .expect("[a,a] wrongly empty — LOST CONFLICT / WRONG UNSAT");
    assert_eq!(singleton.contains(&a1), Some(true));
    assert_eq!(singleton.contains(&a2), Some(true));
    let singleton = IntervalSet::normalize(vec![singleton]).unwrap();
    assert!(!singleton.is_empty());
    assert_eq!(singleton.len(), 1);
    assert_eq!(
        singleton.pick().map(|value| value.cmp_anum(&a1)),
        Some(Some(Ordering::Equal))
    );

    assert_degenerate_half_lines(&a1, &a2);
    assert_degenerate_infinities(&a1);
    println!("AV-DEGENERATE: all degenerate shapes behave");
}
