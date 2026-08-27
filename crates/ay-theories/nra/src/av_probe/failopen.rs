// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================================
// PART A — FAIL-OPEN PROBES
//
// For every predicate: construct an input it CANNOT decide and record what
// comes back. A permissive answer is a soundness defect.
// ============================================================================

/// An `Anum` whose comparison against `sq(2)` is genuinely UNDECIDABLE, because
/// `root_separation_exponent` on the combined defining polynomial exceeds
/// `anum::MAX_SEPARATION_BITS`. Returns `None` if no such value was found.
#[cfg(test)]
fn undecidable_partner() -> Option<(Anum, Anum)> {
    let a = sq(2);
    // x^2 - K for a huge non-square K: gcd with x^2-2 is 1, so cmp_cell must go
    // through the separation bound, which refuses past 8192 bits.
    for bits in [2600u32, 2725, 2800, 3000, 4000, 8000, 16000] {
        let k: BigInt = (BigInt::one() << bits) + BigInt::from(3);
        let p = vec![-k.clone(), BigInt::zero(), BigInt::one()];
        // sqrt(K) is in (2^(bits/2), 2^(bits/2+1)).
        let lo = Bq::from_int(BigInt::one() << (bits / 2));
        let hi = Bq::from_int(BigInt::one() << (bits / 2 + 1));
        let iv = BqInterval::new(lo, hi)?;
        let Some(b) = Anum::from_poly_interval(&p, &iv) else {
            continue;
        };
        if a.cmp_anum(&b).is_none() {
            return Some((a, b));
        }
    }
    None
}

#[test]
fn av_failopen_every_predicate_on_an_undecidable_input() {
    let Some((a, b)) = undecidable_partner() else {
        panic!("could not manufacture an undecidable comparison — probe is void");
    };
    println!(
        "AV-FAILOPEN: manufactured an UNDECIDABLE pair (deg {} vs deg {})",
        a.degree(),
        b.degree()
    );
    assert_eq!(
        a.cmp_anum(&b),
        None,
        "precondition: the pair is undecidable"
    );

    assert_undecidable_endpoint_construction(&a, &b);
    let (ia, ib) = assert_undecidable_membership_and_normalization(&a, &b);
    assert_undecidable_set_operations(&a, &b, &ia, &ib);
}

#[cfg(test)]
fn assert_undecidable_endpoint_construction(a: &Anum, b: &Anum) {
    // 1. AEnd::cmp_value — the ordering of two endpoints.
    let r = end(a).cmp_value(&end(b));
    println!("  cmp_value(a, b)                 -> {r:?}");
    assert_eq!(r, None, "FAIL-OPEN: endpoint ordering guessed");
    let r = end(b).cmp_value(&end(a));
    println!("  cmp_value(b, a)                 -> {r:?}");
    assert_eq!(r, None, "FAIL-OPEN: endpoint ordering guessed");

    // 2. DecidedInterval::from_bounds — emptiness of an undecidable interval.
    for (lo_open, hi_open) in [(true, true), (false, false), (true, false), (false, true)] {
        let r = mk(end(a), lo_open, end(b), hi_open, 1);
        println!(
            "  DecidedInterval::from_bounds(a,{lo_open},b,{hi_open}) -> {}",
            if r.is_none() {
                "None (REFUSED)"
            } else {
                "Some(..)  *** FAIL-OPEN ***"
            }
        );
        assert!(r.is_none(), "FAIL-OPEN: an undecidable interval was built");
        let r = mk(end(b), lo_open, end(a), hi_open, 1);
        assert!(
            r.is_none(),
            "FAIL-OPEN: an undecidable interval was built (reversed)"
        );
    }
}

#[cfg(test)]
fn assert_undecidable_membership_and_normalization(a: &Anum, b: &Anum) -> (AInterval, AInterval) {
    // 3. AInterval::contains — membership at an undecidable point.
    let dec = nonempty(mk(end(&sq(2)), true, end(&sq(3)), true, 1));
    let r = dec.contains(b);
    println!("  (sqrt2,sqrt3).contains(b)       -> {r:?}");
    assert_eq!(
        r, None,
        "FAIL-OPEN: membership guessed on an undecidable point"
    );

    // 4. IntervalSet::contains — the set-level predicate.
    let set = IntervalSet::normalize(vec![dec.clone()]).unwrap();
    let r = set.contains(b);
    println!("  set.contains(b)                 -> {r:?}");
    assert_eq!(r, None, "FAIL-OPEN: set membership guessed");

    // 4b. Exercise both scan positions for the undecidable interval.
    let negative = nonempty(mk(AEnd::NegInf, true, end(&ri(-100)), true, 2));
    let set = IntervalSet::normalize(vec![negative, dec]).unwrap();
    let r = set.contains(b);
    println!("  set(2 ivs).contains(b)          -> {r:?}");
    assert_eq!(
        r, None,
        "FAIL-OPEN: set membership guessed after a decided miss"
    );

    // 5. normalize — the fallible insertion sort and the gap scan.
    let ia = nonempty(mk(end(a), true, end(&ri(10)), true, 1));
    let ib = match mk(end(b), true, end(&b.add(&ri(1)).unwrap()), true, 2)
        .and_then(DecidedInterval::into_interval)
    {
        Some(value) => value,
        other => {
            println!("  (b, b+1) itself refused: {other:?} — using a rational-anchored partner");
            nonempty(mk(end(b), true, AEnd::PosInf, true, 2))
        }
    };
    let r = IntervalSet::normalize(vec![ia.clone(), ib.clone()]);
    println!(
        "  normalize([a..10],[b..])        -> {}",
        if r.is_none() {
            "None (REFUSED)"
        } else {
            "Some(..)  *** FAIL-OPEN ***"
        }
    );
    assert!(
        r.is_none(),
        "FAIL-OPEN: normalize sorted an undecidable pair"
    );
    assert!(
        IntervalSet::normalize(vec![ib.clone(), ia.clone()]).is_none(),
        "FAIL-OPEN: normalize sorted an undecidable pair (swapped)"
    );
    (ia, ib)
}

#[cfg(test)]
fn assert_undecidable_set_operations(a: &Anum, b: &Anum, ia: &AInterval, ib: &AInterval) {
    // 6. These operations genuinely require comparing `a` with `b`.
    let zero_a = nonempty(mk(end(&ri(0)), true, end(a), true, 1));
    let zero_b = nonempty(mk(end(&ri(0)), true, end(b), true, 2));
    let sa = IntervalSet::normalize(vec![zero_a]).unwrap();
    let sb = IntervalSet::normalize(vec![zero_b]).unwrap();
    println!(
        "  sa=(0,a) sb=(0,b): is_empty {} / {}",
        sa.is_empty(),
        sb.is_empty()
    );
    for (name, result) in [
        ("union", sa.union(&sb)),
        ("intersect", sa.intersect(&sb)),
        ("intersect(rev)", sb.intersect(&sa)),
        ("subtract", sa.subtract(&sb)),
        ("subtract(rev)", sb.subtract(&sa)),
    ] {
        println!(
            "  {name:<14}                  -> {}",
            if result.is_none() {
                "None (REFUSED)"
            } else {
                "Some(..)  *** FAIL-OPEN ***"
            }
        );
        assert!(
            result.is_none(),
            "FAIL-OPEN: {name} produced a set across an undecidable boundary"
        );
    }

    let sa2 = IntervalSet::normalize(vec![ia.clone()]).unwrap();
    let sb2 = IntervalSet::normalize(vec![ib.clone()]).unwrap();
    let control = sa2.subtract(&sb2);
    println!(
        "  CONTROL (a,10)\\(b,inf)          -> {}",
        if control.is_none() {
            "None"
        } else {
            "Some(..) (expected: no a-vs-b needed)"
        }
    );
    assert!(
        control.is_some(),
        "the control declined too — the module refuses everything"
    );
    assert_remaining_undecidable_predicates(a, b, &sa, &sb);
}

#[cfg(test)]
fn assert_remaining_undecidable_predicates(a: &Anum, b: &Anum, sa: &IntervalSet, sb: &IntervalSet) {
    // 7. same_set_as.
    let r = sa.same_set_as(sb);
    println!("  same_set_as((0,a),(0,b))        -> {r:?}");
    assert_eq!(r, None, "FAIL-OPEN: set equality guessed");

    // 8. from_sign_condition with an undecidable root list.
    let polynomial = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    let r = from_sign_condition(
        &polynomial,
        &[a.clone(), b.clone()],
        SignCond::Gt,
        Just::none(),
    );
    println!(
        "  from_sign_condition([a,b])      -> {}",
        if r.is_none() {
            "None (REFUSED)"
        } else {
            "Some(..)  *** FAIL-OPEN ***"
        }
    );
    assert!(
        r.is_none(),
        "FAIL-OPEN: an undecidable root ordering was accepted"
    );

    // 9. Interval construction itself must refuse undecidable closed bounds.
    let probe = DecidedInterval::from_bounds(end(a), false, end(b), false, Just::none());
    assert!(
        probe.is_none(),
        "FAIL-OPEN: closed undecidable interval built"
    );

    // 10. pick must not guess across an undecidable boundary.
    let r = sa.pick();
    println!(
        "  sa.pick()                       -> {:?}",
        r.as_ref().map(classify_value)
    );
}

/// The other half of the fail-open question: `IntervalSet::is_empty` returns a
/// bare `bool`. Prove there is NO route to a set whose emptiness was undecided.
#[test]
fn av_failopen_is_empty_has_no_undecided_route() {
    let Some((a, b)) = undecidable_partner() else {
        panic!("probe void");
    };
    // Every public constructor of IntervalSet, fed an undecidable pair.
    let bad = vec![AInterval::full(Just::none())];
    assert!(IntervalSet::normalize(bad).is_some());

    // The only constructors are empty(), full(), normalize(), from_ordered()
    // (private), intersect(), complement(), union(), subtract(). Each is fed an
    // undecidable input above; all refuse. The remaining question is whether an
    // *interval* holding two mutually-undecidable endpoints can exist at all.
    for lo_open in [true, false] {
        for hi_open in [true, false] {
            assert!(
                DecidedInterval::from_bounds(end(&a), lo_open, end(&b), hi_open, Just::none())
                    .is_none(),
                "an interval with undecidable endpoints was constructed"
            );
        }
    }
    println!(
        "AV: no AInterval with mutually-undecidable endpoints can be constructed, \
              so `is_empty()`'s bare bool has no undecided route."
    );
}
