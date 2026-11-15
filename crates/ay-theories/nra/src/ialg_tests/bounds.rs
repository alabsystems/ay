// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn ialg_bounds() -> Result<(), Box<dyn std::error::Error>> {
    // Normalisation refuses more than MAX_INTERVALS inputs before any work.
    let many: Vec<AInterval> = (0..=(MAX_INTERVALS as i64))
        .map(|i| {
            let lo = i.checked_mul(3)?;
            let hi = lo.checked_add(1)?;
            Some(iv(fin(ri(lo)), false, fin(ri(hi)), false))
        })
        .collect::<Option<_>>()
        .ok_or("interval endpoints fit i64")?;
    assert_eq!(many.len(), MAX_INTERVALS + 1);
    assert_eq!(IntervalSet::normalize(many), None);

    // A justification cannot grow past MAX_JUST.
    let a = Just {
        lits: (1..=(MAX_JUST as i32)).collect(),
    };
    let b = Just::of(-1).expect("nonzero");
    assert_eq!(a.merge(&b), None);
    assert!(a.merge(&Just::of(1).expect("nonzero")).is_some());

    // from_sign_condition refuses a root list that would exceed the ceiling.
    let p = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    let roots: Vec<Anum> = (0..MAX_INTERVALS as i64).map(ri).collect();
    assert_eq!(
        from_sign_condition(&p, &roots, SignCond::Lt, Just::none()),
        None
    );
    Ok(())
}
