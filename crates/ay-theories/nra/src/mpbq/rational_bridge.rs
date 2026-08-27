// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// The smallest dyadic interval with `k`-bit endpoints that contains `(lo, hi)`.
/// Both bounds are rounded outward, so the bridge cannot drop a root.
pub(crate) fn enclose_rational(lo: &BigRational, hi: &BigRational, k: u32) -> Option<BqInterval> {
    if lo >= hi || k > MAX_SELECT_K {
        return None;
    }
    let scale = BigInt::one() << k;
    let l = (lo.numer() * &scale).div_floor(lo.denom());
    let h = ceil_div(&(hi.numer() * &scale), hi.denom());
    BqInterval::new(Bq::new(l, k), Bq::new(h, k))
}

/// `ceil(n / d)` for `d > 0`.
fn ceil_div(n: &BigInt, d: &BigInt) -> BigInt {
    let (q, r) = n.div_rem(d);
    if r.is_zero() || r.is_negative() {
        q
    } else {
        q + 1
    }
}
