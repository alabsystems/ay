// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Degree of `p` in variable `v`, for the degree report.
pub(crate) fn degree_in(p: &MPolyZ, v: MVar) -> u32 {
    p.terms()
        .iter()
        .map(|(m, _)| {
            m.pairs()
                .iter()
                .find(|&&(w, _)| w == v)
                .map_or(0, |&(_, e)| e)
        })
        .max()
        .unwrap_or(0)
}

/// The sign of a polynomial's leading coefficient or zero for a zero input.
pub(crate) fn lc_sign(p: &[BigInt]) -> i32 {
    match p.iter().rev().find(|c| !c.is_zero()) {
        Some(c) if c.is_negative() => -1,
        Some(_) => 1,
        None => 0,
    }
}
