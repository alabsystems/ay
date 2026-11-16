// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-bit facts of a word equality between `@bbterm` words.

use super::clean::bb_equal;
use super::helpers::{eq_step, project, transfer};
use super::proof::{Proof, S};

/// From `(cl (= W1 W2))`, the steps `(cl (= a_i b_i))` for every bit.
pub(crate) fn bit_facts(p: &mut Proof<'_>, eq: S) -> Option<Vec<S>> {
    let e = p.unit(eq);
    let (w1, w2) = (p.t.args(e)[0], p.t.args(e)[1]);
    let (b1, b2) = (p.t.bits(w1), p.t.bits(w2));
    let conj = bb_equal(&mut p.t, &b1, &b2);
    let be = eq_step(p, e, conj, "bitblast_equal", &[]);
    let cj = transfer(p, be, eq)?;
    if b1.len() == 1 {
        return Some(vec![cj]);
    }
    (0..b1.len()).map(|i| project(p, cj, i)).collect()
}
