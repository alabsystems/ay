// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{add_up, mul_up, support_term, Axis, BoxHullCut};

// Embedded rounding affects this operation only. Every lane encloses a sum
// over a disjoint subset of the sparse coordinates, including signed products.
#[target_feature(enable = "avx512f")]
pub(super) unsafe fn directed_support(
    axes: &[Axis],
    point: &[f64],
    left: f64,
    right: f64,
    value: f64,
) -> Option<BoxHullCut> {
    use std::arch::x86_64::*;
    const UP: i32 = _MM_FROUND_TO_POS_INF | _MM_FROUND_NO_EXC;
    let mut sum_l = _mm512_setzero_pd();
    let mut sum_r = _mm512_setzero_pd();
    let mut dot = _mm512_setzero_pd();
    let mut terms = Vec::with_capacity(axes.len());
    let mut chunks = axes.chunks_exact(8);
    let step = _mm512_setr_epi64(0, 4, 8, 12, 16, 20, 24, 28);
    for block in chunks.by_ref() {
        // Axis is a repr(C) tuple of one 64-bit index and three binary64s
        // on x86-64. The eight gather indices select the same field from
        // eight consecutive initialized elements.
        const { assert!(std::mem::size_of::<Axis>() == 32) };
        let bytes = block.as_ptr().cast::<u8>();
        let (indices, a, b, s) = unsafe {
            (
                _mm512_i64gather_epi64::<8>(
                    step,
                    bytes.add(std::mem::offset_of!(Axis, index)).cast(),
                ),
                _mm512_i64gather_pd::<8>(step, bytes.add(std::mem::offset_of!(Axis, left)).cast()),
                _mm512_i64gather_pd::<8>(step, bytes.add(std::mem::offset_of!(Axis, right)).cast()),
                _mm512_i64gather_pd::<8>(step, bytes.add(std::mem::offset_of!(Axis, slope)).cast()),
            )
        };
        // Every axis originates in an already range-checked sparse arm.
        let x = unsafe { _mm512_i64gather_pd::<8>(indices, point.as_ptr()) };
        let dl = _mm512_sub_round_pd::<UP>(_mm512_max_pd(a, s), _mm512_min_pd(a, s));
        let dr = _mm512_sub_round_pd::<UP>(_mm512_max_pd(b, s), _mm512_min_pd(b, s));
        sum_l = _mm512_add_round_pd::<UP>(sum_l, dl);
        sum_r = _mm512_add_round_pd::<UP>(sum_r, dr);
        dot = _mm512_add_round_pd::<UP>(dot, _mm512_mul_round_pd::<UP>(s, x));
        for a in block {
            if !a.slope.is_finite() {
                return None;
            }
            if a.slope != 0.0 {
                terms.push((a.index, a.slope));
            }
        }
    }
    let reduce = |initial, sum| {
        let mut lanes = [0.0; 8];
        unsafe {
            _mm512_storeu_pd(lanes.as_mut_ptr(), sum);
        }
        lanes.into_iter().fold(initial, add_up)
    };
    let mut left = reduce(left, sum_l);
    let mut right = reduce(right, sum_r);
    let mut at = reduce(0.0, dot);
    for a in chunks.remainder() {
        if !a.slope.is_finite() {
            return None;
        }
        left = add_up(left, support_term(a.left, a.slope));
        right = add_up(right, support_term(a.right, a.slope));
        if a.slope != 0.0 {
            terms.push((a.index, a.slope));
            at = add_up(at, mul_up(a.slope, point[a.index]));
        }
    }
    let offset = left.max(right);
    let upper = add_up(offset, at);
    (offset.is_finite() && upper.is_finite() && value > upper)
        .then_some(BoxHullCut { offset, terms })
}
