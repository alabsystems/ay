// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FIPS180-4 §6.2.2; all additions intentionally modulo 2^32.

use super::{constants::K, Control, QueryError};

pub(super) fn compress<C: Control>(
    state: &mut [u32; 8],
    block: &[u8; 64],
    control: &mut C,
) -> Result<(), QueryError> {
    // First iterator/header steps are offered before schedule initialization.
    control.offer(64, 0)?;
    control.offer(512, 256)?;
    let mut words = [0u32; 64];
    for index in 0..16 {
        control.offer(128, 0)?;
        let base = 4 * index;
        words[index] = ((block[base] as u32) << 24)
            | ((block[base + 1] as u32) << 16)
            | ((block[base + 2] as u32) << 8)
            | block[base + 3] as u32;
    }
    for index in 16..64 {
        control.offer(192, 0)?;
        let x = words[index - 15];
        let y = words[index - 2];
        let low = x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3);
        let high = y.rotate_right(17) ^ y.rotate_right(19) ^ (y >> 10);
        words[index] = words[index - 16]
            .wrapping_add(low)
            .wrapping_add(words[index - 7])
            .wrapping_add(high);
    }
    control.offer(128, 32)?;
    let mut working = *state;
    for index in 0..64 {
        // The 32-byte successor state is a logical newly constructed record.
        control.offer(256, 32)?;
        let [a, b, c, d, e, f, g, h] = working;
        let sum1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let choose = (e & f) ^ (!e & g);
        let first = h
            .wrapping_add(sum1)
            .wrapping_add(choose)
            .wrapping_add(K[index])
            .wrapping_add(words[index]);
        let sum0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let majority = (a & b) ^ (a & c) ^ (b & c);
        let second = sum0.wrapping_add(majority);
        working = [
            first.wrapping_add(second),
            a,
            b,
            c,
            d.wrapping_add(first),
            e,
            f,
            g,
        ];
    }
    for index in 0..8 {
        control.offer(32, 0)?;
        state[index] = state[index].wrapping_add(working[index]);
    }
    control.offer(0, 0)
}
