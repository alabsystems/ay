// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conversion-only copies of the existing priority encoder and barrel stages.

use crate::construction::control::BuildControl;
use crate::FpSolver;
use ay_core::CnfLit;

impl FpSolver<'_> {
    pub(crate) fn conversion_lz_with_control<C: BuildControl>(
        &mut self,
        bits: &[CnfLit],
        result_width: usize,
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        self.conversion_poll(control)?;
        let n = bits.len();
        if n == 0 {
            let result = self.const_bv(0, result_width);
            self.conversion_poll(control)?;
            return Ok(result);
        }
        let mut lz = self.const_bv(n as u64, result_width);
        for i in 0..n {
            self.conversion_poll(control)?;
            let bit = bits[i];
            let count = n - 1 - i;
            let count_bv = self.const_bv(count as u64, result_width);
            lz = self.make_ite_bits(bit, &count_bv, &lz);
            drop(count_bv);
            self.conversion_poll(control)?;
        }
        self.conversion_poll(control)?;
        Ok(lz)
    }

    pub(crate) fn conversion_lshr_with_control<C: BuildControl>(
        &mut self,
        a: &[CnfLit],
        b: &[CnfLit],
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        self.conversion_poll(control)?;
        let n = a.len();
        let zero = self.const_false();
        let mut current = a.to_vec();
        for i in 0..b.len() {
            self.conversion_poll(control)?;
            let b_bit = b[i];
            let shift_amount = match 1usize.checked_shl(i as u32) {
                Some(v) => v,
                None => n,
            };
            if shift_amount >= n {
                let overflow = self.bv_or_reduce(&b[i..]);
                let all_zero = vec![zero; n];
                current = self.make_ite_bits(overflow, &all_zero, &current);
                drop(all_zero);
                self.conversion_poll(control)?;
                break;
            }
            let mut shifted = Vec::new();
            let _ = shifted.try_reserve_exact(n);
            for j in 0..n {
                match j.checked_add(shift_amount).and_then(|k| current.get(k)) {
                    Some(&bit) => shifted.push(bit),
                    None => shifted.push(zero),
                }
            }
            current = self.make_ite_bits(b_bit, &shifted, &current);
            drop(shifted);
            self.conversion_poll(control)?;
        }
        self.conversion_poll(control)?;
        Ok(current)
    }
}
