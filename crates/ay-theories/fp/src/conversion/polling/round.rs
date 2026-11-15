// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Same rounding gate sequence, separated into conversion-only owned phases.

use crate::construction::control::BuildControl;
use crate::{FpDecomposed, FpPrecision, FpSolver, RmOperand};
use ay_core::CnfLit;

#[derive(Clone, Copy)]
pub(super) struct Format {
    pub eb: usize,
    pub sb: usize,
    pub bias: u64,
    pub w: usize,
}

pub(super) struct Prepared {
    pub ovf1_exp: CnfLit,
    pub tiny: CnfLit,
    pub e_min_bv: Vec<CnfLit>,
    pub beta: Vec<CnfLit>,
    pub sigma: Vec<CnfLit>,
}

pub(super) struct Normalized {
    pub ovf1_exp: CnfLit,
    pub norm_sig: Vec<CnfLit>,
    pub norm_exp: Vec<CnfLit>,
}

pub(super) struct PostRound {
    pub ovf1_exp: CnfLit,
    pub sig_ovf: CnfLit,
    pub post_sig: Vec<CnfLit>,
    pub biased_exp: Vec<CnfLit>,
}

impl FpSolver<'_> {
    pub(crate) fn conversion_round_with_control<C: BuildControl>(
        &mut self,
        precision: FpPrecision,
        rm: RmOperand,
        sgn: CnfLit,
        sig: &[CnfLit],
        exp: &[CnfLit],
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        self.conversion_poll(control)?;
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;
        let bias = u64::from(precision.bias());
        let w = exp.len();
        debug_assert_eq!(sig.len(), sb + 4, "sig must be sbits+4 wide");
        debug_assert!(w >= eb + 2, "exp must be at least ebits+2 wide");
        let format = Format { eb, sb, bias, w };
        let prepared = self.conversion_round_prepare(format, sig, exp, control)?;
        let normalized = self.conversion_round_normalize(format, sig, prepared, control)?;
        let post = self.conversion_round_post(format, rm, sgn, normalized, control)?;
        self.conversion_round_finish(precision, format, rm, sgn, post, control)
    }
}
