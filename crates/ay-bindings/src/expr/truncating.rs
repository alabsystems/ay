// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Capture-free standard-SMT expansion of Rust/fmod's truncating remainder.
//! Original operands occur once, in simultaneous outer let right-hand sides.
//! The generated body contains only its fixed distinct local names. Even an
//! original free name equal to a local is therefore outside that local's scope.

use super::Expr;
use std::fmt;

pub(super) fn display(f: &mut fmt::Formatter<'_>, a: &Expr, b: &Expr) -> fmt::Result {
    write!(f, "(let ((ay_fp_fmod_x {a}) (ay_fp_fmod_y {b})) ")?;
    f.write_str("(let ((ay_fp_fmod_r (fp.rem ay_fp_fmod_x ay_fp_fmod_y))) ")?;
    f.write_str("(ite (and (not (fp.isNaN ay_fp_fmod_r)) ")?;
    f.write_str("(not (fp.isZero ay_fp_fmod_r)) ")?;
    f.write_str("(xor (fp.isNegative ay_fp_fmod_r) (fp.isNegative ay_fp_fmod_x))) ")?;
    f.write_str("(fp.add RNE ay_fp_fmod_r ")?;
    f.write_str("(ite (fp.isNegative ay_fp_fmod_x) ")?;
    f.write_str("(fp.neg (fp.abs ay_fp_fmod_y)) (fp.abs ay_fp_fmod_y))) ")?;
    f.write_str("ay_fp_fmod_r)))")
}

#[cfg(test)]
mod tests;
