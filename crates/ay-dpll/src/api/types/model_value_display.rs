// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Display formatting for `ModelValue` and array store chains.

use num_bigint::BigInt;

use super::{FpSpecialKind, ModelValue};

impl std::fmt::Display for ModelValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(n) => write!(f, "{}", crate::executor_format::format_bigint(n)),
            Self::Real(r) => write!(f, "{}", crate::executor_format::format_rational(r)),
            Self::BitVec { value, width } => {
                // Convert to unsigned representation for hex display
                let hex_digits = (*width as usize).div_ceil(4);
                let modulus = BigInt::from(1) << *width;
                let unsigned_val = ((value % &modulus) + &modulus) % &modulus;
                write!(
                    f,
                    "#x{:0>width$}",
                    format!("{:x}", unsigned_val),
                    width = hex_digits
                )
            }
            Self::String(s) => {
                // SMT-LIB 2.6 string literal escaping, matching z3's convention:
                //   - `"` doubles to `""`
                //   - printable ASCII (0x20..=0x7E, incl. backslash) prints literally
                //   - every other code point prints as `\u{X}` where X is the
                //     lowercase, minimal-digit hex code point (e.g. `\u{3b1}`).
                write!(f, "\"")?;
                for c in s.chars() {
                    match c {
                        '"' => write!(f, "\"\"")?, // SMT-LIB uses "" for escaped quote
                        c if ('\u{20}'..='\u{7e}').contains(&c) => write!(f, "{c}")?,
                        c => write!(f, "\\u{{{:x}}}", c as u32)?,
                    }
                }
                write!(f, "\"")
            }
            Self::Uninterpreted(s) => write!(f, "{s}"),
            Self::ArraySmtlib(s) => write!(f, "{s}"),
            Self::Array { default, stores } => fmt_array(f, default, stores),
            Self::FloatingPoint {
                sign,
                exponent,
                significand,
                eb,
                sb,
            } => {
                let sign_bit = u64::from(*sign);
                write!(
                    f,
                    "(fp #b{sign_bit} #b{exponent:0>eb$b} #b{significand:0>sb$b})",
                    eb = *eb as usize,
                    sb = (*sb as usize).saturating_sub(1)
                )
            }
            Self::FloatingPointSpecial { kind, eb, sb } => {
                let name = match kind {
                    FpSpecialKind::PosZero => "+zero",
                    FpSpecialKind::NegZero => "-zero",
                    FpSpecialKind::PosInf => "+oo",
                    FpSpecialKind::NegInf => "-oo",
                    FpSpecialKind::NaN => "NaN",
                };
                write!(f, "(_ {name} {eb} {sb})")
            }
            Self::Datatype {
                constructor, args, ..
            } => {
                if args.is_empty() {
                    write!(f, "{constructor}")
                } else {
                    write!(f, "({constructor}")?;
                    for arg in args {
                        write!(f, " {arg}")?;
                    }
                    write!(f, ")")
                }
            }
            Self::Seq(elements) => {
                if elements.is_empty() {
                    write!(f, "seq.empty")
                } else if elements.len() == 1 {
                    write!(f, "(seq.unit {})", elements[0])
                } else {
                    for _ in 0..elements.len() - 1 {
                        write!(f, "(seq.++ ")?;
                    }
                    write!(f, "(seq.unit {})", elements[0])?;
                    for elem in &elements[1..] {
                        write!(f, " (seq.unit {elem}))")?;
                    }
                    Ok(())
                }
            }
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

/// Format a structured array as a store chain: `(store (store ... default i1 v1) i2 v2)`.
pub(super) fn fmt_array(
    f: &mut std::fmt::Formatter<'_>,
    default: &ModelValue,
    stores: &[(ModelValue, ModelValue)],
) -> std::fmt::Result {
    if stores.is_empty() {
        return write!(f, "{default}");
    }
    let mut inner = format!("{default}");
    for (idx, val) in stores {
        inner = format!("(store {inner} {idx} {val})");
    }
    write!(f, "{inner}")
}
