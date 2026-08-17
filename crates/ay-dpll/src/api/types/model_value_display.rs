// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Display formatting for `ModelValue` and array store chains.

use std::fmt;

use super::{FpSpecialKind, ModelValue};

impl fmt::Display for ModelValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(n) => write!(f, "{}", crate::executor_format::format_bigint(n)),
            Self::Real(r) => write!(f, "{}", crate::executor_format::format_rational(r)),
            // Delegate to the canonical BV-numeral printer: `#x` is well-formed
            // only at widths that are a multiple of 4, otherwise `#b` is
            // required, or the printed value silently reparses at the wrong
            // width (e.g. `(_ BitVec 5)` value 17 as `#x11`, i.e. 8 bits).
            Self::BitVec { value, width } => {
                write!(
                    f,
                    "{}",
                    crate::executor_format::format_bitvec(value, *width)
                )
            }
            Self::String(s) => fmt_string(f, s),
            Self::Uninterpreted(s) => write!(f, "{s}"),
            Self::ArraySmtlib(s) => write!(f, "{s}"),
            Self::Array { default, stores } => fmt_array(f, default, stores),
            Self::FloatingPoint {
                sign,
                exponent,
                significand,
                eb,
                sb,
            } => fmt_floating_point(f, sign, exponent, significand, eb, sb),
            Self::FloatingPointSpecial { kind, eb, sb } => fmt_fp_special(f, kind, eb, sb),
            Self::Datatype {
                constructor, args, ..
            } => fmt_datatype(f, constructor, args),
            Self::Seq(elements) => fmt_seq(f, elements),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

fn fmt_string(f: &mut fmt::Formatter<'_>, value: &str) -> fmt::Result {
    // SMT-LIB 2.6 string literal escaping, matching z3's convention:
    //   - `"` doubles to `""`
    //   - printable ASCII (0x20..=0x7E, incl. backslash) prints literally
    //   - every other code point prints as `\u{X}` where X is the lowercase,
    //     minimal-digit hex code point (e.g. `\u{3b1}`).
    write!(f, "\"")?;
    for c in value.chars() {
        match c {
            '"' => write!(f, "\"\"")?, // SMT-LIB uses "" for escaped quote
            c if ('\u{20}'..='\u{7e}').contains(&c) => write!(f, "{c}")?,
            c => write!(f, "\\u{{{:x}}}", c as u32)?,
        }
    }
    write!(f, "\"")
}

fn fmt_floating_point(
    f: &mut fmt::Formatter<'_>,
    sign: &bool,
    exponent: &u64,
    significand: &u64,
    eb: &u32,
    sb: &u32,
) -> fmt::Result {
    let sign_bit = u64::from(*sign);
    write!(
        f,
        "(fp #b{sign_bit} #b{exponent:0>eb$b} #b{significand:0>sb$b})",
        eb = *eb as usize,
        sb = (*sb as usize).saturating_sub(1)
    )
}

fn fmt_fp_special(
    f: &mut fmt::Formatter<'_>,
    kind: &FpSpecialKind,
    eb: &u32,
    sb: &u32,
) -> fmt::Result {
    let name = match kind {
        FpSpecialKind::PosZero => "+zero",
        FpSpecialKind::NegZero => "-zero",
        FpSpecialKind::PosInf => "+oo",
        FpSpecialKind::NegInf => "-oo",
        FpSpecialKind::NaN => "NaN",
    };
    write!(f, "(_ {name} {eb} {sb})")
}

fn fmt_datatype(f: &mut fmt::Formatter<'_>, constructor: &str, args: &[ModelValue]) -> fmt::Result {
    if args.is_empty() {
        return write!(f, "{constructor}");
    }
    write!(f, "({constructor}")?;
    for arg in args {
        write!(f, " {arg}")?;
    }
    write!(f, ")")
}

fn fmt_seq(f: &mut fmt::Formatter<'_>, elements: &[ModelValue]) -> fmt::Result {
    if elements.is_empty() {
        return write!(f, "seq.empty");
    }
    if elements.len() == 1 {
        return write!(f, "(seq.unit {})", elements[0]);
    }
    for _ in 0..elements.len() - 1 {
        write!(f, "(seq.++ ")?;
    }
    write!(f, "(seq.unit {})", elements[0])?;
    for elem in &elements[1..] {
        write!(f, " (seq.unit {elem}))")?;
    }
    Ok(())
}

/// Format a structured array as a store chain: `(store (store ... default i1 v1) i2 v2)`.
pub(super) fn fmt_array(
    f: &mut fmt::Formatter<'_>,
    default: &ModelValue,
    stores: &[(ModelValue, ModelValue)],
) -> fmt::Result {
    if stores.is_empty() {
        return write!(f, "{default}");
    }
    let mut inner = format!("{default}");
    for (idx, val) in stores {
        inner = format!("(store {inner} {idx} {val})");
    }
    write!(f, "{inner}")
}
