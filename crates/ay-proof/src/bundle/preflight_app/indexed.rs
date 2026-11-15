// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[derive(Clone, Copy)]
enum Rule {
    Extract,
    Extend,
    Rotate,
    Repeat,
}

const RULES: &[(&str, Rule)] = &[
    ("extract", Rule::Extract),
    ("zero_extend", Rule::Extend),
    ("sign_extend", Rule::Extend),
    ("rotate_left", Rule::Rotate),
    ("rotate_right", Rule::Rotate),
    ("repeat", Rule::Repeat),
];

pub(super) fn validate(app: &mut App<'_, '_>, indices: &[u32]) -> Result<(), ProofCheckError> {
    for &(name, rule) in RULES {
        if app.named(name)? {
            return bitvector(app, indices, rule);
        }
    }
    if names::requires_named(app)? {
        return app.invalid("must be a named symbol without indices");
    }
    for name in ["+zero", "-zero", "+oo", "-oo", "NaN"] {
        if app.named(name)? {
            return floating_literal(app, indices);
        }
    }
    Ok(())
}

fn bitvector(app: &mut App<'_, '_>, indices: &[u32], rule: Rule) -> Result<(), ProofCheckError> {
    app.charge(1, 0)?;
    let expected_indices = if matches!(rule, Rule::Extract) { 2 } else { 1 };
    if app.args.len() != 1 || indices.len() != expected_indices {
        return app.invalid("has an invalid number of indices or arguments");
    }
    let Sort::BitVec(input) = app.arg(0)? else {
        return app.invalid("operand is not a bit-vector");
    };
    let Sort::BitVec(result) = app.result else {
        return app.invalid("result is not a bit-vector");
    };
    app.charge(expected_indices, 0)?;
    let expected_width = match rule {
        Rule::Extract => {
            let (high, low) = (indices[0], indices[1]);
            if low > high || high >= input.width {
                return app.invalid("indices are outside the operand width");
            }
            // high<input.width<=u32::MAX proves high-low+1 cannot overflow.
            high - low + 1
        }
        Rule::Extend => {
            let Some(width) = input.width.checked_add(indices[0]) else {
                return app.invalid("result width overflows");
            };
            width
        }
        Rule::Rotate => input.width,
        Rule::Repeat => {
            if indices[0] == 0 {
                return app.invalid("count must be positive");
            }
            let Some(width) = input.width.checked_mul(indices[0]) else {
                return app.invalid("result width overflows");
            };
            width
        }
    };
    if result.width != expected_width {
        return app.invalid("records an inconsistent result width");
    }
    Ok(())
}

fn floating_literal(app: &mut App<'_, '_>, indices: &[u32]) -> Result<(), ProofCheckError> {
    let Sort::FloatingPoint(exponent, significand) = app.result else {
        return app.invalid("indexed floating-point literal is not floating-point sorted");
    };
    app.charge(3, 0)?;
    if !app.args.is_empty()
        || indices.len() != 2
        || indices[0] != *exponent
        || indices[1] != *significand
    {
        return app.invalid("indexed floating-point literal has inconsistent indices or arguments");
    }
    Ok(())
}
