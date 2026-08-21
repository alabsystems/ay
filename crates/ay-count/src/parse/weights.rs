// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `parse` so the public items retain their DefPaths.

/// Resolved real-weight table plus diagnostics from the format's defaulting
/// rules. A missing complement of `0 < w < 1` becomes `1-w`; an entirely
/// missing pair defaults to `1`; every other one-sided pair is an error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedWeights {
    /// Per-literal weights. Variable `v` (1-based) uses index `2*(v-1)` for
    /// its positive literal and the following index for its negative literal.
    pub weights: Vec<BigRational>,
    /// Format and compatibility warnings emitted during resolution.
    pub warnings: Vec<String>,
}

/// Resolve real weights for `wmc`/`pwmc`.
///
/// When `projected` is present, it must contain exactly `num_vars` entries.
/// Declarations for variables whose entry is `false` are diagnosed and
/// ignored after the complete declaration set has been checked for conflicts.
///
/// # Errors
///
/// Returns [`ParseError`] when `num_vars` exceeds the engine cap; the dense
/// table size overflows or cannot be reserved; a literal is zero or outside
/// `1..=num_vars`; the projection mask has the wrong length; a complex weight
/// appears in a real instance; duplicate declarations conflict; or a lone
/// polarity cannot be completed under the competition rules. The aggregate
/// expanded representation of `raw` must fit the weight-memory budget.
pub fn resolve_real_weights(
    num_vars: usize,
    raw: &[(i32, RawWeight)],
    projected: Option<&[bool]>,
) -> Result<ResolvedWeights, ParseError> {
    let slot_count = validate_weight_inputs(num_vars, raw, projected)?;
    for (lit, weight) in raw {
        if matches!(weight, RawWeight::Complex(_, _)) {
            return err(format!(
                "complex weight on literal {lit} in a real-weighted instance"
            ));
        }
    }
    let mut declared = empty_weight_slots(slot_count)?;
    for (lit, weight) in raw {
        let RawWeight::Rat(weight) = weight else {
            return err(format!(
                "complex weight on literal {lit} in a real-weighted instance"
            ));
        };
        let slot = literal_slot(*lit, num_vars)?;
        insert_declaration(&mut declared[slot], weight.clone(), *lit)?;
    }

    let mut warnings = Vec::new();
    if let Some(mask) = projected {
        apply_projection_mask(&mut declared, raw, mask, num_vars, &mut warnings)?;
    }
    resolve_real_slots(num_vars, slot_count, declared, warnings)
}

fn resolve_real_slots(
    num_vars: usize,
    slot_count: usize,
    given: Vec<Option<BigRational>>,
    mut warnings: Vec<String>,
) -> Result<ResolvedWeights, ParseError> {
    let one: BigRational = One::one();
    let mut weights = reserved_values(slot_count, "resolved real-weight table")?;
    for var in 0..num_vars {
        let pos = given[var * 2].clone();
        let neg = given[var * 2 + 1].clone();
        let (positive, negative) = complete_real_pair(var, pos, neg, &one, &mut warnings)?;
        if positive.is_zero() {
            warnings.push(format!("weight of literal {} is 0", var + 1));
        }
        if negative.is_zero() {
            warnings.push(format!("weight of literal -{} is 0", var + 1));
        }
        weights.push(positive);
        weights.push(negative);
    }
    Ok(ResolvedWeights { weights, warnings })
}

fn complete_real_pair(
    var: usize,
    positive: Option<BigRational>,
    negative: Option<BigRational>,
    one: &BigRational,
    warnings: &mut Vec<String>,
) -> Result<(BigRational, BigRational), ParseError> {
    match (positive, negative) {
        (Some(positive), Some(negative)) => Ok((positive, negative)),
        (None, None) => Ok((one.clone(), one.clone())),
        (Some(positive), None) if positive.is_positive() && positive < *one => {
            let negative = one - &positive;
            warnings.push(format!(
                "weight for literal -{} not given; set to 1-w = {negative}",
                var + 1
            ));
            Ok((positive, negative))
        }
        (None, Some(negative)) if negative.is_positive() && negative < *one => {
            let positive = one - &negative;
            warnings.push(format!(
                "weight for literal {} not given; set to 1-w = {positive}",
                var + 1
            ));
            Ok((positive, negative))
        }
        (Some(weight), None) => err(format!(
            "weight {weight} for literal {} requires the complement weight to be given",
            var + 1
        )),
        (None, Some(weight)) => err(format!(
            "weight {weight} for literal -{} requires the complement weight to be given",
            var + 1
        )),
    }
}

fn apply_projection_mask(
    given: &mut [Option<BigRational>],
    raw: &[(i32, RawWeight)],
    projected: &[bool],
    num_vars: usize,
    warnings: &mut Vec<String>,
) -> Result<(), ParseError> {
    for &(lit, _) in raw {
        let var = validate_literal(lit, num_vars, "weight literal")?;
        if !projected[var] {
            warnings.push(format!(
                "weight given for non-projection variable {}; ignored",
                var + 1
            ));
        }
    }
    for (var, &is_projected) in projected.iter().enumerate() {
        if !is_projected {
            given[var * 2] = None;
            given[var * 2 + 1] = None;
        }
    }
    Ok(())
}

/// Resolved complex weights for `amc-complex`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedComplexWeights {
    /// Per-literal `(real, imaginary)` weights, using the positive-then-negative
    /// indexing convention documented by [`ResolvedWeights::weights`].
    pub weights: Vec<(BigRational, BigRational)>,
    /// Format and compatibility warnings emitted during resolution.
    pub warnings: Vec<String>,
}

/// Resolve complex weights.
///
/// Untouched variables default to `1+0i` for both polarities. Declaring only
/// one polarity is a format error; real declarations are interpreted as
/// complex values with a zero imaginary component.
///
/// # Errors
///
/// Returns [`ParseError`] when `num_vars` exceeds the engine cap; the dense
/// table size overflows or cannot be reserved; a literal is zero or outside
/// `1..=num_vars`; duplicate declarations conflict; or exactly one polarity
/// of a variable is declared. The aggregate expanded representation of `raw`
/// must fit the weight-memory budget.
pub fn resolve_complex_weights(
    num_vars: usize,
    raw: &[(i32, RawWeight)],
) -> Result<ResolvedComplexWeights, ParseError> {
    let slot_count = validate_weight_inputs(num_vars, raw, None)?;
    let mut given = empty_weight_slots(slot_count)?;
    for (lit, weight) in raw {
        let value = match weight {
            RawWeight::Rat(real) => (real.clone(), BigRational::zero()),
            RawWeight::Complex(real, imaginary) => (real.clone(), imaginary.clone()),
        };
        let slot = literal_slot(*lit, num_vars)?;
        insert_declaration(&mut given[slot], value, *lit)?;
    }
    resolve_complex_slots(num_vars, slot_count, given)
}

fn resolve_complex_slots(
    num_vars: usize,
    slot_count: usize,
    given: Vec<Option<(BigRational, BigRational)>>,
) -> Result<ResolvedComplexWeights, ParseError> {
    let mut weights = reserved_values(slot_count, "resolved complex-weight table")?;
    let mut warnings = Vec::new();
    for var in 0..num_vars {
        let pair = match (given[var * 2].clone(), given[var * 2 + 1].clone()) {
            (Some(positive), Some(negative)) => (positive, negative),
            (None, None) => (
                (One::one(), BigRational::zero()),
                (One::one(), BigRational::zero()),
            ),
            _ => {
                return err(format!(
                    "algebraic instance gives a weight for only one polarity of variable {}",
                    var + 1
                ));
            }
        };
        if pair.0 .0.is_zero() && pair.0 .1.is_zero() {
            warnings.push(format!("weight of literal {} is 0", var + 1));
        }
        if pair.1 .0.is_zero() && pair.1 .1.is_zero() {
            warnings.push(format!("weight of literal -{} is 0", var + 1));
        }
        weights.push(pair.0);
        weights.push(pair.1);
    }
    Ok(ResolvedComplexWeights { weights, warnings })
}

fn validate_weight_inputs(
    num_vars: usize,
    raw: &[(i32, RawWeight)],
    projected: Option<&[bool]>,
) -> Result<usize, ParseError> {
    validate_num_vars(num_vars)?;
    if let Some(mask) = projected {
        if mask.len() != num_vars {
            return err(format!(
                "projection mask has length {}, expected {num_vars}",
                mask.len()
            ));
        }
    }
    for &(lit, _) in raw {
        validate_literal(lit, num_vars, "weight literal")?;
    }
    validate_total_weight_bits(raw)?;
    num_vars.checked_mul(2).ok_or_else(|| {
        ParseError(format!(
            "weight table size overflows for {num_vars} variables"
        ))
    })
}

fn literal_slot(lit: i32, num_vars: usize) -> Result<usize, ParseError> {
    let var = validate_literal(lit, num_vars, "weight literal")?;
    var.checked_mul(2)
        .and_then(|base| base.checked_add(usize::from(lit < 0)))
        .ok_or_else(|| ParseError(format!("weight-table index overflows for literal {lit}")))
}

fn empty_weight_slots<T>(slot_count: usize) -> Result<Vec<Option<T>>, ParseError> {
    let mut slots = Vec::new();
    slots.try_reserve_exact(slot_count).map_err(|error| {
        ParseError(format!(
            "could not reserve {slot_count} weight-table slots: {error}"
        ))
    })?;
    slots.resize_with(slot_count, || None);
    Ok(slots)
}

fn reserved_values<T>(slot_count: usize, what: &str) -> Result<Vec<T>, ParseError> {
    let mut values = Vec::new();
    values.try_reserve_exact(slot_count).map_err(|error| {
        ParseError(format!(
            "could not reserve {slot_count} entries for {what}: {error}"
        ))
    })?;
    Ok(values)
}

fn insert_declaration<T: PartialEq>(
    slot: &mut Option<T>,
    value: T,
    literal: i32,
) -> Result<(), ParseError> {
    match slot {
        Some(previous) if *previous != value => err(format!(
            "conflicting duplicate weight for literal {literal}"
        )),
        Some(_) => Ok(()),
        None => {
            *slot = Some(value);
            Ok(())
        }
    }
}
