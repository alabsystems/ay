// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by the crate root to preserve private item DefPaths.

enum PreparedWeights {
    Unweighted,
    Real(Vec<BigRational>),
    Complex(Vec<(BigRational, BigRational)>),
}

fn prepare_weights(
    instance: &Instance,
    warnings: &mut Vec<String>,
) -> Result<PreparedWeights, parse::ParseError> {
    match instance.ptype {
        ProblemType::Mc | ProblemType::Pmc => Ok(PreparedWeights::Unweighted),
        ProblemType::Wmc | ProblemType::Pwmc => {
            let projected_mask = projection_mask(instance)?;
            let resolved = parse::resolve_real_weights(
                instance.num_vars,
                &instance.weights,
                projected_mask.as_deref(),
            )?;
            warnings.extend(resolved.warnings);
            Ok(PreparedWeights::Real(resolved.weights))
        }
        ProblemType::AmcComplex => {
            let resolved = parse::resolve_complex_weights(instance.num_vars, &instance.weights)?;
            warnings.extend(resolved.warnings);
            Ok(PreparedWeights::Complex(resolved.weights))
        }
    }
}

fn projection_mask(instance: &Instance) -> Result<Option<Vec<bool>>, parse::ParseError> {
    let Some(show) = &instance.show else {
        return Ok(None);
    };
    let mut mask = Vec::new();
    mask.try_reserve_exact(instance.num_vars).map_err(|error| {
        parse::ParseError(format!(
            "could not reserve projection mask for {} variables: {error}",
            instance.num_vars
        ))
    })?;
    mask.resize(instance.num_vars, false);
    for &variable in show {
        let Some(index) = (variable as usize).checked_sub(1) else {
            return Err(parse::ParseError(
                "projection variable 0 is outside the valid range".into(),
            ));
        };
        let Some(entry) = mask.get_mut(index) else {
            return Err(parse::ParseError(format!(
                "projection variable {variable} is outside 1..={}",
                instance.num_vars
            )));
        };
        *entry = true;
    }
    Ok(Some(mask))
}

fn no_value_outcome(
    ptype: ProblemType,
    mut warnings: Vec<String>,
    warning: String,
) -> SolveOutcome {
    warnings.push(warning);
    SolveOutcome {
        ptype,
        satisfiable: None,
        value: None,
        warnings,
        stats: None,
    }
}

fn format_error_outcome(
    ptype: ProblemType,
    warnings: Vec<String>,
    error: parse::ParseError,
) -> SolveOutcome {
    no_value_outcome(ptype, warnings, format!("format error: {error}"))
}
