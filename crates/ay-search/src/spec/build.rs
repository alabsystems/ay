// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `spec.rs`; keep items here in `ay_search::spec`.

impl SearchSpec {
    /// Decode the strict version-1 JSON shape without semantic validation.
    ///
    /// This method has no whole-document byte limit. Untrusted C callers are
    /// bounded by the C ABI before parsing; Rust callers that accept untrusted
    /// documents should impose an appropriate transport limit themselves.
    /// Version, identifiers, domains, references, limits, and expressions are
    /// validated by [`Self::build`].
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::Json`] when the input is malformed, omits a
    /// required field, contains an unknown field, or does not match a schema
    /// variant.
    pub fn from_json(input: &str) -> Result<Self, SearchError> {
        Ok(serde_json::from_str(input)?)
    }

    /// Validate the specification and construct its executable search plan.
    ///
    /// Validation is deterministic: version and limits are checked first,
    /// followed by variables, constraints, and finally the objective. This
    /// resolves every named reference and parses every restricted expression.
    /// Backend preparation and execution remain fallible operations on the
    /// returned [`SearchProblem`].
    ///
    /// # Errors
    ///
    /// Returns a typed [`SearchError`] for unsupported versions, invalid
    /// limits or execution modes, invalid variables or domains, unresolved
    /// references, malformed constraints, or invalid restricted expressions.
    pub fn build(&self) -> Result<SearchProblem, SearchError> {
        let limits = validate_header_and_limits(self)?;

        let mut model = Model::new();
        for variable in &self.variables {
            add_variable(&mut model, variable)?;
        }
        for constraint in &self.constraints {
            add_constraint(&mut model, constraint)?;
        }
        let objective = build_objective(self.objective.as_ref(), &model)?;

        Ok(SearchProblem {
            name: self.name.clone(),
            model,
            objective,
            limits,
        })
    }

    /// Build and lower this specification to standalone SMT-LIB 2.
    ///
    /// The output includes an optimization objective when present. Timeout and
    /// enumeration policy affect execution only and are not rendered.
    ///
    /// # Errors
    ///
    /// Returns any validation error from [`Self::build`] or an SMT rendering
    /// error, including [`SearchError::SmtOutputTooLarge`].
    pub fn to_smt2(&self) -> Result<String, SearchError> {
        self.build()?.to_smt2()
    }
}

fn validate_header_and_limits(spec: &SearchSpec) -> Result<LimitsSpec, SearchError> {
    if spec.version != 1 {
        return Err(SearchError::UnsupportedVersion(spec.version));
    }
    let limits = spec.limits.clone().unwrap_or_default();
    if limits.timeout_ms == Some(0) {
        return Err(SearchError::InvalidLimit {
            name: "timeout_ms",
            value: 0,
        });
    }
    if limits.max_solutions == Some(0) {
        return Err(SearchError::InvalidLimit {
            name: "max_solutions",
            value: 0,
        });
    }
    if let Some(max_solutions) = limits.max_solutions {
        if max_solutions > MAX_SEARCH_SPEC_SOLUTIONS {
            return Err(SearchError::InvalidLimit {
                name: "max_solutions",
                value: max_solutions,
            });
        }
        let cells = u128::from(max_solutions).saturating_mul(spec.variables.len() as u128);
        if cells > u128::from(MAX_SEARCH_SPEC_RESULT_CELLS) {
            return Err(SearchError::EnumerationResultTooLarge {
                cells,
                limit: MAX_SEARCH_SPEC_RESULT_CELLS,
            });
        }
        let estimated_bytes = enumeration_result_json_upper_bound(&spec.variables, max_solutions);
        if estimated_bytes > u128::from(MAX_SEARCH_SPEC_RESULT_BYTES) {
            return Err(SearchError::EnumerationOutputTooLarge {
                estimated_bytes,
                limit: MAX_SEARCH_SPEC_RESULT_BYTES,
            });
        }
    }
    if spec.objective.is_some() && limits.max_solutions.is_some() {
        return Err(SearchError::ConflictingExecutionModes);
    }
    Ok(limits)
}

fn add_variable(model: &mut Model, variable: &VariableSpec) -> Result<(), SearchError> {
    let domain = match &variable.domain {
        DomainSpec::Interval { min, max } => Domain::interval(*min, *max)?,
        DomainSpec::Values { values } => Domain::values(values.iter().copied())?,
    };
    let handle = model.int_var(variable.name.clone(), domain)?;
    for (&value, label) in &variable.labels {
        model.set_choice_label(handle, value, label.clone())?;
    }
    Ok(())
}

fn add_constraint(model: &mut Model, constraint: &ConstraintSpec) -> Result<(), SearchError> {
    match constraint {
        ConstraintSpec::Expression { expression } => {
            let (lhs, relation, rhs) = parse_relation(expression, model)?;
            match relation {
                ParsedRelation::Eq => model.eq(lhs, rhs)?,
                ParsedRelation::Le => model.le(lhs, rhs)?,
                ParsedRelation::Ge => model.ge(lhs, rhs)?,
                ParsedRelation::Ne => model.ne(lhs, rhs)?,
            }
        }
        ConstraintSpec::AllDifferent { all_different } => {
            let variables = resolve_variables(all_different, model)?;
            model.all_different(&variables)?;
        }
        ConstraintSpec::Table { table } => {
            let variables = resolve_variables(&table.variables, model)?;
            model.table(&variables, &table.tuples)?;
        }
        ConstraintSpec::Element { element } => {
            let index = resolve_variable(&element.index, model)?;
            let array = resolve_variables(&element.array, model)?;
            let result = resolve_variable(&element.result, model)?;
            model.element(index, &array, result)?;
        }
    }
    Ok(())
}

fn build_objective(
    objective: Option<&ObjectiveSpec>,
    model: &Model,
) -> Result<Option<(ObjectiveSense, LinearExpr)>, SearchError> {
    objective
        .map(|objective| {
            Ok((
                objective.sense,
                parse_linear_expression(&objective.expression, model)?,
            ))
        })
        .transpose()
}

/// Conservative byte bound for serde_json's compact serialization of an
/// enumeration result. Container constants intentionally include slack so a
/// future status spelling or punctuation adjustment cannot invalidate the
/// bound without a structural serialization change.
fn enumeration_result_json_upper_bound(variables: &[VariableSpec], max_solutions: u64) -> u128 {
    const RESULT_CONTAINER_BYTES: u128 = 64;
    const SOLUTION_CONTAINER_BYTES: u128 = 64;
    const I64_DECIMAL_BYTES: u128 = 20;

    let mut solution_bytes = SOLUTION_CONTAINER_BYTES;
    for variable in variables {
        let name_bytes = json_string_bytes(&variable.name);
        // Assignment map entry: quoted name, colon, signed i64, and a comma.
        solution_bytes = solution_bytes
            .saturating_add(name_bytes)
            .saturating_add(1 + I64_DECIMAL_BYTES + 1);

        // At most one choice label is selected for a variable in a solution.
        // Charge the longest possible serialized label plus the repeated name.
        if let Some(label_bytes) = variable
            .labels
            .values()
            .map(|label| json_string_bytes(label))
            .max()
        {
            solution_bytes = solution_bytes
                .saturating_add(name_bytes)
                .saturating_add(1)
                .saturating_add(label_bytes)
                .saturating_add(1);
        }
    }

    RESULT_CONTAINER_BYTES
        .saturating_add(u128::from(max_solutions).saturating_mul(solution_bytes.saturating_add(1)))
}

/// Exact compact serde_json string size for the escape set used by serde_json:
/// quotes/backslashes and five short control escapes take two bytes, remaining
/// ASCII controls take six, and all other UTF-8 bytes pass through unchanged.
fn json_string_bytes(value: &str) -> u128 {
    let content_bytes = value.as_bytes().iter().fold(0u128, |length, byte| {
        let escaped = match byte {
            b'"' | b'\\' | b'\x08' | b'\t' | b'\n' | b'\x0c' | b'\r' => 2,
            0x00..=0x1f => 6,
            _ => 1,
        };
        length.saturating_add(escaped)
    });
    content_bytes.saturating_add(2)
}
