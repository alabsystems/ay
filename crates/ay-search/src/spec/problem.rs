// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `spec.rs`; keep items here in `ay_search::spec`.

impl SearchProblem {
    /// Return the optional diagnostic name from the source specification.
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    /// Borrow the validated constraint model.
    ///
    /// The returned model contains variables, labels, and constraints. The
    /// SearchSpec objective and execution limits remain properties of this
    /// [`SearchProblem`] and are applied by [`Self::run`] or [`Self::to_smt2`].
    pub fn model(&self) -> &Model {
        &self.model
    }

    /// Execute the mode selected by the specification.
    ///
    /// An objective selects optimization, `limits.max_solutions` selects
    /// capped enumeration, and otherwise this performs one satisfaction solve.
    /// A timeout is a global wall-clock budget for the selected operation.
    ///
    /// # Errors
    ///
    /// Returns a typed [`SearchError`] when backend preparation, execution, or
    /// independent result validation fails.
    pub fn run(&self) -> Result<SearchRunResult, SearchError> {
        let options = SolveOptions {
            timeout: self.limits.timeout_ms.map(Duration::from_millis),
        };
        if let Some((sense, objective)) = &self.objective {
            let result = match sense {
                ObjectiveSense::Minimize => self
                    .model
                    .minimize_with_options(objective.clone(), options)?,
                ObjectiveSense::Maximize => self
                    .model
                    .maximize_with_options(objective.clone(), options)?,
            };
            return Ok(SearchRunResult::Optimization(result));
        }
        if let Some(max_solutions) = self.limits.max_solutions {
            let cap = usize::try_from(max_solutions).map_err(|_| SearchError::InvalidLimit {
                name: "max_solutions",
                value: max_solutions,
            })?;
            return Ok(SearchRunResult::Enumeration(
                self.model.enumerate(Some(cap), options)?,
            ));
        }
        Ok(SearchRunResult::Solve(
            self.model.solve_with_options(options)?,
        ))
    }

    /// Render exact standalone SMT-LIB 2 for this problem.
    ///
    /// An optional optimization objective is inserted before `check-sat`.
    /// Timeout and enumeration policy are execution metadata and are omitted.
    ///
    /// # Errors
    ///
    /// Returns a typed rendering error or [`SearchError::SmtOutputTooLarge`]
    /// when the conservative output bound exceeds
    /// [`MAX_SEARCH_SPEC_SMT_BYTES`].
    pub fn to_smt2(&self) -> Result<String, SearchError> {
        let mut estimated_bytes = self.model.smt2_size_upper_bound();
        if let Some((sense, objective)) = &self.objective {
            let command = match sense {
                ObjectiveSense::Minimize => "minimize",
                ObjectiveSense::Maximize => "maximize",
            };
            estimated_bytes = estimated_bytes.saturating_add(
                self.model
                    .expression_smt_size_upper_bound(objective)?
                    .saturating_add(command.len() as u128)
                    // `(` + command + space + expression + `)` + newline.
                    .saturating_add(4),
            );
        }
        if estimated_bytes > u128::from(MAX_SEARCH_SPEC_SMT_BYTES) {
            return Err(SearchError::SmtOutputTooLarge {
                estimated_bytes,
                limit: MAX_SEARCH_SPEC_SMT_BYTES,
            });
        }

        let mut smt = self.model.to_smt2()?;
        if let Some((sense, objective)) = &self.objective {
            let command = match sense {
                ObjectiveSense::Minimize => "minimize",
                ObjectiveSense::Maximize => "maximize",
            };
            let rendered = self.model.expression_to_smt(objective)?;
            let insertion = format!("({command} {rendered})\n");
            if let Some(position) = smt.find("(check-sat)\n") {
                smt.insert_str(position, &insertion);
            }
        }
        Ok(smt)
    }
}

fn resolve_variable(name: &str, model: &Model) -> Result<crate::IntVar, SearchError> {
    model
        .variable(name)
        .ok_or_else(|| SearchError::UnknownVariable(name.to_owned()))
}

fn resolve_variables(names: &[String], model: &Model) -> Result<Vec<crate::IntVar>, SearchError> {
    names
        .iter()
        .map(|name| resolve_variable(name, model))
        .collect()
}
