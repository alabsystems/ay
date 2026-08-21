// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `parse` so the public function and impl retain their DefPaths.

impl Instance {
    /// Validate the invariants required by the counting engine.
    ///
    /// Parsed instances already satisfy these invariants. This method is
    /// primarily for callers that construct or mutate the public fields.
    ///
    /// # Errors
    ///
    /// Returns [`ParseError`] when the variable count exceeds the engine cap;
    /// the public fields contradict the selected problem type; a clause or
    /// weight contains zero or an out-of-range literal; or the projection list
    /// contains zero, an out-of-range variable, or a duplicate. The aggregate
    /// expanded representation of all raw weights must also fit the parser's
    /// memory budget.
    pub fn validate(&self) -> Result<(), ParseError> {
        validate_num_vars(self.num_vars)?;
        self.validate_track_state()?;
        for (clause_index, clause) in self.clauses.iter().enumerate() {
            for &lit in clause {
                validate_literal(lit, self.num_vars, "clause literal")
                    .map_err(|error| ParseError(format!("clause {}: {error}", clause_index + 1)))?;
            }
        }
        if let Some(show) = &self.show {
            let mut seen = Vec::new();
            seen.try_reserve_exact(self.num_vars).map_err(|error| {
                ParseError(format!(
                    "could not reserve projection-validation table for {} variables: {error}",
                    self.num_vars
                ))
            })?;
            seen.resize(self.num_vars, false);
            for &var in show {
                if var == 0 || var as usize > self.num_vars {
                    return err(format!(
                        "projection variable {var} is outside 1..={}",
                        self.num_vars
                    ));
                }
                let index = var as usize - 1;
                if seen[index] {
                    return err(format!(
                        "projection variable {var} is listed more than once"
                    ));
                }
                seen[index] = true;
            }
        }
        for &(lit, _) in &self.weights {
            validate_literal(lit, self.num_vars, "weight literal")?;
        }
        validate_total_weight_bits(&self.weights)?;
        Ok(())
    }

    fn validate_track_state(&self) -> Result<(), ParseError> {
        match self.ptype {
            ProblemType::Mc => {
                if self.show.is_some() {
                    return err("mc instances cannot contain a projection set");
                }
                if !self.weights.is_empty() {
                    return err("mc instances cannot contain weights");
                }
            }
            ProblemType::Wmc => {
                if self.show.is_some() {
                    return err("wmc instances cannot contain a projection set");
                }
            }
            ProblemType::Pmc => {
                if !self.weights.is_empty() {
                    return err("pmc instances cannot contain weights");
                }
                if self.show.is_none() {
                    return err("pmc instances require a projection set");
                }
            }
            ProblemType::Pwmc => {
                if self.show.is_none() {
                    return err("pwmc instances require a projection set");
                }
            }
            ProblemType::AmcComplex => {
                if self.show.is_some() {
                    return err("amc-complex instances cannot contain a projection set");
                }
            }
        }
        Ok(())
    }
}

/// Parse a complete MC-2026 instance from text.
///
/// The parser accepts a final unterminated clause with a warning and accepts a
/// weight line both with and without its conventional final `0`. Projection
/// lines always require a final `0`; neither record form accepts trailing junk.
/// An absent show record on `pmc`/`pwmc` denotes the empty projection.
///
/// # Errors
///
/// Returns [`ParseError`] for malformed records, conflicting type lines,
/// identifiers outside the declared variable range, excess clauses, missing
/// required terminators, unsupported projected AMC, or a variable count above
/// the counting-engine cap. Weight tokens must remain proportional to their
/// expanded integer representation and fit the aggregate weight-memory budget.
pub fn parse_instance(content: &str) -> Result<Instance, ParseError> {
    let mut parser = InstanceParser::default();
    for (line_index, raw_line) in content.lines().enumerate() {
        parser.parse_line(line_index + 1, raw_line.trim())?;
    }
    parser.finish()
}

#[derive(Default)]
struct InstanceParser {
    num_vars: Option<usize>,
    declared_clauses: usize,
    clauses: Vec<Vec<i32>>,
    current_clause: Vec<i32>,
    explicit_type: Option<ProblemType>,
    show_vars: Vec<u32>,
    saw_show: bool,
    weights: Vec<(i32, RawWeight)>,
    expanded_weight_bits: u64,
    warnings: Vec<String>,
}

impl InstanceParser {
    fn parse_line(&mut self, line_no: usize, line: &str) -> Result<(), ParseError> {
        if line.is_empty() {
            return Ok(());
        }
        if let Some(rest) = line.strip_prefix('p') {
            return self.parse_problem_line(line_no, line, rest);
        }
        if line.starts_with('c') {
            return self.parse_comment_line(line_no, line);
        }
        self.parse_clause_line(line_no, line)
    }

    fn parse_problem_line(
        &mut self,
        line_no: usize,
        line: &str,
        rest: &str,
    ) -> Result<(), ParseError> {
        if self.num_vars.is_some() {
            return err(format!("duplicate `p` line at line {line_no}"));
        }
        let mut tokens = rest.split_whitespace();
        if tokens.next() != Some("cnf") {
            return err(format!(
                "malformed problem line at line {line_no}: `{line}`"
            ));
        }
        let n_token = tokens.next().ok_or_else(|| {
            ParseError(format!(
                "malformed problem line at line {line_no}: `{line}`"
            ))
        })?;
        let m_token = tokens.next().ok_or_else(|| {
            ParseError(format!(
                "malformed problem line at line {line_no}: `{line}`"
            ))
        })?;
        let n: usize = n_token
            .parse()
            .map_err(|_| ParseError(format!("invalid variable count at line {line_no}")))?;
        validate_num_vars(n)?;
        let m: usize = m_token
            .parse()
            .map_err(|_| ParseError(format!("invalid clause count at line {line_no}")))?;
        // Additional header metadata is tolerated for compatibility with the
        // projected-count example's `p cnf n m k` form.
        self.num_vars = Some(n);
        self.declared_clauses = m;
        Ok(())
    }

    fn parse_comment_line(&mut self, line_no: usize, line: &str) -> Result<(), ParseError> {
        let mut tokens = line.split_whitespace();
        if tokens.next() != Some("c") {
            return Ok(());
        }
        match tokens.next() {
            Some("t") => {
                if let Some(token) = tokens.next() {
                    self.parse_type(line_no, token)?;
                }
            }
            Some("p") => match tokens.next() {
                Some("show") => self.parse_show(line_no, tokens)?,
                Some("weight") => self.parse_weight_line(line_no, tokens)?,
                _ => {}
            },
            _ => {}
        }
        Ok(())
    }

    fn parse_type(&mut self, line_no: usize, token: &str) -> Result<(), ParseError> {
        let problem_type = ProblemType::from_token(token).ok_or_else(|| {
            ParseError(format!(
                "unsupported problem type `{token}` at line {line_no}"
            ))
        })?;
        if let Some(previous) = self.explicit_type {
            if previous != problem_type {
                return err(format!(
                    "conflicting `c t` lines: {} then {}",
                    previous.as_str(),
                    problem_type.as_str()
                ));
            }
        }
        self.explicit_type = Some(problem_type);
        Ok(())
    }

    fn parse_show<'a>(
        &mut self,
        line_no: usize,
        mut tokens: impl Iterator<Item = &'a str>,
    ) -> Result<(), ParseError> {
        self.saw_show = true;
        while let Some(token) = tokens.next() {
            if token == "0" {
                if let Some(trailing) = tokens.next() {
                    return err(format!(
                        "projection line {line_no} has trailing token `{trailing}` after terminating 0"
                    ));
                }
                return Ok(());
            }
            let var: u32 = token.parse().map_err(|_| {
                ParseError(format!(
                    "invalid projection variable `{token}` at line {line_no}"
                ))
            })?;
            if var == 0 {
                return err(format!("projection variable 0 at line {line_no}"));
            }
            self.show_vars.push(var);
        }
        err(format!("projection line {line_no} missing terminating 0"))
    }

    fn parse_weight_line<'a>(
        &mut self,
        line_no: usize,
        mut tokens: impl Iterator<Item = &'a str>,
    ) -> Result<(), ParseError> {
        let Some(lit_token) = tokens.next() else {
            return err(format!("malformed weight line at line {line_no}"));
        };
        let Some(weight_token) = tokens.next() else {
            return err(format!("malformed weight line at line {line_no}"));
        };
        if let Some(terminator) = tokens.next() {
            if terminator != "0" {
                return err(format!(
                    "weight line {line_no} has unexpected trailing token `{terminator}`"
                ));
            }
            if let Some(trailing) = tokens.next() {
                return err(format!(
                    "weight line {line_no} has trailing token `{trailing}` after terminating 0"
                ));
            }
        }
        let lit: i32 = lit_token.parse().map_err(|_| {
            ParseError(format!(
                "invalid weight literal `{lit_token}` at line {line_no}"
            ))
        })?;
        if lit == 0 {
            return err(format!("weight literal 0 at line {line_no}"));
        }
        let weight = parse_weight(weight_token)
            .map_err(|error| ParseError(format!("line {line_no}: {error}")))?;
        self.expanded_weight_bits =
            charge_parsed_weight(self.expanded_weight_bits, weight_token.len(), &weight)
                .map_err(|error| ParseError(format!("line {line_no}: {error}")))?;
        self.weights.push((lit, weight));
        Ok(())
    }

    fn parse_clause_line(&mut self, line_no: usize, line: &str) -> Result<(), ParseError> {
        let Some(num_vars) = self.num_vars else {
            return err(format!(
                "clause data before `p cnf` header at line {line_no}"
            ));
        };
        for token in line.split_whitespace() {
            let lit: i32 = token
                .parse()
                .map_err(|_| ParseError(format!("invalid literal `{token}` at line {line_no}")))?;
            if lit == 0 {
                if self.clauses.len() == self.declared_clauses {
                    return err(format!(
                        "more clauses than the {} announced in the header (line {line_no})",
                        self.declared_clauses
                    ));
                }
                self.clauses.push(std::mem::take(&mut self.current_clause));
            } else {
                if lit.unsigned_abs() as usize > num_vars {
                    return err(format!(
                        "literal {lit} exceeds variable count {num_vars} (line {line_no})"
                    ));
                }
                self.current_clause.push(lit);
            }
        }
        Ok(())
    }

    fn finish(mut self) -> Result<Instance, ParseError> {
        let Some(num_vars) = self.num_vars else {
            return err("missing `p cnf` header");
        };
        self.finish_clauses()?;
        self.validate_references(num_vars)?;
        self.show_vars.sort_unstable();
        self.show_vars.dedup();
        let problem_type = self.effective_problem_type();
        if problem_type == ProblemType::AmcComplex && self.saw_show {
            return err("amc-complex does not support projection records");
        }
        self.reconcile_problem_lines(problem_type, num_vars);
        let show = match problem_type {
            ProblemType::Pmc | ProblemType::Pwmc => Some(self.show_vars),
            ProblemType::Mc | ProblemType::Wmc | ProblemType::AmcComplex => {
                self.saw_show.then_some(self.show_vars)
            }
        };
        Ok(Instance {
            num_vars,
            clauses: self.clauses,
            ptype: problem_type,
            show,
            weights: self.weights,
            warnings: self.warnings,
        })
    }

    fn finish_clauses(&mut self) -> Result<(), ParseError> {
        if !self.current_clause.is_empty() {
            if self.clauses.len() == self.declared_clauses {
                return err(format!(
                    "more clauses than the {} announced in the header (unterminated final clause)",
                    self.declared_clauses
                ));
            }
            self.clauses.push(std::mem::take(&mut self.current_clause));
            self.warnings
                .push("last clause missing terminating 0; accepted".to_string());
        }
        if self.clauses.len() < self.declared_clauses {
            self.warnings.push(format!(
                "header announced {} clauses but file contains {}",
                self.declared_clauses,
                self.clauses.len()
            ));
        }
        Ok(())
    }

    fn validate_references(&self, num_vars: usize) -> Result<(), ParseError> {
        for &var in &self.show_vars {
            if var as usize > num_vars {
                return err(format!(
                    "projection variable {var} exceeds variable count {num_vars}"
                ));
            }
        }
        for &(lit, _) in &self.weights {
            if lit.unsigned_abs() as usize > num_vars {
                return err(format!(
                    "weight literal {lit} exceeds variable count {num_vars}"
                ));
            }
        }
        Ok(())
    }

    fn effective_problem_type(&self) -> ProblemType {
        if let Some(problem_type) = self.explicit_type {
            return problem_type;
        }
        let has_weights = !self.weights.is_empty();
        let has_complex = self
            .weights
            .iter()
            .any(|(_, weight)| matches!(weight, RawWeight::Complex(_, _)));
        match (has_complex, has_weights, self.saw_show) {
            (true, _, _) => ProblemType::AmcComplex,
            (false, true, true) => ProblemType::Pwmc,
            (false, true, false) => ProblemType::Wmc,
            (false, false, true) => ProblemType::Pmc,
            (false, false, false) => ProblemType::Mc,
        }
    }

    fn reconcile_problem_lines(&mut self, problem_type: ProblemType, num_vars: usize) {
        let has_weights = !self.weights.is_empty();
        match problem_type {
            ProblemType::Mc => {
                if has_weights {
                    self.warnings
                        .push("type is mc but weight lines present; weights ignored".into());
                    self.weights.clear();
                }
                if self.saw_show {
                    self.warnings
                        .push("type is mc but show lines present; projection ignored".into());
                    self.saw_show = false;
                    self.show_vars.clear();
                }
            }
            ProblemType::Wmc => {
                if self.saw_show {
                    if self.show_vars.len() != num_vars {
                        self.warnings.push(
                            "type is wmc but a partial show line is present; projection ignored"
                                .into(),
                        );
                    }
                    self.saw_show = false;
                    self.show_vars.clear();
                }
            }
            ProblemType::Pmc => {
                if has_weights {
                    self.warnings
                        .push("type is pmc but weight lines present; weights ignored".into());
                    self.weights.clear();
                }
            }
            ProblemType::Pwmc | ProblemType::AmcComplex => {}
        }
    }
}

fn validate_num_vars(num_vars: usize) -> Result<(), ParseError> {
    if num_vars > MAX_COUNT_VARS {
        return err(format!(
            "variable count {num_vars} exceeds the maximum supported {MAX_COUNT_VARS}; refusing to allocate"
        ));
    }
    Ok(())
}

fn validate_literal(lit: i32, num_vars: usize, description: &str) -> Result<usize, ParseError> {
    if lit == 0 {
        return err(format!("{description} 0 is invalid"));
    }
    let variable = lit.unsigned_abs() as usize;
    if variable > num_vars {
        return err(format!(
            "{description} {lit} exceeds variable count {num_vars}"
        ));
    }
    Ok(variable - 1)
}
