// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

struct StreamingDimacsHeader {
    body_offset: usize,
    num_vars: usize,
    num_clauses_declared: usize,
}

fn parse_streaming_dimacs_header(bytes: &[u8]) -> Option<StreamingDimacsHeader> {
    let mut pos = 0;
    while pos < bytes.len() {
        while pos < bytes.len() && matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
            pos += 1;
        }
        match bytes.get(pos).copied() {
            None | Some(b'%') => return None,
            Some(b'p') => {
                let line_start = pos;
                while pos < bytes.len() && bytes[pos] != b'\n' {
                    pos += 1;
                }
                return parse_streaming_problem_line(&bytes[line_start..pos], pos);
            }
            Some(b'c') | Some(_) => {
                while pos < bytes.len() && bytes[pos] != b'\n' {
                    pos += 1;
                }
            }
        }
    }
    None
}

fn parse_streaming_problem_line(line: &[u8], body_offset: usize) -> Option<StreamingDimacsHeader> {
    let mut pos = 0;
    skip_ascii_letters(line, &mut pos);
    skip_ascii_spaces(line, &mut pos);
    skip_ascii_letters(line, &mut pos);
    skip_ascii_spaces(line, &mut pos);
    let num_vars = parse_saturating_usize(line, &mut pos);
    skip_ascii_spaces(line, &mut pos);
    let num_clauses_declared = parse_saturating_usize(line, &mut pos);
    Some(StreamingDimacsHeader {
        body_offset,
        num_vars,
        num_clauses_declared,
    })
}

fn skip_ascii_letters(bytes: &[u8], pos: &mut usize) {
    while *pos < bytes.len() && bytes[*pos].is_ascii_alphabetic() {
        *pos += 1;
    }
}

fn skip_ascii_spaces(bytes: &[u8], pos: &mut usize) {
    while *pos < bytes.len() && bytes[*pos] == b' ' {
        *pos += 1;
    }
}

fn parse_saturating_usize(bytes: &[u8], pos: &mut usize) -> usize {
    let mut value = 0usize;
    while *pos < bytes.len() && bytes[*pos].is_ascii_digit() {
        value = value
            .saturating_mul(10)
            .saturating_add((bytes[*pos] - b'0') as usize);
        *pos += 1;
    }
    value
}

fn require_streaming_dimacs_header(bytes: &[u8]) -> StreamingDimacsHeader {
    let Some(mut header) = parse_streaming_dimacs_header(bytes) else {
        safe_eprintln!(
            "c Parse error: no valid DIMACS header found, expected \"p cnf <num_vars> <num_clauses>\""
        );
        safe_println!("s UNKNOWN");
        std::process::exit(1);
    };
    if header.num_vars == 0 {
        safe_eprintln!(
            "c Parse error: no valid DIMACS header found, expected \"p cnf <num_vars> <num_clauses>\""
        );
        safe_println!("s UNKNOWN");
        std::process::exit(1);
    }
    header.num_vars = scan_max_variable(bytes);
    if header.num_vars > ay_sat::dimacs_core::MAX_DIMACS_VARS {
        safe_eprintln!(
            "c Parse error: maximum variable {} exceeds the maximum supported {}",
            header.num_vars,
            ay_sat::dimacs_core::MAX_DIMACS_VARS
        );
        safe_println!("s UNKNOWN");
        std::process::exit(1);
    }
    header
}

fn create_streaming_dimacs_solver(
    header: &StreamingDimacsHeader,
    variant: SolverVariant,
) -> (SatSolver, ay_sat::VariantConfig) {
    let mut solver = SatSolver::with_clause_hint(header.num_vars, header.num_clauses_declared);
    solver.set_clause_ids_disabled(true);
    solver.set_symmetry_oneshot(true);
    let mut config = variant.config(variant_input_for_dimacs(
        variant,
        header.num_vars,
        header.num_clauses_declared,
        DimacsProofPosture::NoProof,
    ));
    let ratio = header.num_clauses_declared as f64 / header.num_vars.max(1) as f64;
    if ratio > 100.0 {
        config.features.condition = false;
    }
    config.apply_to_solver(&mut solver);
    (solver, config)
}

struct StreamingClauseLoader<'a> {
    bytes: &'a [u8],
    pos: usize,
    clause_buf: Vec<Literal>,
    clauses_loaded: usize,
    ternary_count: usize,
    horn_count: usize,
    positive_in_clause: u32,
}

impl<'a> StreamingClauseLoader<'a> {
    fn new(bytes: &'a [u8], pos: usize) -> Self {
        Self {
            bytes,
            pos,
            clause_buf: Vec::with_capacity(32),
            clauses_loaded: 0,
            ternary_count: 0,
            horn_count: 0,
            positive_in_clause: 0,
        }
    }

    fn load(mut self, solver: &mut SatSolver) -> (usize, usize, usize) {
        while self.pos < self.bytes.len() {
            self.skip_whitespace();
            let Some(ch) = self.bytes.get(self.pos).copied() else {
                break;
            };
            if ch == b'%' {
                break;
            }
            if ch == b'c' || ch.is_ascii_alphabetic() {
                self.skip_line();
                continue;
            }
            let negative = ch == b'-';
            if negative {
                self.pos += 1;
            }
            if self.pos >= self.bytes.len() || !self.bytes[self.pos].is_ascii_digit() {
                self.pos += 1;
                continue;
            }
            let value = self.parse_u32();
            if value == 0 {
                self.finish_clause(solver);
            } else {
                self.push_literal(value, negative);
            }
        }
        if !self.clause_buf.is_empty() {
            self.finish_clause(solver);
        }
        (self.clauses_loaded, self.ternary_count, self.horn_count)
    }

    fn skip_whitespace(&mut self) {
        while self.pos < self.bytes.len()
            && matches!(self.bytes[self.pos], b' ' | b'\t' | b'\r' | b'\n')
        {
            self.pos += 1;
        }
    }

    fn skip_line(&mut self) {
        while self.pos < self.bytes.len() && self.bytes[self.pos] != b'\n' {
            self.pos += 1;
        }
    }

    fn parse_u32(&mut self) -> u32 {
        let mut value = 0;
        while self.pos < self.bytes.len() && self.bytes[self.pos].is_ascii_digit() {
            value = value * 10 + u32::from(self.bytes[self.pos] - b'0');
            self.pos += 1;
        }
        value
    }

    fn push_literal(&mut self, value: u32, negative: bool) {
        if !negative {
            self.positive_in_clause += 1;
        }
        let variable = Variable::new(value - 1);
        self.clause_buf.push(if negative {
            Literal::negative(variable)
        } else {
            Literal::positive(variable)
        });
    }

    fn finish_clause(&mut self, solver: &mut SatSolver) {
        self.ternary_count += usize::from(self.clause_buf.len() == 3);
        self.horn_count += usize::from(self.positive_in_clause <= 1);
        self.positive_in_clause = 0;
        solver.add_clause(std::mem::take(&mut self.clause_buf));
        self.clauses_loaded += 1;
    }
}

fn run_streaming_body(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    variant: SolverVariant,
    variant_source: DecisionSource,
) {
    let bytes = content.as_bytes();
    let header = require_streaming_dimacs_header(bytes);
    let (mut solver, streaming_config) = create_streaming_dimacs_solver(&header, variant);
    let (clauses_loaded, ternary_count, horn_count) =
        StreamingClauseLoader::new(bytes, header.body_offset).load(&mut solver);
    let features = SatFeatures::from_streaming_counters(
        header.num_vars,
        clauses_loaded,
        ternary_count,
        horn_count,
    );
    let plan = VariantProfilePlan::from_config_features_with_source(
        streaming_config,
        &features,
        variant_source,
    );
    plan.apply_postparse_to_solver(&mut solver);
    safe_eprintln!(
        "c streaming parse: {clauses_loaded} clauses loaded ({} vars)",
        header.num_vars
    );
    configure_dimacs_solver(&mut solver, stats_cfg);
    let result = solver.solve_interruptible(is_timed_out).into_inner();
    finish_dimacs_solve(&mut solver, result, stats_cfg, content, None, None, None);
}
