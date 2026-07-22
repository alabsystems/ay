// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB command tests - check-sat-assuming, get-info, get-option,
//! get-assertions, get-assignment, get-unsat-core, get-proof,
//! named terms, define-fun-rec

pub(crate) use crate::Executor;
pub(crate) use ay_frontend::parse;
pub(crate) use ay_frontend::sexp::{parse_sexp, SExpr};
pub(crate) use ay_sat::Solver as SatSolver;

pub(crate) fn get_numeral_stat(stats: &str, key: &str) -> Option<u64> {
    let stats_sexp = parse_sexp(stats).ok()?;
    let entries = stats_sexp.as_list()?;
    for pair in entries.chunks_exact(2) {
        let [SExpr::Keyword(entry_key), SExpr::Numeral(numeral)] = pair else {
            continue;
        };
        if entry_key == key {
            return numeral.parse::<u64>().ok();
        }
    }
    None
}

pub(crate) fn parse_assume_term(line: &str) -> Option<&str> {
    let rest = line.trim().strip_prefix("(assume ")?;
    let (_id, term_with_close) = rest.split_once(' ')?;
    term_with_close.strip_suffix(')')
}

pub(crate) fn count_assumes(proof: &str) -> usize {
    proof.lines().filter_map(parse_assume_term).count()
}

pub(crate) fn count_assumes_for_term(proof: &str, expected_term: &str) -> usize {
    proof
        .lines()
        .filter_map(parse_assume_term)
        .filter(|term| *term == expected_term)
        .count()
}

mod assertions;
mod check_sat_assuming;
mod info_options;
mod regression;
mod unsat_assumptions;
mod unsat_core_pigeonhole;
