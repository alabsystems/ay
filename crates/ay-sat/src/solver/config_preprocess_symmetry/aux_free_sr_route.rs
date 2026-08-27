// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Aux-free symmetry-refutation family selection.

use crate::literal::Literal;
use crate::symmetry::detector::{self, LexClause};

/// Try the cheap structural families in their established priority order.
///
/// Every family rides the same aux-free SR machinery as the pigeonhole
/// route: WLOG units carry transposition witnesses over the ORIGINAL
/// variables, with no lex towers whose per-generator permutation could
/// invalidate earlier towers. `r-uniform matching` covers the whole
/// `count_p` family (`count_p2` edges, `count_p3` triples, …).
pub(super) fn detect(clauses: &[Vec<Literal>]) -> (&'static str, Option<Vec<LexClause>>) {
    let mut route_kind = "php matrix";
    let steps = detector::detect_php_aux_free_sr(clauses)
        .or_else(|| {
            route_kind = "r-uniform matching";
            detector::detect_matching_aux_free_sr(clauses)
        })
        .or_else(|| {
            route_kind = "phased colouring";
            detector::detect_phased_colouring_aux_free_sr(clauses)
        })
        .or_else(|| {
            route_kind = "clique colouring";
            detector::detect_clique_colouring_aux_free_sr(clauses)
        })
        .or_else(|| {
            route_kind = "relativized php";
            detector::detect_relativized_php_aux_free_sr(clauses)
        });
    (route_kind, steps)
}
