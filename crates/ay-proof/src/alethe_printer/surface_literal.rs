// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Narrow syntactic equivalence for alternate SMT-LIB bit-vector literal
//! spellings below otherwise byte-identical applications.

use super::*;

const MAX_LITERAL_EQUIVALENCE_BYTES: usize = 64 * 1024;
const MAX_LITERAL_EQUIVALENCE_DEPTH: usize = 64;
const MAX_LITERAL_EQUIVALENCE_NODES: usize = 256;

pub(super) fn equal_modulo_bitvec_literal_spelling(left: &str, right: &str) -> bool {
    if left.len() > MAX_LITERAL_EQUIVALENCE_BYTES || right.len() > MAX_LITERAL_EQUIVALENCE_BYTES {
        return false;
    }
    let mut nodes = 0;
    equal_inner(left, right, 0, &mut nodes)
}

fn equal_inner(left: &str, right: &str, depth: usize, nodes: &mut usize) -> bool {
    if left == right {
        return true;
    }
    if depth > MAX_LITERAL_EQUIVALENCE_DEPTH || *nodes >= MAX_LITERAL_EQUIVALENCE_NODES {
        return false;
    }
    *nodes += 1;
    if let (Some(left_bv), Some(right_bv)) = (
        parse_printed_bitvec_literal(left),
        parse_printed_bitvec_literal(right),
    ) {
        return left_bv == right_bv;
    }
    let (Some(left), Some(right)) = (
        left.strip_prefix('(')
            .and_then(|term| term.strip_suffix(')')),
        right
            .strip_prefix('(')
            .and_then(|term| term.strip_suffix(')')),
    ) else {
        return false;
    };
    let (Some(left_parts), Some(right_parts)) = (split_smt_terms(left), split_smt_terms(right))
    else {
        return false;
    };
    left_parts.len() == right_parts.len()
        && left_parts
            .iter()
            .zip(right_parts.iter())
            .all(|(left, right)| equal_inner(left, right, depth + 1, nodes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alternate_bitvector_literal_spellings_match_positionally() {
        assert!(equal_modulo_bitvec_literal_spelling(
            "(store mem idx #xAA)",
            "(store mem idx #b10101010)"
        ));
        assert!(equal_modulo_bitvec_literal_spelling("#xAA", "(_ bv170 8)"));
    }

    #[test]
    fn changed_bitvector_values_or_application_shapes_decline() {
        assert!(!equal_modulo_bitvec_literal_spelling("#xAA", "#xAB"));
        assert!(!equal_modulo_bitvec_literal_spelling("#xAA", "#x00AA"));
        assert!(!equal_modulo_bitvec_literal_spelling(
            "(store mem idx #xAA)",
            "(select mem idx #b10101010)"
        ));
    }
}
