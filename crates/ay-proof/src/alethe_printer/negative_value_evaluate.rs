// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `evaluate` of a ground arithmetic term whose value is NEGATIVE.
//!
//! THE DEFECT. Pinned Carcara's `evaluate` (1.1.0, `rules/extras.rs`) checks
//! `(= term value)` by evaluating `term` and comparing the result with
//! `value` STRUCTURALLY. A negative value evaluates to the pool's negative
//! constant, but SMT-LIB can only spell it `(- 1)`, which parses as unary
//! minus applied to `1`; the two never compare equal, so every such step is
//! refused ("expected terms to be equal: '-1' and '(- 1)'") and the whole
//! document is `invalid`. Measured on the OR-substitution fuzz with standard
//! negative literals: 12 of 496 certified UNSATs on main, every one at an
//! `evaluate` step concluding `(= (+ (- 3) 2) (- 1))` or the like.
//!
//! THE DERIVATION. The same rule evaluates the whole EQUALITY instead: both
//! sides of `(= term (- 1))` evaluate to the constant `-1`, so
//! `(= (= term (- 1)) true)` is an `evaluate` instance pinned Carcara accepts,
//! and `equiv_pos1` with the `true` axiom resolves it down to the original
//! conclusion. Nothing new is claimed: the conclusion is the step's own
//! clause, byte for byte, and every step is an ordinary instance of its rule
//! (measured valid on pinned Carcara 1.1.0).

use ay_core::{ProofId, TermId};

use super::{split_application, AlethePrinter};

impl AlethePrinter<'_> {
    /// The four-step rendering above for a unit `evaluate` equality whose
    /// printed side is a negative number, or `None` for any other clause
    /// (which keeps its one-step `evaluate`).
    pub(super) fn format_negative_value_evaluate(
        &self,
        id: ProofId,
        clause: &[TermId],
        clause_str: &str,
    ) -> Option<String> {
        let [literal] = clause else {
            return None;
        };
        let equality = self.format_term(*literal);
        let sides = split_application(&equality, "=")?;
        if sides.len() != 2
            || !sides.iter().any(|side| is_negative_number_spelling(side))
            || clause_str != format!("(cl {equality})")
        {
            return None;
        }
        Some(format!(
            "(step {id}.ev (cl (= {equality} true)) :rule evaluate)\n\
             (step {id}.tr (cl true) :rule true)\n\
             (step {id}.ep (cl (not (= {equality} true)) {equality} (not true)) :rule equiv_pos1)\n\
             (step {id} {clause_str} :rule resolution :premises ({id}.ev {id}.tr {id}.ep))"
        ))
    }
}

/// `(- n)` with `n` an unsigned numeral or decimal: the only spelling
/// SMT-LIB has for a negative arithmetic constant.
fn is_negative_number_spelling(side: &str) -> bool {
    side.strip_prefix("(- ")
        .and_then(|rest| rest.strip_suffix(')'))
        .is_some_and(|magnitude| {
            magnitude.starts_with(|c: char| c.is_ascii_digit())
                && magnitude.chars().all(|c| c.is_ascii_digit() || c == '.')
        })
}

#[cfg(test)]
mod tests {
    use super::is_negative_number_spelling;

    #[test]
    fn only_a_negated_numeral_or_decimal_is_a_negative_number() {
        assert!(is_negative_number_spelling("(- 1)"));
        assert!(is_negative_number_spelling("(- 12.5)"));
        assert!(!is_negative_number_spelling("1"));
        assert!(!is_negative_number_spelling("(- x)"));
        assert!(!is_negative_number_spelling("(- 3 1)"));
        assert!(!is_negative_number_spelling("(- (+ 1 2))"));
    }
}
