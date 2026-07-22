// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::term::TermId;

#[test]
fn test_monomial_binary() {
    let x = TermId(1);
    let y = TermId(2);
    let aux = TermId(100);
    let mon = Monomial::new(vec![x, y], aux);

    assert!(mon.is_binary());
    assert!(!mon.is_square());
    assert_eq!(mon.x(), Some(x));
    assert_eq!(mon.y(), Some(y));
}

#[test]
fn test_monomial_square() {
    let x = TermId(1);
    let aux = TermId(100);
    let mon = Monomial::new(vec![x, x], aux);

    assert!(mon.is_binary());
    assert!(mon.is_square());
    assert_eq!(mon.x(), Some(x));
    assert_eq!(mon.y(), Some(x));
}

/// Ternary monomial should NOT be binary.
#[test]
fn test_monomial_ternary_not_binary() {
    let x = TermId(1);
    let y = TermId(2);
    let z = TermId(3);
    let aux = TermId(100);
    let mon = Monomial::new(vec![x, y, z], aux);

    assert!(!mon.is_binary());
    assert!(!mon.is_square());
    // x() and y() are convenience accessors for binary monomials;
    // for ternary monomials they still return Some (first/second element).
    assert_eq!(mon.x(), Some(x));
    assert_eq!(mon.y(), Some(y));
    assert_eq!(mon.vars.len(), 3);
}

/// aux_var is preserved.
#[test]
fn test_monomial_aux_var_preserved() {
    let x = TermId(10);
    let y = TermId(20);
    let aux = TermId(999);
    let mon = Monomial::new(vec![x, y], aux);
    assert_eq!(mon.aux_var, aux);
}

/// vars are preserved.
#[test]
fn test_monomial_vars_preserved() {
    let a = TermId(5);
    let b = TermId(10);
    let c = TermId(15);
    let aux = TermId(100);
    let mon = Monomial::new(vec![a, b, c], aux);
    assert_eq!(mon.vars, vec![a, b, c]);
    assert_eq!(mon.vars.len(), 3);
}
