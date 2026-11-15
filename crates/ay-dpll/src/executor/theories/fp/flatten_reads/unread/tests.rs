// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;

fn bv_array() -> Sort {
    Sort::array(Sort::bitvec(64), Sort::bitvec(32))
}

fn mentions(terms: &TermStore, roots: &[TermId], target: TermId) -> bool {
    let mut stack = roots.to_vec();
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(term) = stack.pop() {
        if term == target {
            return true;
        }
        if seen.insert(term) {
            stack.extend(children(terms, term).unwrap_or_default());
        }
    }
    false
}

/// The model-checker-consumer slice shape: `data = s!fld_data` with the field unused.
#[test]
fn drops_the_definition_of_an_array_field_nothing_reads() {
    let mut terms = TermStore::new();
    let data = terms.mk_var("data", bv_array());
    let field = terms.mk_var("s!fld_data", bv_array());
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let read = terms.mk_select(data, zero);
    let value = terms.mk_bitvec(BigInt::from(7), 32);
    let read_is_seven = terms.mk_eq(read, value);
    let defines_field = terms.mk_eq(data, field);
    let roots = [defines_field, read_is_seven];

    let elimination =
        eliminate_unread_array_equalities(&mut terms, &roots).expect("the field equality goes");
    assert_eq!(elimination.definitions, vec![(field, data)]);
    assert!(!mentions(&terms, &elimination.assertions, field));
    assert!(mentions(&terms, &elimination.assertions, read_is_seven));
}

/// Negative twin: an array that is also READ is observable off the equality,
/// so the equality is a real constraint on its cells and must stay.
#[test]
fn keeps_an_equality_whose_array_is_also_read() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv_array());
    let a = terms.mk_var("a", bv_array());
    let i = terms.mk_bitvec(BigInt::from(1), 64);
    let v = terms.mk_bitvec(BigInt::from(5), 32);
    let stored = terms.mk_store(a, i, v);
    let defines_x = terms.mk_eq(x, stored);
    let read = terms.mk_select(x, i);
    let w = terms.mk_bitvec(BigInt::from(6), 32);
    let read_is_six = terms.mk_eq(read, w);

    assert!(eliminate_unread_array_equalities(&mut terms, &[defines_x, read_is_six]).is_none());
}

/// Negative twin: a negated equality forces the arrays APART; replacing it by
/// `true` would weaken a negative occurrence, which is not an equivalence.
#[test]
fn keeps_a_negated_equality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv_array());
    let a = terms.mk_var("a", bv_array());
    let eq = terms.mk_eq(x, a);
    let ne = terms.mk_not(eq);
    assert!(eliminate_unread_array_equalities(&mut terms, &[ne]).is_none());
}

/// An implication's antecedent and an `ite` condition are not positive.
#[test]
fn keeps_an_equality_in_an_antecedent_or_a_condition() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv_array());
    let a = terms.mk_var("a", bv_array());
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let eq = terms.mk_eq(x, a);
    let implication = terms.mk_implies(eq, p);
    assert!(eliminate_unread_array_equalities(&mut terms, &[implication]).is_none());

    let y = terms.mk_var("y", bv_array());
    let b = terms.mk_var("b", bv_array());
    let eq2 = terms.mk_eq(y, b);
    let conditional = terms.mk_ite(eq2, p, q);
    assert!(eliminate_unread_array_equalities(&mut terms, &[conditional]).is_none());
}

/// A guarded definition (the SSA `ite` lifted into `or`) is positive.
#[test]
fn drops_a_guarded_definition_chain_in_two_rounds() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", bv_array());
    let x = terms.mk_var("x!fld_data", bv_array());
    let ssa = terms.mk_var("x_ssa!fld_data", bv_array());
    let g = terms.mk_var("g", Sort::Bool);
    let not_g = terms.mk_not(g);
    let i = terms.mk_bitvec(BigInt::from(0), 64);
    let v = terms.mk_bitvec(BigInt::from(3), 32);
    let stored = terms.mk_store(a, i, v);
    let x_is_stored = terms.mk_eq(stored, x);
    let x_is_ssa = terms.mk_eq(x, ssa);
    let when_g = terms.mk_or(vec![not_g, x_is_stored]);
    let otherwise = terms.mk_or(vec![g, x_is_ssa]);

    let elimination = eliminate_unread_array_equalities(&mut terms, &[when_g, otherwise])
        .expect("both guarded equalities go");
    // Round one can only take the SSA link (`x` occurs twice); round two then
    // takes `x` itself. Reconstruction runs in reverse: x first, then ssa.
    assert_eq!(elimination.definitions, vec![(ssa, x), (x, stored)]);
    assert!(!mentions(&terms, &elimination.assertions, x));
    assert!(!mentions(&terms, &elimination.assertions, stored));
}

#[test]
fn abstains_under_a_quantifier() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv_array());
    let a = terms.mk_var("a", bv_array());
    let eq = terms.mk_eq(x, a);
    let p = terms.mk_var("p", Sort::Bool);
    let body = terms.mk_or(vec![p]);
    let quantified = terms.mk_forall(vec![("k".to_string(), Sort::bitvec(8))], body);
    assert!(eliminate_unread_array_equalities(&mut terms, &[eq, quantified]).is_none());
}

/// A definition chain longer than the round cap, anchored by a read of its
/// first array, unwinds within one round: each removal leaves the next link's
/// constant with one occurrence. Reconstruction order is the reverse of the
/// removal order, so `x1` is rebuilt from `x0` first and `x200` last.
#[test]
fn drops_a_definition_chain_longer_than_the_round_cap() {
    const LINKS: usize = 200;
    assert!(LINKS > MAX_ROUNDS);
    let mut terms = TermStore::new();
    let xs: Vec<TermId> = (0..=LINKS)
        .map(|k| terms.mk_var(&format!("x{k}"), bv_array()))
        .collect();
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let read = terms.mk_select(xs[0], zero);
    let seven = terms.mk_bitvec(BigInt::from(7), 32);
    let mut roots = vec![terms.mk_eq(read, seven)];
    for k in 0..LINKS {
        roots.push(terms.mk_eq(xs[k], xs[k + 1]));
    }

    let elimination =
        eliminate_unread_array_equalities(&mut terms, &roots).expect("the whole chain goes");
    assert_eq!(elimination.definitions.len(), LINKS);
    assert_eq!(elimination.definitions[0], (xs[LINKS], xs[LINKS - 1]));
    assert_eq!(elimination.definitions[LINKS - 1], (xs[1], xs[0]));
    assert!(mentions(&terms, &elimination.assertions, xs[0]));
    for &x in &xs[1..] {
        assert!(!mentions(&terms, &elimination.assertions, x));
    }
}

/// An unread memory SSA chain `m(k+1) = (store mk i v)` unwinds in one round:
/// removing the last definition releases its `store`, which leaves the
/// previous version with one occurrence. The base array stays, it is read.
#[test]
fn drops_an_unread_store_chain_down_to_the_read_base() {
    let mut terms = TermStore::new();
    let ms: Vec<TermId> = (0..=5)
        .map(|k| terms.mk_var(&format!("m{k}"), bv_array()))
        .collect();
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let read = terms.mk_select(ms[0], zero);
    let seven = terms.mk_bitvec(BigInt::from(7), 32);
    let mut roots = vec![terms.mk_eq(read, seven)];
    for k in 0..5 {
        let at = terms.mk_bitvec(BigInt::from(k as u64 + 1), 64);
        let value = terms.mk_bitvec(BigInt::from(k as u64), 32);
        let stored = terms.mk_store(ms[k], at, value);
        roots.push(terms.mk_eq(ms[k + 1], stored));
    }

    let elimination =
        eliminate_unread_array_equalities(&mut terms, &roots).expect("the chain goes");
    let defined: Vec<TermId> = elimination.definitions.iter().map(|&(x, _)| x).collect();
    assert_eq!(defined, vec![ms[5], ms[4], ms[3], ms[2], ms[1]]);
    assert!(mentions(&terms, &elimination.assertions, ms[0]));
    assert!(!mentions(&terms, &elimination.assertions, ms[1]));
}

/// A `let` abstains even with no bindings: the substitution treats it as a
/// leaf, so an atom below it would be recorded but never replaced.
#[test]
fn abstains_on_a_let() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv_array());
    let a = terms.mk_var("a", bv_array());
    let eq = terms.mk_eq(x, a);
    let wrapped = terms.mk_let(Vec::new(), eq);
    assert!(eliminate_unread_array_equalities(&mut terms, &[wrapped]).is_none());
}
