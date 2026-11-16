// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;
use num_bigint::BigInt;

/// A boxed-integer vocabulary: `box : Int -> U`, `unbox : U -> Int`.
struct Vocabulary {
    terms: TermStore,
    boxed: Sort,
}

impl Vocabulary {
    fn new() -> Self {
        Self {
            terms: TermStore::new(),
            boxed: Sort::Uninterpreted("U".to_string()),
        }
    }

    fn int(&mut self, value: i64) -> TermId {
        self.terms.mk_int(BigInt::from(value))
    }

    fn int_var(&mut self, name: &str) -> TermId {
        self.terms.mk_var(name, Sort::Int)
    }

    fn flag(&mut self, name: &str) -> TermId {
        self.terms.mk_var(name, Sort::Bool)
    }

    fn boxed(&mut self, inner: TermId) -> TermId {
        let sort = self.boxed.clone();
        self.terms.mk_app(Symbol::named("box"), vec![inner], sort)
    }

    fn unbox(&mut self, inner: TermId) -> TermId {
        self.terms
            .mk_app(Symbol::named("unbox"), vec![inner], Sort::Int)
    }

    fn int_fn(&mut self, name: &str, args: Vec<TermId>) -> TermId {
        self.terms.mk_app(Symbol::named(name), args, Sort::Int)
    }

    fn pred(&mut self, name: &str, args: Vec<TermId>) -> TermId {
        self.terms.mk_app(Symbol::named(name), args, Sort::Bool)
    }

    fn run(&mut self, window: Vec<TermId>) -> CanonicalWindow {
        canonicalize_window(&mut self.terms, window)
    }

    /// `window` holds the equality of `a` and `b`, written either way.
    fn holds_equality(&mut self, window: &[TermId], a: TermId, b: TermId) -> bool {
        let (forward, backward) = (self.terms.mk_eq(a, b), self.terms.mk_eq(b, a));
        window.contains(&forward) || window.contains(&backward)
    }
}

/// Every subterm of `term`, `term` included.
fn subterms(terms: &TermStore, term: TermId) -> Vec<TermId> {
    let mut seen = Vec::new();
    let mut stack = vec![term];
    while let Some(next) = stack.pop() {
        if seen.contains(&next) {
            continue;
        }
        seen.push(next);
        match terms.get(next) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            _ => {}
        }
    }
    seen
}

#[test]
fn two_atoms_over_root_equal_terms_become_one_atom() {
    let mut v = Vocabulary::new();
    let four = v.int(4);
    let boxed = v.boxed(four);
    let round_trip = v.unbox(boxed);
    let hi = v.int_var("hi");
    let (p, q) = (v.flag("p"), v.flag("q"));
    let root = v.terms.mk_eq(four, round_trip);
    let through_box = v.terms.mk_lt(round_trip, hi);
    let direct = v.terms.mk_lt(four, hi);
    let first = v.terms.mk_or(vec![through_box, p]);
    let not_direct = v.terms.mk_not(direct);
    let second = v.terms.mk_or(vec![not_direct, q]);

    let canonical = v.run(vec![root, first, second]);

    let expected_first = v.terms.mk_or(vec![direct, p]);
    assert_eq!(canonical.assertions.len(), 3);
    assert_eq!(canonical.assertions[..2], [expected_first, second]);
    assert!(v.holds_equality(&canonical.assertions, round_trip, four));
    assert_eq!(canonical.merges, 1);
}

#[test]
fn without_the_root_equality_the_two_atoms_stay_apart() {
    let mut v = Vocabulary::new();
    let four = v.int(4);
    let boxed = v.boxed(four);
    let round_trip = v.unbox(boxed);
    let hi = v.int_var("hi");
    let (p, q) = (v.flag("p"), v.flag("q"));
    let through_box = v.terms.mk_lt(round_trip, hi);
    let direct = v.terms.mk_lt(four, hi);
    let first = v.terms.mk_or(vec![through_box, p]);
    let not_direct = v.terms.mk_not(direct);
    let second = v.terms.mk_or(vec![not_direct, q]);

    let canonical = v.run(vec![first, second]);

    assert_eq!(canonical.assertions, vec![first, second]);
    assert_eq!((canonical.rounds, canonical.merges), (0, 0));
}

#[test]
fn a_value_stands_for_its_class_and_the_atom_folds() {
    let mut v = Vocabulary::new();
    let eight = v.int(8);
    let hi = v.int_fn("hi", vec![eight]);
    let limit = v.int(256);
    let zero = v.int(0);
    let c = v.int_var("c");
    let diff = v.int_fn("sub", vec![c, c]);
    let p = v.flag("p");
    let hi_is = v.terms.mk_eq(hi, limit);
    let diff_is = v.terms.mk_eq(zero, diff);
    let atom = v.terms.mk_le(hi, diff);
    let clause = v.terms.mk_or(vec![atom, p]);

    let canonical = v.run(vec![hi_is, diff_is, clause]);

    // `(<= 256 0)` folds to false, so the clause is the literal `p`.
    assert_eq!(canonical.assertions.len(), 3);
    assert_eq!(canonical.assertions[0], p);
    assert!(v.holds_equality(&canonical.assertions, hi, limit));
    assert!(v.holds_equality(&canonical.assertions, diff, zero));
}

#[test]
fn congruence_reaches_under_function_symbols() {
    let mut v = Vocabulary::new();
    let (a, b) = (v.int_var("a"), v.int_var("b"));
    let (fa, fb) = (v.int_fn("f", vec![a]), v.int_fn("f", vec![b]));
    let (pa, pb) = (v.pred("P", vec![fa]), v.pred("P", vec![fb]));
    let (q, r) = (v.flag("q"), v.flag("r"));
    let root = v.terms.mk_eq(a, b);
    let first = v.terms.mk_or(vec![pa, q]);
    let second = v.terms.mk_or(vec![pb, r]);

    let canonical = v.run(vec![root, first, second]);

    let window = canonical.assertions.clone();
    assert_eq!(window.len(), 3);
    assert!(v.holds_equality(&window, a, b));
    let atoms_first = subterms(&v.terms, window[0]);
    let atoms_second = subterms(&v.terms, window[1]);
    let shared: Vec<TermId> = [pa, pb]
        .into_iter()
        .filter(|atom| atoms_first.contains(atom) && atoms_second.contains(atom))
        .collect();
    assert_eq!(shared.len(), 1, "both clauses name one of the two atoms");
}

#[test]
fn an_application_defined_by_arithmetic_is_read_as_that_arithmetic() {
    let mut v = Vocabulary::new();
    let (a, b) = (v.int_var("a"), v.int_var("b"));
    let named = v.int_fn("sub", vec![a, b]);
    let plain = v.terms.mk_sub(vec![a, b]);
    let zero = v.int(0);
    let p = v.flag("p");
    let root = v.terms.mk_eq(named, plain);
    let atom = v.terms.mk_le(zero, named);
    let clause = v.terms.mk_or(vec![atom, p]);

    let canonical = v.run(vec![root, clause]);

    let expected_atom = v.terms.mk_le(zero, plain);
    let expected = v.terms.mk_or(vec![expected_atom, p]);
    assert_eq!(canonical.assertions.len(), 2);
    assert_eq!(canonical.assertions[0], expected);
    assert!(v.holds_equality(&canonical.assertions, named, plain));
}

#[test]
fn among_uninterpreted_terms_the_smallest_stands_for_the_class() {
    let mut v = Vocabulary::new();
    let (a, x) = (v.int_var("a"), v.int_var("x"));
    let ga = v.int_fn("g", vec![a]);
    let fga = v.int_fn("f", vec![ga]);
    let q = v.flag("q");
    let root = v.terms.mk_eq(fga, x);
    let atom = v.pred("P", vec![fga]);
    let clause = v.terms.mk_or(vec![atom, q]);

    let canonical = v.run(vec![root, clause]);

    let shallow = v.pred("P", vec![x]);
    let expected = v.terms.mk_or(vec![shallow, q]);
    assert_eq!(canonical.assertions[0], expected);
    assert!(v.holds_equality(&canonical.assertions, fga, x));
}

#[test]
fn a_fixed_atom_opens_a_guarded_equality_in_the_next_round() {
    let mut v = Vocabulary::new();
    let (a, x, y) = (v.int_var("a"), v.int_var("x"), v.int_var("y"));
    let guard = v.pred("P", vec![a]);
    let (rx, ry) = (v.pred("R", vec![x]), v.pred("R", vec![y]));
    let (q, r) = (v.flag("q"), v.flag("r"));
    let equal = v.terms.mk_eq(x, y);
    let guarded = v.terms.mk_implies(guard, equal);
    let first = v.terms.mk_or(vec![rx, q]);
    let second = v.terms.mk_or(vec![ry, r]);

    let canonical = v.run(vec![guard, guarded, first, second]);

    let window = canonical.assertions.clone();
    assert_eq!(canonical.rounds, 2);
    assert!(window.contains(&guard), "the literal stays asserted");
    assert!(
        v.holds_equality(&window, x, y),
        "the opened equality is asserted"
    );
    let clauses: Vec<TermId> = window
        .iter()
        .copied()
        .filter(|&conjunct| {
            let inside = subterms(&v.terms, conjunct);
            conjunct != guard && (inside.contains(&rx) || inside.contains(&ry))
        })
        .collect();
    assert_eq!(clauses.len(), 2);
    assert!(
        clauses.iter().all(|&c| subterms(&v.terms, c).contains(&rx))
            || clauses.iter().all(|&c| subterms(&v.terms, c).contains(&ry)),
        "after the second round both clauses name the same atom"
    );
}

#[test]
fn a_guard_that_is_not_fixed_keeps_its_equality_closed() {
    let mut v = Vocabulary::new();
    let (a, x, y) = (v.int_var("a"), v.int_var("x"), v.int_var("y"));
    let guard = v.pred("P", vec![a]);
    let (rx, ry) = (v.pred("R", vec![x]), v.pred("R", vec![y]));
    let (q, r) = (v.flag("q"), v.flag("r"));
    let equal = v.terms.mk_eq(x, y);
    let guarded = v.terms.mk_implies(guard, equal);
    let first = v.terms.mk_or(vec![rx, q]);
    let second = v.terms.mk_or(vec![ry, r]);

    let canonical = v.run(vec![guarded, first, second]);

    assert_eq!(canonical.assertions, vec![guarded, first, second]);
    assert_eq!(canonical.rounds, 0);
}

#[test]
fn a_literal_is_not_rewritten_by_itself() {
    let mut v = Vocabulary::new();
    let a = v.int_var("a");
    let atom = v.pred("P", vec![a]);
    let q = v.flag("q");
    let not_atom = v.terms.mk_not(atom);
    let clause = v.terms.mk_or(vec![atom, q]);

    let canonical = v.run(vec![not_atom, clause]);

    assert_eq!(canonical.assertions, vec![not_atom, q]);
}

/// `(= a (wrap g))`, a clause over `(R a)` and one over `(R (wrap false))`,
/// with the literal `(not g)` when `fixed`.
fn wrapped_flag_window(v: &mut Vocabulary, fixed: bool) -> (Vec<TermId>, [TermId; 4]) {
    let (g, q, r) = (v.flag("g"), v.flag("q"), v.flag("r"));
    let sort = v.boxed.clone();
    let a = v.terms.mk_var("a", sort.clone());
    let wrapped = v.terms.mk_app(Symbol::named("wrap"), vec![g], sort.clone());
    let false_term = v.terms.false_term();
    let wrapped_false = v
        .terms
        .mk_app(Symbol::named("wrap"), vec![false_term], sort);
    let not_g = v.terms.mk_not(g);
    let defined = v.terms.mk_eq(a, wrapped);
    let (on_a, on_false) = (v.pred("R", vec![a]), v.pred("R", vec![wrapped_false]));
    let first = v.terms.mk_or(vec![on_a, q]);
    let second = v.terms.mk_or(vec![on_false, r]);
    let second_over_a = v.terms.mk_or(vec![on_a, r]);
    let mut window = vec![defined, first, second];
    if fixed {
        window.insert(0, not_g);
    }
    (window, [a, wrapped, wrapped_false, second_over_a])
}

#[test]
fn a_fixed_flag_under_a_function_is_its_value_in_the_definition() {
    let mut v = Vocabulary::new();
    let (window, [a, wrapped, wrapped_false, second_over_a]) = wrapped_flag_window(&mut v, true);

    let window = v.run(window).assertions;

    assert!(
        v.holds_equality(&window, a, wrapped_false),
        "the definition names the value of the flag"
    );
    assert!(
        window
            .iter()
            .all(|&conjunct| !subterms(&v.terms, conjunct).contains(&wrapped)),
        "no term over the fixed flag is left"
    );
    assert!(
        window.contains(&second_over_a),
        "the clause over the value is a clause over the defined term"
    );
}

#[test]
fn a_flag_that_is_not_fixed_stays_under_the_function() {
    let mut v = Vocabulary::new();
    let (window, [a, wrapped, wrapped_false, second_over_a]) = wrapped_flag_window(&mut v, false);

    let window = v.run(window).assertions;

    assert!(v.holds_equality(&window, a, wrapped));
    assert!(!v.holds_equality(&window, a, wrapped_false));
    assert!(!window.contains(&second_over_a));
}

#[test]
fn two_values_in_one_class_refute_the_window() {
    let mut v = Vocabulary::new();
    let x = v.int_var("x");
    let (one, two) = (v.int(1), v.int(2));
    let p = v.flag("p");
    let first = v.terms.mk_eq(x, one);
    let second = v.terms.mk_eq(x, two);
    let atom = v.terms.mk_le(x, one);
    let clause = v.terms.mk_or(vec![atom, p]);

    let canonical = v.run(vec![first, second, clause]);

    assert_eq!(canonical.assertions, vec![v.terms.false_term()]);
}

#[test]
fn two_values_in_two_classes_refute_nothing() {
    let mut v = Vocabulary::new();
    let (x, y) = (v.int_var("x"), v.int_var("y"));
    let (one, two) = (v.int(1), v.int(2));
    let p = v.flag("p");
    let first = v.terms.mk_eq(x, one);
    let second = v.terms.mk_eq(y, two);
    let atom = v.terms.mk_le(y, one);
    let clause = v.terms.mk_or(vec![atom, p]);

    let canonical = v.run(vec![first, second, clause]);

    // `(<= 2 1)` folds to false and leaves `p`; both definitions stay.
    assert_eq!(canonical.assertions.len(), 3);
    assert_eq!(canonical.assertions[0], p);
    assert!(v.holds_equality(&canonical.assertions, x, one));
    assert!(v.holds_equality(&canonical.assertions, y, two));
}

#[test]
fn a_refuted_conjunct_collapses_the_window() {
    let mut v = Vocabulary::new();
    let x = v.int_var("x");
    let (one, zero) = (v.int(1), v.int(0));
    let root = v.terms.mk_eq(x, one);
    let atom = v.terms.mk_lt(x, zero);

    let canonical = v.run(vec![root, atom]);

    assert_eq!(canonical.assertions, vec![v.terms.false_term()]);
}

#[test]
fn a_satisfied_twin_of_the_refuted_conjunct_leaves_the_definition() {
    let mut v = Vocabulary::new();
    let x = v.int_var("x");
    let (one, zero) = (v.int(1), v.int(0));
    let root = v.terms.mk_eq(x, one);
    let atom = v.terms.mk_gt(x, zero);

    let canonical = v.run(vec![root, atom]);

    assert_eq!(canonical.assertions.len(), 1);
    assert!(v.holds_equality(&canonical.assertions, x, one));
    let again = v.run(canonical.assertions.clone());
    assert_eq!(again.assertions, canonical.assertions);
    assert_eq!(again.rounds, 0, "a finished window is a fixpoint");
}

#[test]
fn a_term_equal_to_its_own_application_does_not_loop() {
    let mut v = Vocabulary::new();
    let x = v.int_var("x");
    let fx = v.int_fn("f", vec![x]);
    let ffx = v.int_fn("f", vec![fx]);
    let q = v.flag("q");
    let root = v.terms.mk_eq(x, fx);
    let deep = v.pred("P", vec![ffx]);
    let clause = v.terms.mk_or(vec![deep, q]);

    let canonical = v.run(vec![root, clause]);

    let shallow = v.pred("P", vec![x]);
    let expected = v.terms.mk_or(vec![shallow, q]);
    assert_eq!(canonical.assertions.len(), 2);
    assert_eq!(canonical.assertions[0], expected);
    assert!(v.holds_equality(&canonical.assertions, fx, x));
}

#[test]
fn an_arithmetic_term_over_its_own_class_does_not_loop() {
    let mut v = Vocabulary::new();
    let (x, y) = (v.int_var("x"), v.int_var("y"));
    let sum = v.terms.mk_add(vec![x, y]);
    let q = v.flag("q");
    let root = v.terms.mk_eq(x, sum);
    let atom = v.pred("P", vec![x]);
    let clause = v.terms.mk_or(vec![atom, q]);

    let canonical = v.run(vec![root, clause]);

    assert_ne!(canonical.assertions, [] as [TermId; 0]);
    assert_ne!(canonical.assertions, vec![v.terms.false_term()]);
}

#[test]
fn nothing_inside_a_quantifier_is_rewritten() {
    let mut v = Vocabulary::new();
    let (a, b) = (v.int_var("a"), v.int_var("b"));
    let bound = v.terms.mk_var("k", Sort::Int);
    let fa = v.int_fn("f", vec![a]);
    let body = v.terms.mk_le(bound, fa);
    let quantified = v.terms.mk_forall(vec![("k".to_string(), Sort::Int)], body);
    let root = v.terms.mk_eq(fa, b);

    let canonical = v.run(vec![root, quantified]);

    assert_eq!(canonical.assertions.len(), 2);
    assert_eq!(canonical.assertions[0], quantified);
    assert!(v.holds_equality(&canonical.assertions, fa, b));
}
