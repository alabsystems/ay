// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// REGRESSION: the collision can also arrive as an application HEAD — a
/// user FUNCTION named `x` applied to arguments. The printed `(x 0)` is a
/// parse error inside `(choice ((x S)) …)`, so an unguarded lowering would
/// regress the document from `holey` to `invalid`. Measured on carcara
/// 1.1.0: `(x 0)` parses at the top level but not under the binder.
#[test]
fn test_array_store_permutation_with_a_function_named_x_stays_a_hole() {
    use ay_core::{ArraySort, Symbol};

    let mut terms = TermStore::new();
    let sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let array = terms.mk_var("a", sort);
    let zero = terms.mk_int(0.into());
    // Index i = (x 0): an application whose HEAD wears the binder's name.
    let i = terms.mk_app(Symbol::named("x"), [zero], Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let left_inner = terms.mk_store(array, i, v);
    let left = terms.mk_store(left_inner, j, w);
    let right_inner = terms.mk_store(array, j, w);
    let right = terms.mk_store(right_inner, i, v);
    let index_equality = terms.mk_app(Symbol::named("="), [i, j], Sort::Bool);
    let array_equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);

    let output = export_store_permutation(vec![index_equality, array_equality], &terms);
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule arrays_ext"), "{output}");
    assert!(!output.contains("(choice ((x "), "{output}");
}

/// AY stores `((as const (Array I E)) v)` as the internal application
/// `(const-array v)` (`TermStore::mk_const_array`). SMT-LIB has no such
/// function, so printing it verbatim makes an external checker reject the whole
/// document at the PARSER — `identifier 'const-array' is not defined`, i.e.
/// `invalid`, which is strictly worse than a `hole` because no rule can run on
/// a file that does not parse. The printer must emit the SMT-LIB spelling, with
/// the mandatory sort annotation recovered from the term's own sort.
#[test]
fn const_array_prints_as_the_smtlib_as_const_spelling() {
    let mut terms = TermStore::new();
    let fill = terms.mk_var("fill", Sort::bitvec(8));
    let array = terms.mk_const_array(Sort::bitvec(64), fill);

    assert_eq!(
        format_term_alethe(&terms, array),
        "((as const (Array (_ BitVec 64) (_ BitVec 8))) fill)"
    );
}

/// The rewrite is keyed on BOTH the internal name and an `Array` sort whose
/// element sort is the argument's, so an ordinary user function that happens to
/// be spelled `const-array` keeps its plain application rendering.
#[test]
fn a_non_array_sorted_const_array_application_keeps_its_plain_rendering() {
    let mut terms = TermStore::new();
    let fill = terms.mk_var("fill", Sort::bitvec(8));
    let impostor = terms.mk_app(Symbol::named("const-array"), [fill], Sort::bitvec(8));

    assert_eq!(format_term_alethe(&terms, impostor), "(const-array fill)");
}
