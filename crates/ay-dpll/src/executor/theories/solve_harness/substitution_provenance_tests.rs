// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn constant_rewrite_never_borrows_its_old_singleton_source() {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(
        "(set-logic QF_UFLIA) (declare-const x Int)
         (declare-fun f (Int) Int)
         (assert (= x 4)) (assert (<= (f x) 0))",
    )
    .expect("source parses");
    executor.execute_all(&commands).expect("source installs");
    let originals = executor.ctx.assertions.clone();
    let mut pending = vec![originals[1]];
    let symbol = loop {
        let term = pending.pop().expect("original UF call");
        if let TermData::App(symbol, args) = executor.ctx.terms.get(term) {
            if !crate::features::is_builtin_symbol_name(symbol.name()) && args.len() == 1 {
                break symbol.clone();
            }
        }
        pending.extend(executor.ctx.terms.children(term));
    };
    let four = executor.ctx.terms.mk_int(4.into());
    let rewritten_call = executor.ctx.terms.mk_app(symbol, [four], Sort::Int);
    let (rewritten, provenance, _) = executor.preprocess_auflia_assertions_with_proof_provenance();
    let contains_rewrite = |root| {
        crate::executor::theories::reachable_term_set(&executor.ctx.terms, &[root])
            .contains(&rewritten_call)
    };
    assert!(
        rewritten.iter().any(|&root| contains_rewrite(root)),
        "constant substitution must fire"
    );
    for (root, groups) in &provenance.assertion_sources {
        if contains_rewrite(*root) {
            assert!(
                groups.iter().all(|group| group.contains(&originals[0])),
                "rewritten UF row needs the licensing definition: {groups:?}"
            );
        }
    }
    assert_eq!(provenance.original_problem_assertions, originals);
}
