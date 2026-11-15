// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn raw_source_probes_cannot_capture_matrix_only_or_unused_global_functions() {
    let source = QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-fun __gpi0 () (_ BitVec 64))
         (declare-fun __gpi1 () (_ BitVec 64))
         (declare-fun __gpv0 () (_ BitVec 8))
         (declare-rel P ((Array (_ BitVec 64) (_ BitVec 8))))
         (declare-rel error ())
         (declare-var a (Array (_ BitVec 64) (_ BitVec 8)))
         (rule (=> (forall ((i (_ BitVec 64)))
                    (= (select a i) (select a __gpi0))) (P a)))
         (rule (=> (and (P a) (distinct (select a (_ bv0 64))
                                     (select a (_ bv1 64)))) error))
         (query error)",
    )
    .unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let spec = GhostPairSpec::analyze(source.source_problem(), 1);
    let raw = rewrite_source(&source, &spec, &control).unwrap();
    let ClauseHead::Predicate(_, args) = &raw.clauses()[0].head else {
        panic!("fact head")
    };
    for arg in &args[1..] {
        let ChcExpr::Var(var) = arg else {
            panic!("fresh probe")
        };
        assert!(!source
            .function_declarations()
            .iter()
            .any(|f| f.name() == var.name));
    }
    let constraint = raw.clauses()[0].body.constraint.as_ref().unwrap();
    assert!(InvariantModel::expr_to_smtlib(constraint).contains("(select a __gpi0)"));
    assert!(!constraint.vars().iter().any(|var| var.name == "__gpi0"));
}
