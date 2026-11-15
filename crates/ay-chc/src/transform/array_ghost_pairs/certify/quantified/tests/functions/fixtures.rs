// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
pub(super) enum Shape {
    Array,
    Vec,
    Nested,
}
#[derive(Clone, Copy)]
pub(super) enum Calls {
    Same,
    Independent,
}
#[derive(Clone, Copy)]
pub(super) enum Query {
    Same,
    Shifted,
}

const FUNCTIONS: &str = "(declare-fun f (Bool (_ BitVec 8)) (_ BitVec 8))
(declare-fun g (Bool (_ BitVec 8)) (_ BitVec 8))
(declare-fun matrix_only ((_ BitVec 64)) (_ BitVec 1))
(declare-fun unused ((_ BitVec 136)) (_ BitVec 1))
(declare-fun __gpi0 () (_ BitVec 1))
(declare-fun __gpc0 () (_ BitVec 1))
(declare-fun |ay!observation!0!0| () (_ BitVec 1))";

pub(super) fn script(shape: Shape, calls: Calls, query: Query) -> String {
    let call = match calls {
        Calls::Same => "f",
        Calls::Independent => "g",
    };
    let expected = match query {
        Query::Same => "fill",
        Query::Shifted => "(bvadd fill (_ bv1 8))",
    };
    let (declarations, arguments, relation, constraint, matrix, guard, read) = match shape {
        Shape::Array => (
            "(declare-var a (Array (_ BitVec 64) (_ BitVec 8)))\n(declare-var length (_ BitVec 64))",
            "a length fill", "(Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 8)",
            "(= length (_ bv65 64))", format!("(=> (bvult i length) (= (select a i) ({call} true x)))"),
            "(and (bvuge k (_ bv32 64)) (bvult k length))", "(select a k)",
        ),
        Shape::Vec => (
            "(declare-datatype Vec ((mkVec (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
                (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
             (declare-var v Vec)(declare-var a (Array (_ BitVec 64) (_ BitVec 8)))",
            "v fill", "Vec (_ BitVec 8)",
            "(= v (mkVec (_ bv0 64) (_ bv65 64) (_ bv65 64) a))",
            format!("(=> (bvult i (fld_len v)) (= (select (fld_data v) i) ({call} true x)))"),
            "(and (bvuge k (_ bv32 64)) (bvult k (fld_len v)))", "(select (fld_data v) k)",
        ),
        Shape::Nested => (
            "(declare-datatype Inner ((mkInner (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
                (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
             (declare-datatype Outer ((mkOuter (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
                (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) Inner)))))
             (declare-var outer Outer)(declare-var rows (Array (_ BitVec 64) Inner))",
            "outer fill", "Outer (_ BitVec 8)",
            "(= outer (mkOuter (_ bv0 64) (_ bv65 64) (_ bv65 64) rows))",
            format!("(=> (and (bvult i (fld_len outer))
                     (bvult j (fld_len (select (fld_data outer) i))))
                  (= (select (fld_data (select (fld_data outer) i)) j) ({call} true x)))"),
            "(and (bvuge row (_ bv32 64)) (bvuge col (_ bv32 64))
                  (bvult row (fld_len outer))
                  (bvult col (fld_len (select (fld_data outer) row))))",
            "(select (fld_data (select (fld_data outer) row)) col)",
        ),
    };
    // One global summary symbol, not an independent choice at every occurrence.
    // No const-array equality: the complete premise supplies the fill property.
    format!(
        "(set-logic HORN)\n{FUNCTIONS}\n{declarations}
       (declare-var x (_ BitVec 8))(declare-var fill (_ BitVec 8))
       (declare-var k (_ BitVec 64))(declare-var row (_ BitVec 64))(declare-var col (_ BitVec 64))
       (declare-rel P ({relation}))(declare-rel error ())
       (rule (=> (and (= fill (f true x)) {constraint}
         (forall ((i (_ BitVec 64)) (j (_ BitVec 64)))
           (and {matrix} (= (matrix_only j) (matrix_only j))))) (P {arguments})))
       (rule (=> (and (P {arguments}) {guard} (distinct {read} {expected})) error))
       (query error)"
    )
}

pub(super) fn source(shape: Shape, calls: Calls, query: Query) -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(&script(shape, calls, query))
        .expect("authored UF array source")
}

/// Untrusted authored interpretation used only to inspect original obligations.
/// Public solve tests must synthesize their own candidate.
pub(super) fn ghost_candidate(
    source: &QuantifiedChcProblem,
    shape: Shape,
    control: &SourceControl<'_>,
) -> GhostSourceCertificate {
    let records = match shape {
        Shape::Array => None,
        Shape::Vec => {
            let projection = RecordProjection::new(source, control).unwrap();
            let projected = projection.project(source, control).unwrap();
            Some(RecordSource {
                projection,
                projected,
            })
        }
        Shape::Nested => panic!("nested arrays require observation layout"),
    };
    let raw = records
        .as_ref()
        .map_or(source.source_problem(), |r| r.projected.source_problem());
    let spec = GhostPairSpec::analyze(raw, 1);
    let predicate = &raw.predicates()[0];
    let vars: Vec<_> = spec
        .extended_sorts(predicate.id, &predicate.arg_sorts)
        .unwrap()
        .into_iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("m{i}"), sort))
        .collect();
    let terms: Vec<_> = vars.iter().cloned().map(ChcExpr::var).collect();
    let (fill, index, cell) = match shape {
        Shape::Array => (2, 3, 4),
        Shape::Vec => (4, 5, 6),
        _ => unreachable!(),
    };
    assert_eq!(terms.len(), cell + 1);
    let guard = ChcExpr::and_all(vec![
        op(ChcOp::BvULt, vec![terms[index].clone(), terms[1].clone()]),
        op(
            ChcOp::BvUGe,
            vec![terms[index].clone(), ChcExpr::BitVec(32, 64)],
        ),
    ]);
    let formula = op(
        ChcOp::Implies,
        vec![guard, ChcExpr::eq(terms[cell].clone(), terms[fill].clone())],
    );
    assert!(!InvariantModel::expr_to_smtlib(&formula).contains("(f "));
    let mut model = InvariantModel::new();
    model.set(predicate.id, PredicateInterpretation::new(vars, formula));
    model.set(
        raw.predicates()[1].id,
        PredicateInterpretation::new(vec![], ChcExpr::Bool(false)),
    );
    GhostSourceCertificate {
        source: Arc::from(source.source_smtlib()),
        interpretation: GhostPairModel {
            spec,
            model,
            executor_term_memory_limit: Some(128 * 1024 * 1024),
        },
        records,
    }
}

pub(super) fn observation_candidate(
    source: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> source_observations::ObservationModel {
    let layout = source_observations::Layout::analyze(source, control).unwrap();
    let predicate = source.source_problem().predicates()[0].id;
    let vars = layout.canonical(predicate).unwrap().to_vec();
    // outer/fill, row/column, outer ptr/len/cap, inner ptr/len/cap, cell.
    assert_eq!(vars.len(), 11);
    let terms: Vec<_> = vars.iter().cloned().map(ChcExpr::var).collect();
    let guard = ChcExpr::and_all(vec![
        op(ChcOp::BvULt, vec![terms[2].clone(), terms[5].clone()]),
        op(ChcOp::BvULt, vec![terms[3].clone(), terms[8].clone()]),
        op(
            ChcOp::BvUGe,
            vec![terms[2].clone(), ChcExpr::BitVec(32, 64)],
        ),
        op(
            ChcOp::BvUGe,
            vec![terms[3].clone(), ChcExpr::BitVec(32, 64)],
        ),
    ]);
    let formula = op(
        ChcOp::Implies,
        vec![guard, ChcExpr::eq(terms[10].clone(), terms[1].clone())],
    );
    let mut model = InvariantModel::new();
    model.set(predicate, PredicateInterpretation::new(vars, formula));
    model.set(
        source.source_problem().predicates()[1].id,
        PredicateInterpretation::new(vec![], ChcExpr::Bool(false)),
    );
    source_observations::ObservationModel { layout, model }
}
