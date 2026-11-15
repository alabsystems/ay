// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
pub(super) enum Table {
    Float32,
    Float64,
}

#[derive(Clone, Copy)]
pub(super) enum Change {
    None,
    IndependentTable,
    OtherTag,
    MissingSuffix,
}

impl Table {
    pub(super) fn cell_width(self) -> u32 {
        match self {
            Self::Float32 => 32,
            Self::Float64 => 64,
        }
    }
    pub(super) fn key_width(self) -> u32 {
        8 + 2 * self.cell_width()
    }
    pub(super) fn key(self, tag: u128) -> ChcExpr {
        let scalar = ChcSort::BitVec(self.cell_width());
        op(
            ChcOp::BvConcat,
            vec![
                op(
                    ChcOp::BvConcat,
                    vec![ChcExpr::BitVec(tag, 8), variable("lhs", &scalar)],
                ),
                variable("rhs", &scalar),
            ],
        )
    }
}

pub(super) fn script(table: Table, change: Change) -> String {
    let w = table.cell_width();
    let key_width = table.key_width();
    let output_table = match change {
        Change::IndependentTable => "other_table",
        _ => "table",
    };
    let query_tag = match change {
        Change::OtherTag => 0,
        _ => 4,
    };
    let suffix = match change {
        Change::MissingSuffix => "true".to_owned(),
        _ => "(=> (and (bvuge i old) (bvult i new))
                    (= (select b i) ((_ extract 7 0) first)))"
            .to_owned(),
    };
    // Authored composition of the current producer's frozen table and resize
    // shapes. The table is arbitrary, not an IEEE implementation. Tag4 is REM;
    // tag0 is ADD. Original scalar operands remain separate state columns.
    format!("(set-logic HORN)
      (declare-var table (Array (_ BitVec {key_width}) (_ BitVec {w})))
      (declare-var other_table (Array (_ BitVec {key_width}) (_ BitVec {w})))
      (declare-var lhs (_ BitVec {w}))(declare-var rhs (_ BitVec {w}))
      (declare-var first (_ BitVec {w}))
      (declare-var a (Array (_ BitVec 64) (_ BitVec 8)))
      (declare-var b (Array (_ BitVec 64) (_ BitVec 8)))
      (declare-var old (_ BitVec 64))(declare-var new (_ BitVec 64))
      (declare-var j (_ BitVec 64))
      (declare-rel P ((Array (_ BitVec {key_width}) (_ BitVec {w}))
        (_ BitVec {w}) (_ BitVec {w}) (_ BitVec {w})
        (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 64)))
      (declare-rel Q ((_ BitVec {w}) (_ BitVec {w})
        (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64)
        (Array (_ BitVec {key_width}) (_ BitVec {w})) (_ BitVec 64) (_ BitVec {w})))
      (declare-rel error ())
      (declare-rel unused ((_ BitVec {w})))
      (rule (=> (and (= first (select table (concat (concat (_ bv4 8) lhs) rhs)))
                    (= old (_ bv32 64)) (= new (_ bv65 64))
                    (forall ((i (_ BitVec 64)))
                      (and (=> (bvult i old) (= (select b i) (select a i))) {suffix})))
                  (P table lhs rhs first b old new)))
      (rule (=> (P table lhs rhs first b old new)
                  (Q first lhs b new {output_table} old rhs)))
      (rule (=> (and (Q first lhs b new table old rhs)
                    (or (distinct (select table (concat (concat (_ bv{query_tag} 8) lhs) rhs)) first)
                        (and (bvuge j old) (bvult j new) (bvuge j (_ bv32 64))
                             (distinct (select b j) ((_ extract 7 0) first))))) error))
      (query error)")
}

pub(super) fn source(table: Table, change: Change) -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(&script(table, change))
        .expect("authored wide readonly table with BV64 resize")
}

pub(super) enum AddTable {
    Arbitrary,
    ThreeAtInput,
}

pub(super) fn ieee_named_add_source(table: AddTable) -> QuantifiedChcProblem {
    let format = Table::Float32;
    let w = format.cell_width();
    let key_width = format.key_width();
    let key = InvariantModel::expr_to_smtlib(&format.key(0));
    let point_constraint = match table {
        AddTable::Arbitrary => "true",
        AddTable::ThreeAtInput => "(= first (_ bv1077936128 32))",
    };
    // Tag0 is the consumer's ADD tag. 1.0 and 2.0 reach its unrefined
    // nonzero/non-NaN branch. Neither that spelling nor the array's name
    // supplies IEEE semantics. The control adds only an explicit point
    // constraint (3.0), not an interpretation of the whole table.
    let script = format!(
        "(set-logic HORN)
         (declare-var float_binop_tbl_f32 (Array (_ BitVec {key_width}) (_ BitVec {w})))
         (declare-var lhs (_ BitVec {w}))(declare-var rhs (_ BitVec {w}))
         (declare-var first (_ BitVec {w}))
         (declare-rel P ((Array (_ BitVec {key_width}) (_ BitVec {w}))
                         (_ BitVec {w}) (_ BitVec {w}) (_ BitVec {w})))
         (declare-rel error ())
         (rule (=> (and (= lhs (_ bv1065353216 32))
                        (= rhs (_ bv1073741824 32))
                        (= first (select float_binop_tbl_f32 {key}))
                        {point_constraint})
                   (P float_binop_tbl_f32 lhs rhs first)))
         (rule (=> (and (P float_binop_tbl_f32 lhs rhs first)
                        (= first (_ bv0 32))
                        (= (select float_binop_tbl_f32 {key}) first)) error))
         (query error)"
    );
    QuantifiedChcProblem::parse_smtlib(&script).expect("arbitrary IEEE-looking table")
}

pub(super) fn candidate(
    source: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> (ChcProblem, source_observations::ObservationModel) {
    let layout = source_observations::Layout::analyze(source, control).unwrap();
    let (raw, pools) = source_observations::test_candidates(source, &layout, control).unwrap();
    let mut model = InvariantModel::new();
    for predicate in source.source_problem().predicates() {
        if predicate.name == "P" || predicate.name == "Q" {
            assert!(
                !pools.get(&predicate.id).unwrap().is_empty(),
                "real query/reverse-CFG candidate"
            );
        }
        let formulas = pools
            .get(&predicate.id)
            .into_iter()
            .flat_map(|pool| pool.iter().map(|c| c.formula.clone()));
        model.set(
            predicate.id,
            PredicateInterpretation::new(
                layout.canonical(predicate.id).unwrap().to_vec(),
                ChcExpr::and_all(formulas),
            ),
        );
    }
    // These are untrusted candidates from real generation, not Houdini results
    // or construction-sealed source evidence. Only native tests solve/recheck.
    (raw, source_observations::ObservationModel { layout, model })
}
