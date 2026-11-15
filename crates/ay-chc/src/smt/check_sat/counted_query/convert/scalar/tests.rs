// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use crate::{ChcOp, ChcSort, ChcVar};
use ay_core::original_query::{CountedAdmissionError, FiniteAdmissionGrant};
use ay_sat::{Literal, SatResult, Solver};
use std::sync::Arc;

mod arrays;
mod bootstrap;
mod resources;

pub(super) fn owner(work: u64, bytes: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

pub(super) fn ample() -> CountedAdmission {
    owner(100_000_000, 1 << 30)
}

pub(super) fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

pub(super) fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

pub(super) fn convert<'a>(source: &'a ChcExpr, owner: &CountedAdmission) -> Result<Converted<'a>> {
    crate::smt::check_sat::counted_query::read(source, owner)?.into_terms()
}

pub(super) fn formula() -> ChcExpr {
    op(
        ChcOp::And,
        vec![
            var("same", ChcSort::Bool),
            op(
                ChcOp::Eq,
                vec![var("same", ChcSort::BitVec(8)), ChcExpr::BitVec(7, 8)],
            ),
            op(
                ChcOp::Eq,
                vec![
                    var("same", ChcSort::BitVec(64)),
                    ChcExpr::BitVec(0xfedc_ba98_7654_3210, 64),
                ],
            ),
            op(
                ChcOp::Eq,
                vec![
                    op(
                        ChcOp::Ite,
                        vec![
                            var("same", ChcSort::Bool),
                            var("same", ChcSort::BitVec(8)),
                            op(
                                ChcOp::BvExtract(7, 0),
                                vec![var("same", ChcSort::BitVec(64))],
                            ),
                        ],
                    ),
                    ChcExpr::BitVec(7, 8),
                ],
            ),
            op(
                ChcOp::Ne,
                vec![var("same", ChcSort::BitVec(8)), ChcExpr::BitVec(8, 8)],
            ),
        ],
    )
}

// Independent TEST oracle only. Its search is intentionally outside the
// attachment receipt: no counted production SAT search is claimed.
pub(super) enum OracleRows {
    Attached,
    WithoutLinks,
}

pub(super) fn solve(encoding: &ScalarEncoding<'_, '_>, rows: OracleRows) -> SatResult {
    let mut solver = Solver::new(encoding.num_vars() as usize);
    for row in encoding.rows() {
        if matches!(rows, OracleRows::Attached) || !matches!(row.origin(), RowOrigin::Link { .. }) {
            solver.add_clause(
                row.literals()
                    .iter()
                    .copied()
                    .map(Literal::from_dimacs)
                    .collect(),
            );
        }
    }
    solver.solve().into_inner()
}

pub(super) fn model(encoding: &ScalarEncoding<'_, '_>) -> Vec<bool> {
    let SatResult::Sat(model) = solve(encoding, OracleRows::Attached) else {
        panic!("the independent oracle must find the supported source model");
    };
    model
}

#[test]
fn authentic_attachment_preserves_every_row_link_root_and_gate_ledger() {
    let source = formula();
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            assert!(std::ptr::eq(encoding.context.original(), &source));
            assert_eq!(encoding.source_cnf().roots(), &[encoding.context.root()]);
            assert!(!encoding.source_cnf().steps().is_empty());
            assert!(!encoding.source_cnf().bridges().is_empty());
            assert_eq!(
                encoding.links.len(),
                encoding.source_cnf().num_vars() as usize
            );
            assert_eq!(
                encoding.rows().len(),
                encoding.cnf.rows().len()
                    + encoding.bv.clauses().map_err(bv_error)?.len()
                    + 2 * encoding.links.len()
            );
            for link in &encoding.links {
                assert_eq!(encoding.cnf.sat_literal_term(link.boolean)?, link.source);
                assert_eq!(encoding.cnf.literal_for_term(link.source)?, link.boolean);
                assert_eq!(
                    attachment::shifted(
                        encoding.bv.literal(link.source).map_err(bv_error)?,
                        encoding.offset
                    )?,
                    link.bitvector
                );
            }
            for row in encoding.rows() {
                let expected = match row.origin() {
                    RowOrigin::Boolean(index) => encoding.cnf.rows()[index].literals().to_vec(),
                    RowOrigin::Bitvector(index) => encoding.bv.clauses().map_err(bv_error)?[index]
                        .literals()
                        .iter()
                        .map(|lit| attachment::shifted(*lit, encoding.offset).unwrap())
                        .collect(),
                    RowOrigin::Link { index, reverse } => {
                        let link = encoding.links[index];
                        if reverse {
                            vec![link.boolean, -link.bitvector]
                        } else {
                            vec![-link.boolean, link.bitvector]
                        }
                    }
                    RowOrigin::ArrayRead(_) => {
                        panic!("scalar-only source acquired an array premise")
                    }
                };
                assert_eq!(row.literals(), expected);
            }
            let bv = encoding.bitvector_encoding();
            assert!(!bv.and_gates().map_err(bv_error)?.is_empty());
            assert!(!bv.mux_gates().map_err(bv_error)?.is_empty());
            let candidate = encoding.check_scalar_candidate(&model(encoding))?;
            assert_eq!(
                candidate.values(),
                &[
                    ScalarValue::Bool(true),
                    ScalarValue::BitVec(7, 8),
                    ScalarValue::BitVec(0xfedc_ba98_7654_3210, 64)
                ]
            );
            encoding.replay_scalar_candidate(&candidate)
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn absent_links_make_the_false_source_satisfiable_but_never_an_accepted_candidate() {
    let source = op(
        ChcOp::And,
        vec![
            var("p", ChcSort::Bool),
            op(
                ChcOp::Eq,
                vec![
                    op(
                        ChcOp::Ite,
                        vec![
                            var("p", ChcSort::Bool),
                            ChcExpr::BitVec(0, 8),
                            ChcExpr::BitVec(1, 8),
                        ],
                    ),
                    ChcExpr::BitVec(1, 8),
                ],
            ),
        ],
    );
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            assert!(matches!(
                solve(encoding, OracleRows::Attached),
                SatResult::Unsat(_)
            ));
            let SatResult::Sat(disconnected) = solve(encoding, OracleRows::WithoutLinks) else {
                panic!("the missing-link control must actually be satisfiable");
            };
            assert!(matches!(
                encoding.check_scalar_candidate(&disconnected),
                Err(Error::InvalidCandidate)
            ));
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn identical_numeric_namespaces_do_not_authorize_cross_run_replay() {
    let source = formula();
    let mut left = convert(&source, &ample()).unwrap();
    let mut right = convert(&source, &ample()).unwrap();
    left.with_scalar_encoding(|a| {
        right.with_scalar_encoding(|b| {
            assert_eq!(a.num_vars(), b.num_vars());
            let candidate = a.check_scalar_candidate(&model(a))?;
            assert_eq!(
                b.replay_scalar_candidate(&candidate),
                Err(Error::InvalidCandidate)
            );
            a.replay_scalar_candidate(&candidate)
        })
    })
    .unwrap();
    left.finish().unwrap();
    right.finish().unwrap();
}

#[test]
fn missing_extra_and_mutated_sat_assignments_are_rejected() {
    let source = formula();
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let mut assignment = model(encoding);
            assert!(encoding.check_scalar_candidate(&assignment).is_ok());
            assert!(matches!(
                encoding.check_scalar_candidate(&assignment[..assignment.len() - 1]),
                Err(Error::InvalidCandidate)
            ));
            assignment.push(false);
            assert!(matches!(
                encoding.check_scalar_candidate(&assignment),
                Err(Error::InvalidCandidate)
            ));
            assignment.pop();
            let root = encoding.cnf.literal_for_term(encoding.context.root())?;
            assignment[root.unsigned_abs() as usize - 1] ^= true;
            assert!(matches!(
                encoding.check_scalar_candidate(&assignment),
                Err(Error::InvalidCandidate)
            ));
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn boolean_aliases_inside_bitvector_ite_keep_the_original_value() {
    let p = Arc::new(var("p", ChcSort::Bool));
    let not = Arc::new(ChcExpr::Op(ChcOp::Not, vec![p.clone()]));
    let alias = Arc::new(ChcExpr::Op(ChcOp::Not, vec![not.clone()]));
    let term = Arc::new(ChcExpr::Op(
        ChcOp::Ite,
        vec![
            alias.clone(),
            Arc::new(ChcExpr::BitVec(7, 8)),
            Arc::new(ChcExpr::BitVec(9, 8)),
        ],
    ));
    let source = ChcExpr::Op(
        ChcOp::And,
        vec![
            p.clone(),
            Arc::new(ChcExpr::Op(
                ChcOp::Eq,
                vec![term, Arc::new(ChcExpr::BitVec(7, 8))],
            )),
        ],
    );
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let literal = |node: &ChcExpr| -> Result<_> {
                Ok(encoding
                    .cnf
                    .literal_for_term(encoding.context.term_for(node)?)?)
            };
            assert_eq!(literal(&p)?, literal(&alias)?);
            assert_eq!(literal(&p)?, -literal(&not)?);
            let candidate = encoding.check_scalar_candidate(&model(encoding))?;
            assert_eq!(candidate.values(), &[ScalarValue::Bool(true)]);
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn closed_array_reads_attach_but_retain_unchecked_theory_premises() {
    let source = op(
        ChcOp::Eq,
        vec![
            op(
                ChcOp::Select,
                vec![
                    ChcExpr::ConstArray(ChcSort::BitVec(8), Arc::new(ChcExpr::Bool(true))),
                    ChcExpr::BitVec(0, 8),
                ],
            ),
            ChcExpr::Bool(true),
        ],
    );
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let closure = encoding.array_read_obligations().unwrap();
            assert_eq!(closure.steps().len(), 1);
            assert_eq!(encoding.cnf.roots(), closure.roots());
            assert!(matches!(
                closure.steps()[0].derivation(),
                ay_arrays::counted_reads::Derivation::ConstFill { .. }
            ));
            let candidate = encoding.check_scalar_candidate(&model(encoding))?;
            encoding.replay_scalar_candidate(&candidate)
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn wide_circuit_is_exact_while_scalar_replay_explicitly_declines() {
    let source = op(
        ChcOp::Eq,
        vec![var("wide", ChcSort::BitVec(129)), ChcExpr::BitVec(0, 129)],
    );
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let variable = encoding.context.bindings()[0].term;
            assert_eq!(encoding.bv.bits(variable).map_err(bv_error)?.len(), 129);
            assert!(matches!(
                encoding.check_scalar_candidate(&model(encoding)),
                Err(Error::Unsupported)
            ));
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn checked_namespace_layout_never_wraps_or_accepts_zero_literals() {
    assert_eq!(attachment::layout(u32::MAX, 1), Err(Error::IllTyped));
    assert_eq!(attachment::layout(i32::MAX as u32, 1), Err(Error::IllTyped));
    assert_eq!(attachment::layout(3, 7), Ok((3, 10)));
    assert_eq!(attachment::shifted(0, 1), Err(Error::IllTyped));
    assert_eq!(attachment::shifted(i32::MIN, 0), Err(Error::IllTyped));
    assert_eq!(
        attachment::shifted(1, i32::MAX as u32),
        Err(Error::IllTyped)
    );
    assert_eq!(attachment::shifted(-7, 11), Ok(-18));
}
