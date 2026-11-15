// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded DATA constructor/parser/evaluator oracle; no native SAT credential.

use ay_core::{Sort, TermData, TermId, TermStore};
use ay_frontend::parse;
use ay_model_check::{ArraySnapshot, ArrayValue, Evaluator, ModelValue, ModelView};
use num_bigint::BigInt;
use num_traits::One;
use std::sync::Arc;

use crate::Executor;

struct Empty;
impl ModelView for Empty {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }
}

fn bv(value: u64, width: u32) -> ModelValue {
    ModelValue::bitvec(value.into(), width)
}

fn fixture(width: u32) -> Arc<ArraySnapshot> {
    let default = ModelValue::BitVec {
        value: (BigInt::one() << width) - 1,
        width,
    };
    let array_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(width));
    let old = ArraySnapshot::finite(
        ArrayValue {
            default,
            store: vec![(bv(u64::MAX, 64), bv(7, width)), (bv(0, 64), bv(9, width))],
        },
        &array_sort,
        &mut 100_000,
    )
    .expect("original immutable DATA");
    ArraySnapshot::range_copy(
        Arc::clone(&old),
        old,
        &bv(1, 64),
        &bv(3, 64),
        &bv(u64::MAX, 64),
        &mut 1000,
    )
    .expect("shared captured range")
}

fn parsed_snapshot(source: &str, width: u32) -> Arc<ArraySnapshot> {
    let script = format!(
        "(declare-fun pin () (Array (_ BitVec 64) (_ BitVec {width}))) (assert (= pin {source}))"
    );
    let mut exec = Executor::new();
    exec.execute_all(&parse(&script).expect("complete text parser"))
        .expect("elaboration only, no check-sat");
    let root = *exec.ctx.assertions.first().expect("whole equality");
    let TermData::App(_, args) = exec.ctx.terms.get(root) else {
        panic!("array equality")
    };
    assert_eq!(args.len(), 2);
    Evaluator::new(&exec.ctx.terms, &Empty)
        .capture_array_snapshot(args[1])
        .expect("whole parsed value")
}

#[test]
fn closed_snapshot_constructor_matches_reparsed_whole_bv128_and_modular_range() {
    for width in [8, 128] {
        let original = fixture(width);
        let mut work = 1_000_000_000usize;
        let mut bytes = 1_000_000_000usize;
        let mut refused = false;
        let mut progress = |w: usize, b: usize| {
            if refused {
                return false;
            }
            match (work.checked_sub(w), bytes.checked_sub(b)) {
                (Some(w), Some(b)) => {
                    work = w;
                    bytes = b;
                    true
                }
                _ => {
                    refused = true;
                    false
                }
            }
        };
        let topology = original
            .topology_with_progress(&mut progress)
            .expect("same original prepaid export");
        let mut terms = TermStore::new();
        let id = topology
            .try_to_term_with_progress(&mut terms, &mut progress)
            .expect("closed whole term");
        drop(topology);
        assert!(progress(0, 0));
        let constructed = Evaluator::new(&terms, &Empty)
            .capture_array_snapshot(id)
            .expect("whole constructed value");
        // Serializer/parser/evaluator are independent bounded fixture oracles,
        // not new grants to production constructor or original native replay.
        let source = original
            .to_smtlib(&mut 100_000)
            .expect("complete bounded fixture text");
        let reparsed = parsed_snapshot(&source, width);
        assert!(original
            .same_function(&constructed, &mut 100_000)
            .expect("complete original graph"));
        assert!(original
            .same_function(&reparsed, &mut 100_000)
            .expect("complete reparsed graph"));
        for index in [0, 1, 2, 3, u64::MAX] {
            let left = constructed
                .read(&bv(index, 64), &mut 1000)
                .expect("constructed read");
            let right = reparsed
                .read(&bv(index, 64), &mut 1000)
                .expect("reparsed read");
            let (
                ModelValue::BitVec {
                    value: left,
                    width: lw,
                },
                ModelValue::BitVec {
                    value: right,
                    width: rw,
                },
            ) = (left, right)
            else {
                panic!("exact BV")
            };
            assert_eq!(lw, width);
            assert_eq!(rw, width);
            assert_eq!(left, right);
        }
    }
}
