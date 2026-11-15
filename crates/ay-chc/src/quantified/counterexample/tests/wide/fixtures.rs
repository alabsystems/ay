// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
pub(super) enum Table {
    Float32,
    // Historical call-table emulation; current fetched MC emits real UFs for
    // calls. Retained here as the exact128-bit boundary control, not adoption.
    Call,
    Float64,
}

#[derive(Clone, Copy)]
pub(super) enum Cells {
    Filled,
    CorruptLast,
}

impl Table {
    pub(super) fn width(self) -> u32 {
        match self {
            Self::Float32 => 72,
            Self::Call => 128,
            Self::Float64 => 136,
        }
    }

    pub(super) fn keys(self) -> (BigUint, BigUint) {
        let low = match self {
            Self::Float32 => (BigUint::from(2_147_483_651u64) << 32usize) + BigUint::from(9u8),
            Self::Call => (BigUint::from(2_147_483_651u64) << 64usize) + BigUint::from(9u8),
            Self::Float64 => {
                (BigUint::from(9_223_372_036_854_775_811u64) << 64usize) + BigUint::from(9u8)
            }
        };
        let tag_bit = match self {
            Self::Float32 => 66usize,
            Self::Call => 127,
            Self::Float64 => 130,
        };
        let high = &low + (BigUint::from(1u8) << tag_bit);
        (low, high)
    }

    fn text(self, high: bool) -> String {
        // Current floating-point producers use tags 0..=4; 4 denotes REM.
        let (tag, tag_width, lhs, lhs_width, rhs_width) = match self {
            Self::Float32 => (4u64, 8, 2_147_483_651u64, 32, 32),
            Self::Call => (2_147_483_648u64, 32, 2_147_483_651u64, 32, 64),
            Self::Float64 => (4u64, 8, 9_223_372_036_854_775_811u64, 64, 64),
        };
        let tag = if high { tag } else { 0 };
        format!(
            "(concat (_ bv{tag} {tag_width}) (concat (_ bv{lhs} {lhs_width}) (_ bv9 {rhs_width})))"
        )
    }
}

pub(super) fn source(table: Table, cells: Cells, expected: u8) -> QuantifiedChcProblem {
    let width = table.width();
    let low = table.text(false);
    let high = table.text(true);
    let filled = "((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8))";
    let data = match cells {
        Cells::Filled => filled.to_owned(),
        Cells::CorruptLast => format!("(store {filled} (_ bv64 64) (_ bv8 8))"),
    };
    // Authored frozen congruent-table shape. Arbitrary table values are not an
    // implementation or validation of IEEE arithmetic or external call purity.
    QuantifiedChcProblem::parse_smtlib(&format!(
        "(set-logic HORN)
         (declare-fun P ((Array (_ BitVec {width}) (_ BitVec 8)) (_ BitVec {width})
           (_ BitVec {width}) (Array (_ BitVec 64) (_ BitVec 8))) Bool)
         (assert (forall ((table (Array (_ BitVec {width}) (_ BitVec 8)))
             (low (_ BitVec {width})) (high (_ BitVec {width}))
             (data (Array (_ BitVec 64) (_ BitVec 8))))
           (=> (and (= low {low}) (= high {high})
                    (= table (store (store ((as const (Array (_ BitVec {width}) (_ BitVec 8)))
                           (_ bv0 8)) low (_ bv7 8)) high (_ bv9 8)))
                    (= data {data})
                    (forall ((i (_ BitVec 64)))
                      (=> (bvult i (_ bv65 64)) (= (select data i) (_ bv7 8)))))
               (P table low high data))))
         (assert (forall ((table (Array (_ BitVec {width}) (_ BitVec 8)))
             (low (_ BitVec {width})) (high (_ BitVec {width}))
             (data (Array (_ BitVec 64) (_ BitVec 8))))
           (=> (and (P table low high data) (= (select table low) (_ bv7 8))
                    (= (select table high) (_ bv{expected} 8))
                    (distinct (select table low) (select table high))) false)))
         (check-sat)"
    ))
    .expect("bounded wide table source with narrow universal binder")
}
