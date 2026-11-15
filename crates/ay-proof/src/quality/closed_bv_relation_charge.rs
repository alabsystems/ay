// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Byte precharge for ONE closed BV literal relation, not a truth recognizer.
//!
//! The admitted shape is exactly `(cl (not (= C1 C2)))`, with canonical,
//! same-width1..64 BV literals. `validate_bool_tautology` still runs unchanged:
//! in particular C1=C2 is admitted to this PRICE and rejected by that validator.
//!
//! Its structural clausification probes see at most four nodes and no `and`,
//! `or`, ITE or binder. `bounded_vars` visits those four nodes, with <=4 visited
//! entries, <=3 stack entries and ZERO variable entries. The one assignment
//! allocates an empty environment; its evaluator uses fixed-width u64 values,
//! two at-most64-bit positive BigInt conversions and recursion depth3.
//! There is no width-dependent intermediate or operation beyond equality/Not.
//! Four copies of the authenticated payload plus4096bytes covers these small
//! vectors/sets, call frames and scalar temporaries. Work keeps the existing
//! conservative256-assignment model; byte charging is capped by the old fee.
//! Every other spelling, sort, kind, width or value keeps the old price.

use super::*;
use num_bigint::Sign;

fn canonical(value: &num_bigint::BigInt, width: u32, sort: &Sort) -> bool {
    (1..=u64::BITS).contains(&width)
        && sort == &Sort::bitvec(width)
        && value.sign() != Sign::Minus
        && value.bits() <= u64::from(width)
}

pub(super) fn matches(step: &ProofStep, terms: &TermStore) -> bool {
    let ProofStep::TheoryLemma {
        kind: TheoryLemmaKind::BoolTautology,
        clause,
        ..
    } = step
    else {
        return false;
    };
    let [literal] = clause.as_slice() else {
        return false;
    };
    if terms.entry_stamp(*literal).is_none() || terms.sort(*literal) != &Sort::Bool {
        return false;
    }
    let TermData::Not(equality) = terms.get(*literal) else {
        return false;
    };
    if terms.entry_stamp(*equality).is_none() || terms.sort(*equality) != &Sort::Bool {
        return false;
    }
    let TermData::App(Symbol::Named(op), args) = terms.get(*equality) else {
        return false;
    };
    let [left, right] = args.as_slice() else {
        return false;
    };
    if op != "=" || terms.entry_stamp(*left).is_none() || terms.entry_stamp(*right).is_none() {
        return false;
    }
    let TermData::Const(Constant::BitVec {
        value: lv,
        width: lw,
    }) = terms.get(*left)
    else {
        return false;
    };
    let TermData::Const(Constant::BitVec {
        value: rv,
        width: rw,
    }) = terms.get(*right)
    else {
        return false;
    };
    lw == rw && canonical(lv, *lw, terms.sort(*left)) && canonical(rv, *rw, terms.sort(*right))
}

#[cfg(test)]
mod tests;
