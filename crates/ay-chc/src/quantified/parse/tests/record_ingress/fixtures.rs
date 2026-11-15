// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

pub(super) fn record() -> &'static str {
    "(declare-datatype Vec ((mkVec
        (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
        (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))"
}

pub(super) fn resize() -> String {
    format!(
        "(set-logic HORN){}
        (declare-var v Vec)(declare-var out Vec)
        (declare-var fresh_data (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-var new (_ BitVec 64))(declare-var old (_ BitVec 64))
        (declare-var fill (_ BitVec 8))(declare-var j (_ BitVec 64))
        (declare-rel R (Vec (_ BitVec 64) (_ BitVec 64) (_ BitVec 8)))
        (declare-rel error ())
        (rule (=> (and
          (forall ((i (_ BitVec 64)))
            (and (=> (bvult i (fld_len v))
                     (= (select fresh_data i) (select (fld_data v) i)))
                 (=> (and (bvuge i (fld_len v)) (bvult i new))
                     (= (select fresh_data i) fill))))
          (= out (mkVec (fld_ptr v) new (fld_cap v)
                   (ite (bvult (fld_len v) new) fresh_data (fld_data v)))))
          (R out (fld_len v) new fill)))
        (rule (=> (and (R out old new fill) (bvuge j old) (bvult j new)
                       (bvuge j (_ bv32 64))
                       (distinct (select (fld_data out) j) fill)) error))
        (query error)",
        record()
    )
}

pub(super) fn refuses(input: &str) {
    let error =
        super::QuantifiedChcProblem::parse_smtlib(input).expect_err("unsupported record input");
    assert!(
        matches!(
            error,
            super::ChcError::Parse(_) | super::ChcError::Verification(_)
        ),
        "{error:?}"
    );
}
