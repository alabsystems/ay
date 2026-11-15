// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! The canonical encoding of one expression node's OWN fields, for its Merkle
//! digest (`digest.rs`).
//!
//! The encoding is the variant's name, then every non-child field in
//! declaration order: integers and strings length-prefixed, widths and flags
//! fixed-width, sorts as their Merkle digests, and the SHAPE of every child
//! list (an n-ary operator's arity, a quantifier's binders and trigger-group
//! lengths), so that the payload followed by the children's digests in
//! [`ExprValue::children`] order determines the node. Children's sorts are
//! not encoded: a child's digest covers its own sort.
//!
//! The match is exhaustive with no wildcard, so a new `ExprValue` variant does
//! not compile until it is given an encoding here.

use num_bigint::BigInt;
use sha2::{Digest, Sha256};

use super::digest::length;
use crate::expr::{Expr, ExprValue, RoundingMode};
use crate::sort::Sort;

/// Writes one node's payload into its digest.
pub(super) struct Payload<'a> {
    hasher: &'a mut Sha256,
    sort_digest: &'a mut dyn FnMut(&Sort) -> [u8; 32],
}

impl<'a> Payload<'a> {
    pub(super) fn new(
        hasher: &'a mut Sha256,
        sort_digest: &'a mut dyn FnMut(&Sort) -> [u8; 32],
    ) -> Self {
        Self {
            hasher,
            sort_digest,
        }
    }

    fn bytes(&mut self, bytes: &[u8]) {
        self.hasher.update(length(bytes.len()));
        self.hasher.update(bytes);
    }

    fn tag(&mut self, tag: &str) {
        self.bytes(tag.as_bytes());
    }

    fn text(&mut self, text: &str) {
        self.bytes(text.as_bytes());
    }

    fn integer(&mut self, value: &BigInt) {
        self.bytes(&value.to_signed_bytes_le());
    }

    fn width(&mut self, value: u32) {
        self.hasher.update(value.to_le_bytes());
    }

    fn flag(&mut self, value: bool) {
        self.hasher.update([u8::from(value)]);
    }

    fn count(&mut self, count: usize) {
        self.hasher.update(length(count));
    }

    fn rounding(&mut self, mode: RoundingMode) {
        let index: u8 = match mode {
            RoundingMode::RNE => 0,
            RoundingMode::RNA => 1,
            RoundingMode::RTP => 2,
            RoundingMode::RTN => 3,
            RoundingMode::RTZ => 4,
        };
        self.hasher.update([index]);
    }

    fn sort(&mut self, sort: &Sort) {
        let digest = (self.sort_digest)(sort);
        self.hasher.update(digest);
    }

    fn binders(&mut self, binders: &[(String, Sort)]) {
        self.count(binders.len());
        for (name, sort) in binders {
            self.text(name);
            self.sort(sort);
        }
    }

    fn groups(&mut self, groups: &[Vec<Expr>]) {
        self.count(groups.len());
        for group in groups {
            self.count(group.len());
        }
    }
}

/// `node_payload(value, payload)`: the exhaustive encoding. Variants whose
/// only fields are children encode their name alone (`tuple`, `record`).
macro_rules! node_payload {
    (
        payload: $payload:ident,
        tuple: [$($tuple:ident),* $(,)?],
        record: [$($record:ident),* $(,)?],
        $($pattern:pat => $encode:block)*
    ) => {
        pub(super) fn node_payload(value: &ExprValue, $payload: &mut Payload<'_>) {
            match value {
                $(ExprValue::$tuple(..) => $payload.tag(stringify!($tuple)),)*
                $(ExprValue::$record { .. } => $payload.tag(stringify!($record)),)*
                $($pattern => $encode)*
            }
        }
    };
}

node_payload! {
    payload: p,
    tuple: [
        Not, Xor, Implies, Eq, BvAdd, BvSub, BvMul, BvUDiv, BvSDiv, BvURem, BvSRem, BvNeg,
        BvNot, BvAnd, BvOr, BvXor, BvShl, BvLShr, BvAShr, BvULt, BvULe, BvUGt, BvUGe, BvSLt,
        BvSLe, BvSGt, BvSGe, BvConcat, BvAddNoOverflowUnsigned, BvAddNoOverflowSigned,
        BvSubNoUnderflowUnsigned, BvSubNoOverflowSigned, BvMulNoOverflowUnsigned,
        BvMulNoOverflowSigned, BvNegNoOverflow, BvSdivNoOverflow, IntAdd, IntSub, IntMul,
        IntDiv, IntMod, IntNeg, IntLt, IntLe, IntGt, IntGe, IntToReal, RealToInt, IsInt,
        RealAdd, RealSub, RealMul, RealDiv, RealNeg, RealLt, RealLe, RealGt, RealGe, FpAbs,
        FpNeg, FpRem, FpTruncatingRem, FpMin, FpMax, FpEq, FpLt, FpLe, FpGt, FpGe, FpIsNaN, FpIsInfinite,
        FpIsZero, FpIsNormal, FpIsSubnormal, FpIsPositive, FpIsNegative, FpToReal, FpFromBvs,
        FpToIeeeBv, Bv2Int, StrConcat, StrLen, StrAt, StrSubstr, StrContains, StrPrefixOf,
        StrSuffixOf, StrIndexOf, StrReplace, StrReplaceAll, StrToInt, StrFromInt, StrToRe,
        StrInRe, ReStar, RePlus, ReUnion, ReConcat, SeqUnit, SeqConcat, SeqLen, SeqNth,
        SeqExtract, SeqContains, SeqPrefixOf, SeqSuffixOf, SeqIndexOf, SeqReplace,
    ],
    record: [
        Ite, Select, Store, ArrayRangeCopy,
    ],
    ExprValue::BoolConst(f0) => { p.tag("BoolConst"); p.flag(*f0); }
    ExprValue::BitVecConst { value, width } => { p.tag("BitVecConst"); p.integer(value); p.width(*width); }
    ExprValue::IntConst(f0) => { p.tag("IntConst"); p.integer(f0); }
    ExprValue::RealConst(f0) => { p.tag("RealConst"); p.integer(f0); }
    ExprValue::Var { name } => { p.tag("Var"); p.text(name); }
    ExprValue::And(f0) => { p.tag("And"); p.count(f0.len()); }
    ExprValue::Or(f0) => { p.tag("Or"); p.count(f0.len()); }
    ExprValue::Distinct(f0) => { p.tag("Distinct"); p.count(f0.len()); }
    ExprValue::BvZeroExtend { extra_bits, .. } => { p.tag("BvZeroExtend"); p.width(*extra_bits); }
    ExprValue::BvSignExtend { extra_bits, .. } => { p.tag("BvSignExtend"); p.width(*extra_bits); }
    ExprValue::BvExtract { high, low, .. } => { p.tag("BvExtract"); p.width(*high); p.width(*low); }
    ExprValue::ConstArray { index_sort, .. } => { p.tag("ConstArray"); p.sort(index_sort); }
    ExprValue::DatatypeConstructor { datatype_name, constructor_name, args } => { p.tag("DatatypeConstructor"); p.text(datatype_name); p.text(constructor_name); p.count(args.len()); }
    ExprValue::DatatypeSelector { datatype_name, selector_name, .. } => { p.tag("DatatypeSelector"); p.text(datatype_name); p.text(selector_name); }
    ExprValue::DatatypeTester { datatype_name, constructor_name, .. } => { p.tag("DatatypeTester"); p.text(datatype_name); p.text(constructor_name); }
    ExprValue::FpPlusInfinity { eb, sb } => { p.tag("FpPlusInfinity"); p.width(*eb); p.width(*sb); }
    ExprValue::FpMinusInfinity { eb, sb } => { p.tag("FpMinusInfinity"); p.width(*eb); p.width(*sb); }
    ExprValue::FpNaN { eb, sb } => { p.tag("FpNaN"); p.width(*eb); p.width(*sb); }
    ExprValue::FpPlusZero { eb, sb } => { p.tag("FpPlusZero"); p.width(*eb); p.width(*sb); }
    ExprValue::FpMinusZero { eb, sb } => { p.tag("FpMinusZero"); p.width(*eb); p.width(*sb); }
    ExprValue::FpAdd(f0, _, _) => { p.tag("FpAdd"); p.rounding(*f0); }
    ExprValue::FpSub(f0, _, _) => { p.tag("FpSub"); p.rounding(*f0); }
    ExprValue::FpMul(f0, _, _) => { p.tag("FpMul"); p.rounding(*f0); }
    ExprValue::FpDiv(f0, _, _) => { p.tag("FpDiv"); p.rounding(*f0); }
    ExprValue::FpFma(f0, _, _, _) => { p.tag("FpFma"); p.rounding(*f0); }
    ExprValue::FpSqrt(f0, _) => { p.tag("FpSqrt"); p.rounding(*f0); }
    ExprValue::FpRoundToIntegral(f0, _) => { p.tag("FpRoundToIntegral"); p.rounding(*f0); }
    ExprValue::FpToSbv(f0, _, f2) => { p.tag("FpToSbv"); p.rounding(*f0); p.width(*f2); }
    ExprValue::FpToUbv(f0, _, f2) => { p.tag("FpToUbv"); p.rounding(*f0); p.width(*f2); }
    ExprValue::BvToFp(f0, _, f2, f3) => { p.tag("BvToFp"); p.rounding(*f0); p.width(*f2); p.width(*f3); }
    ExprValue::BvToFpUnsigned(f0, _, f2, f3) => { p.tag("BvToFpUnsigned"); p.rounding(*f0); p.width(*f2); p.width(*f3); }
    ExprValue::FpToFp(f0, _, f2, f3) => { p.tag("FpToFp"); p.rounding(*f0); p.width(*f2); p.width(*f3); }
    ExprValue::Forall { vars, triggers, .. } => { p.tag("Forall"); p.binders(vars); p.groups(triggers); }
    ExprValue::Exists { vars, triggers, .. } => { p.tag("Exists"); p.binders(vars); p.groups(triggers); }
    ExprValue::Int2Bv(_, f1) => { p.tag("Int2Bv"); p.width(*f1); }
    ExprValue::SeqEmpty(f0) => { p.tag("SeqEmpty"); p.sort(f0); }
    ExprValue::FuncApp { name, args } => { p.tag("FuncApp"); p.text(name); p.count(args.len()); }
}
