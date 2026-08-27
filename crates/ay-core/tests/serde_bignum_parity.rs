// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EXACT-PARITY GATE for the local bignum codec.
//!
//! `serde_bignum_golden.rs` pins the incumbent's ENCODING byte-for-byte and
//! its ACCEPT/REJECT decisions. This file closes the three gaps that gate
//! deliberately leaves open, because each one hides a real difference:
//!
//! * **The rejection message itself.** The golden gate asserts only that a
//!   rejection message is non-empty. Two codecs can agree on rejecting a
//!   document and still disagree on WHICH fault they found. Measured on
//!   `{"Int":[2,[-1]]}` — a bad sign AND a bad limb — the incumbent reports
//!   the sign and a naive `(i8, Vec<u32>)` codec reports the limb.
//! * **Missing fields and tuple arity.** Absent from the golden set entirely.
//! * **Panic vs error.** Probed through `catch_unwind`, so an abort where the
//!   incumbent returned `Err` is a test failure rather than a dead run.
//!
//! The fixture was captured by running this same file against the incumbent —
//! `num-bigint/serde` and `num-rational/serde` enabled, no local codec. Every
//! expected value here is therefore OBSERVED, never invented.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use ay_core::{Constant, FarkasAnnotation, RationalWrapper};
use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use serde::{Deserialize, Serialize};
use std::panic::AssertUnwindSafe;
use std::str::FromStr;

// ------------------------------------------------------------------ records

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct EncodeCase {
    name: String,
    ty: String,
    json: String,
    raw: String,
    /// Decoding `json` again and re-encoding: must be byte-identity.
    reencoded: String,
    /// Structural render of the decoded value.
    decoded_raw: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum Outcome {
    Accept {
        raw: String,
        reencoded: String,
    },
    /// FULL message, position suffix INCLUDED.
    Reject {
        message: String,
        message_trimmed: String,
    },
    Panic {
        message: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct DecodeCase {
    name: String,
    ty: String,
    note: String,
    json: String,
    outcome: Outcome,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct Report {
    schema: String,
    encode: Vec<EncodeCase>,
    decode: Vec<DecodeCase>,
}

// ------------------------------------------------------- structural renders

fn ratio_raw_big(v: &BigRational) -> String {
    format!("numer={} denom={}", v.numer(), v.denom())
}

fn ratio_raw_i64(v: &Rational64) -> String {
    format!("numer={} denom={}", v.numer(), v.denom())
}

fn constant_raw(c: &Constant) -> String {
    match c {
        Constant::Bool(b) => format!("Bool({b})"),
        Constant::Int(i) => format!("Int({i})"),
        Constant::Rational(r) => format!("Rational({})", ratio_raw_big(&r.0)),
        Constant::BitVec { value, width } => format!("BitVec(value={value} width={width})"),
        Constant::String(s) => format!("String({s:?})"),
        other => panic!("unhandled Constant arm: {other:?}"),
    }
}

fn wrapper_raw(w: &RationalWrapper) -> String {
    format!("RationalWrapper({})", ratio_raw_big(&w.0))
}

fn farkas_raw(f: &FarkasAnnotation) -> String {
    let parts: Vec<String> = f.coefficients.iter().map(ratio_raw_i64).collect();
    format!("coefficients=[{}]", parts.join(", "))
}

fn bi(s: &str) -> BigInt {
    BigInt::from_str(s).expect("decimal literal parses")
}

fn trim_position(message: &str) -> String {
    match message.find(" at line ") {
        Some(i) => message[..i].to_string(),
        None => message.to_string(),
    }
}

// -------------------------------------------------------------- probe engine

enum Inner {
    Accept(String, String),
    Reject(String),
}

fn probe<T, F>(json: &str, render: F) -> Outcome
where
    T: serde::de::DeserializeOwned + Serialize,
    F: Fn(&T) -> String,
{
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result =
        std::panic::catch_unwind(AssertUnwindSafe(|| match serde_json::from_str::<T>(json) {
            Ok(v) => Inner::Accept(
                render(&v),
                serde_json::to_string(&v).expect("re-encode decoded value"),
            ),
            Err(e) => Inner::Reject(e.to_string()),
        }));
    std::panic::set_hook(prev);

    match result {
        Ok(Inner::Accept(raw, reencoded)) => Outcome::Accept { raw, reencoded },
        Ok(Inner::Reject(message)) => Outcome::Reject {
            message_trimmed: trim_position(&message),
            message,
        },
        Err(payload) => {
            let message = if let Some(s) = payload.downcast_ref::<&str>() {
                (*s).to_string()
            } else if let Some(s) = payload.downcast_ref::<String>() {
                s.clone()
            } else {
                "<non-string panic payload>".to_string()
            };
            Outcome::Panic { message }
        }
    }
}

// ------------------------------------------------------------- encode corpus

fn encode_constants() -> Vec<(&'static str, Constant)> {
    let mut v: Vec<(&'static str, Constant)> = vec![
        ("bigint/zero", Constant::Int(bi("0"))),
        ("bigint/one", Constant::Int(bi("1"))),
        ("bigint/neg_one", Constant::Int(bi("-1"))),
        ("bigint/u32_max", Constant::Int(bi("4294967295"))),
        ("bigint/two_pow_32", Constant::Int(bi("4294967296"))),
        (
            "bigint/two_pow_64_minus_1",
            Constant::Int(bi("18446744073709551615")),
        ),
        (
            "bigint/two_pow_64",
            Constant::Int(bi("18446744073709551616")),
        ),
        (
            "bigint/two_pow_64_plus_1",
            Constant::Int(bi("18446744073709551617")),
        ),
        (
            "bigint/neg_two_pow_64",
            Constant::Int(bi("-18446744073709551616")),
        ),
        ("bigint/i64_min", Constant::Int(bi("-9223372036854775808"))),
        (
            "bigint/two_pow_128_plus_1",
            Constant::Int(bi("340282366920938463463374607431768211457")),
        ),
        (
            "bigint/large_positive",
            Constant::Int(bi("123456789012345678901234567890")),
        ),
        (
            "bigint/large_negative",
            Constant::Int(bi("-123456789012345678901234567890")),
        ),
        // --- cases NOT in the committed fixture ---
        // Odd u32-word count across three 64-bit limbs: 3*2^64 + 5 -> [5,0,3].
        (
            "bigint/x_odd_word_count",
            Constant::Int(bi("55340232221128654853")),
        ),
        // 2^96 -> [0,0,0,1]: interior zeros AND an even word count.
        (
            "bigint/x_two_pow_96",
            Constant::Int(bi("79228162514264337593543950336")),
        ),
        // 2^64 * (2^32) = 2^96 already covered; this is 2^63 (i64::MAX + 1) positive.
        (
            "bigint/x_two_pow_63",
            Constant::Int(bi("9223372036854775808")),
        ),
        ("bigint/x_neg_u32_max", Constant::Int(bi("-4294967295"))),
    ];
    v.extend(vec![
        ("constant/bool_true", Constant::Bool(true)),
        ("constant/bool_false", Constant::Bool(false)),
        (
            "constant/string",
            Constant::String("hello \"world\"".to_string()),
        ),
        (
            "constant/int_neg",
            Constant::Int(bi("-18446744073709551617")),
        ),
        (
            "constant/rational_neg_denom_raw",
            Constant::Rational(RationalWrapper(BigRational::new_raw(bi("3"), bi("-4")))),
        ),
        (
            "constant/bitvec_zero_width8",
            Constant::BitVec {
                value: bi("0"),
                width: 8,
            },
        ),
        (
            "constant/bitvec_straddle_width65",
            Constant::BitVec {
                value: bi("18446744073709551617"),
                width: 65,
            },
        ),
        // --- not in the committed fixture ---
        (
            "constant/x_bitvec_width0",
            Constant::BitVec {
                value: bi("0"),
                width: 0,
            },
        ),
        (
            "constant/x_bitvec_width_max",
            Constant::BitVec {
                value: bi("1"),
                width: u32::MAX,
            },
        ),
        ("constant/x_string_empty", Constant::String(String::new())),
        (
            "constant/x_string_unicode",
            Constant::String("λ\u{1F600}\n\t".to_string()),
        ),
    ]);
    v
}

fn encode_wrappers() -> Vec<(&'static str, RationalWrapper)> {
    vec![
        (
            "bigrational/zero",
            RationalWrapper(BigRational::new(bi("0"), bi("1"))),
        ),
        (
            "bigrational/one",
            RationalWrapper(BigRational::new(bi("1"), bi("1"))),
        ),
        (
            "bigrational/neg_numer",
            RationalWrapper(BigRational::new(bi("-3"), bi("4"))),
        ),
        (
            "bigrational/neg_denom_normalized",
            RationalWrapper(BigRational::new(bi("3"), bi("-4"))),
        ),
        (
            "bigrational/neg_denom_raw",
            RationalWrapper(BigRational::new_raw(bi("3"), bi("-4"))),
        ),
        (
            "bigrational/unreduced_raw",
            RationalWrapper(BigRational::new_raw(bi("2"), bi("4"))),
        ),
        (
            "bigrational/multilimb",
            RationalWrapper(BigRational::new_raw(
                bi("18446744073709551617"),
                bi("-36893488147419103232"),
            )),
        ),
        // --- not in the committed fixture ---
        (
            "bigrational/x_both_negative_raw",
            RationalWrapper(BigRational::new_raw(bi("-3"), bi("-4"))),
        ),
        (
            "bigrational/x_zero_numer_neg_denom_raw",
            RationalWrapper(BigRational::new_raw(bi("0"), bi("-1"))),
        ),
    ]
}

fn encode_farkas() -> Vec<(&'static str, FarkasAnnotation)> {
    vec![
        ("farkas/empty", FarkasAnnotation::new(vec![])),
        (
            "farkas/zero",
            FarkasAnnotation::new(vec![Rational64::new(0, 1)]),
        ),
        (
            "farkas/one",
            FarkasAnnotation::new(vec![Rational64::new(1, 1)]),
        ),
        (
            "farkas/neg_numer",
            FarkasAnnotation::new(vec![Rational64::new(-3, 4)]),
        ),
        (
            "farkas/neg_denom_normalized",
            FarkasAnnotation::new(vec![Rational64::new(3, -4)]),
        ),
        (
            "farkas/neg_denom_raw",
            FarkasAnnotation::new(vec![Rational64::new_raw(3, -4)]),
        ),
        (
            "farkas/unreduced_raw",
            FarkasAnnotation::new(vec![Rational64::new_raw(2, 4)]),
        ),
        (
            "farkas/i64_extremes",
            FarkasAnnotation::new(vec![Rational64::new_raw(i64::MIN, i64::MAX)]),
        ),
        (
            "farkas/realistic_vector",
            FarkasAnnotation::new(vec![
                Rational64::new(1, 1),
                Rational64::new(-3, 4),
                Rational64::new(0, 1),
                Rational64::new_raw(7, 2),
            ]),
        ),
        // --- not in the committed fixture ---
        (
            "farkas/x_denom_i64_min",
            FarkasAnnotation::new(vec![Rational64::new_raw(1, i64::MIN)]),
        ),
        (
            "farkas/x_both_i64_min",
            FarkasAnnotation::new(vec![Rational64::new_raw(i64::MIN, i64::MIN)]),
        ),
    ]
}

fn build_encode() -> Vec<EncodeCase> {
    let mut out = Vec::new();

    for (name, value) in encode_constants() {
        let json = serde_json::to_string(&value).expect("encode Constant");
        let back: Constant = serde_json::from_str(&json).expect("decode own output");
        out.push(EncodeCase {
            name: name.to_string(),
            ty: "Constant".to_string(),
            raw: constant_raw(&value),
            decoded_raw: constant_raw(&back),
            reencoded: serde_json::to_string(&back).expect("re-encode"),
            json,
        });
    }
    for (name, value) in encode_wrappers() {
        let json = serde_json::to_string(&value).expect("encode RationalWrapper");
        let back: RationalWrapper = serde_json::from_str(&json).expect("decode own output");
        out.push(EncodeCase {
            name: name.to_string(),
            ty: "RationalWrapper".to_string(),
            raw: wrapper_raw(&value),
            decoded_raw: wrapper_raw(&back),
            reencoded: serde_json::to_string(&back).expect("re-encode"),
            json,
        });
    }
    for (name, value) in encode_farkas() {
        let json = serde_json::to_string(&value).expect("encode FarkasAnnotation");
        let back: FarkasAnnotation = serde_json::from_str(&json).expect("decode own output");
        out.push(EncodeCase {
            name: name.to_string(),
            ty: "FarkasAnnotation".to_string(),
            raw: farkas_raw(&value),
            decoded_raw: farkas_raw(&back),
            reencoded: serde_json::to_string(&back).expect("re-encode"),
            json,
        });
    }
    out
}

// ------------------------------------------------------------- decode corpus

/// `(name, note, json)` decoded as `Constant`.
fn decode_constants() -> Vec<(&'static str, &'static str, &'static str)> {
    vec![
        // ---- the committed set ----
        (
            "decode/bigint/nosign_with_limbs",
            "sign 0 with limbs: from_biguint CLEARS them",
            r#"{"Int":[0,[1,2]]}"#,
        ),
        (
            "decode/bigint/plus_with_empty_limbs",
            "sign 1, no limbs: sign DEMOTED to 0",
            r#"{"Int":[1,[]]}"#,
        ),
        (
            "decode/bigint/trailing_zero_limb",
            "trailing zero limb trimmed; re-encode != input",
            r#"{"Int":[-1,[3,0]]}"#,
        ),
        (
            "decode/bigint/bad_sign",
            "sign outside {-1,0,1} must be REJECTED",
            r#"{"Int":[2,[1]]}"#,
        ),
        (
            "decode/bigint/limb_overflows_u32",
            "limb above u32::MAX must be REJECTED",
            r#"{"Int":[1,[4294967296]]}"#,
        ),
        (
            "decode/bigint/negative_limb",
            "limbs are unsigned",
            r#"{"Int":[1,[-1]]}"#,
        ),
        (
            "decode/rational/unreduced_preserved",
            "new_raw: 2/4 stays 2/4",
            r#"{"Rational":[[1,[2]],[1,[4]]]}"#,
        ),
        (
            "decode/rational/zero_denominator",
            "zero denominator REJECTED",
            r#"{"Rational":[[1,[1]],[0,[]]]}"#,
        ),
        (
            "decode/bitvec/unknown_field",
            "deny_unknown_fields: extra key REJECTED",
            r#"{"BitVec":{"value":[0,[]],"width":8,"extra":1}}"#,
        ),
        // ---- ERROR ORDER: two faults in one document, which one is reported? ----
        (
            "decode/x/order_bad_sign_and_bad_limb",
            "ORDER: bad sign in elem 0 AND negative limb in elem 1",
            r#"{"Int":[2,[-1]]}"#,
        ),
        (
            "decode/x/order_bad_sign_and_limb_overflow",
            "ORDER: bad sign AND limb > u32::MAX",
            r#"{"Int":[3,[4294967296]]}"#,
        ),
        (
            "decode/x/order_numer_bad_sign_and_zero_denom",
            "ORDER: bad sign in numerator AND zero denominator",
            r#"{"Rational":[[7,[1]],[0,[]]]}"#,
        ),
        (
            "decode/x/order_bad_numer_and_bad_denom",
            "ORDER: both members malformed",
            r#"{"Rational":[[7,[1]],[9,[1]]]}"#,
        ),
        // ---- MISSING FIELDS (absent from the committed set entirely) ----
        (
            "decode/x/bitvec_missing_width",
            "MISSING FIELD width",
            r#"{"BitVec":{"value":[0,[]]}}"#,
        ),
        (
            "decode/x/bitvec_missing_value",
            "MISSING FIELD value",
            r#"{"BitVec":{"width":8}}"#,
        ),
        (
            "decode/x/bitvec_missing_both",
            "MISSING both named fields",
            r#"{"BitVec":{}}"#,
        ),
        (
            "decode/x/bitvec_null_value",
            "null for a bignum field",
            r#"{"BitVec":{"value":null,"width":8}}"#,
        ),
        (
            "decode/x/bitvec_field_order_swapped",
            "named fields out of declaration order: accepted, re-encoded canonically",
            r#"{"BitVec":{"width":8,"value":[1,[1]]}}"#,
        ),
        (
            "decode/x/bitvec_duplicate_field",
            "duplicate named field",
            r#"{"BitVec":{"value":[0,[]],"width":8,"width":9}}"#,
        ),
        // ---- TUPLE ARITY ----
        (
            "decode/x/bigint_tuple_short",
            "1-element tuple where 2 required",
            r#"{"Int":[1]}"#,
        ),
        (
            "decode/x/bigint_tuple_empty",
            "empty tuple",
            r#"{"Int":[]}"#,
        ),
        (
            "decode/x/bigint_tuple_long",
            "3-element tuple",
            r#"{"Int":[1,[1],9]}"#,
        ),
        (
            "decode/x/rational_tuple_short",
            "ratio with only a numerator",
            r#"{"Rational":[[1,[1]]]}"#,
        ),
        // ---- TYPE ERRORS (the `expecting` string is part of the message) ----
        (
            "decode/x/bigint_limbs_not_seq",
            "limbs field is a string, not a sequence",
            r#"{"Int":[1,"x"]}"#,
        ),
        (
            "decode/x/bigint_limbs_object",
            "limbs field is an object",
            r#"{"Int":[1,{}]}"#,
        ),
        (
            "decode/x/bigint_sign_is_string",
            "sign is a string",
            r#"{"Int":["1",[1]]}"#,
        ),
        (
            "decode/x/bigint_sign_is_float",
            "sign is a float",
            r#"{"Int":[1.5,[1]]}"#,
        ),
        (
            "decode/x/bigint_limb_is_float",
            "limb is a float",
            r#"{"Int":[1,[1.5]]}"#,
        ),
        (
            "decode/x/bigint_not_a_seq",
            "Int payload is a bare integer",
            r#"{"Int":5}"#,
        ),
        // ---- DENORMALIZED-TO-ZERO DENOMINATOR ----
        (
            "decode/x/rational_denom_neg_sign_empty_limbs",
            "denom sign -1 with EMPTY limbs normalizes to 0: reject or accept?",
            r#"{"Rational":[[1,[1]],[-1,[]]]}"#,
        ),
        (
            "decode/x/rational_denom_zero_limbs",
            "denom sign 1 with an explicit zero limb",
            r#"{"Rational":[[1,[1]],[1,[0]]]}"#,
        ),
        (
            "decode/x/rational_both_negative_raw",
            "both members negative, unreduced",
            r#"{"Rational":[[-1,[2]],[-1,[4]]]}"#,
        ),
        // ---- ENUM-LEVEL ----
        (
            "decode/x/unknown_variant",
            "unknown enum variant",
            r#"{"Nope":1}"#,
        ),
        (
            "decode/x/no_variant",
            "empty object: no variant selected",
            r#"{}"#,
        ),
        (
            "decode/x/two_variants",
            "two variants in one object",
            r#"{"Int":[0,[]],"Bool":true}"#,
        ),
        (
            "decode/x/bool_ok",
            "control: an unrelated variant still decodes",
            r#"{"Bool":true}"#,
        ),
    ]
}

/// `(name, note, json)` decoded as `FarkasAnnotation`.
fn decode_farkas() -> Vec<(&'static str, &'static str, &'static str)> {
    vec![
        // ---- the committed set ----
        (
            "decode/farkas/unreduced_preserved",
            "2/4 stays 2/4",
            r#"{"coefficients":[[2,4]]}"#,
        ),
        (
            "decode/farkas/neg_denom_preserved",
            "negative denominator survives",
            r#"{"coefficients":[[3,-4]]}"#,
        ),
        (
            "decode/farkas/zero_denominator",
            "zero denominator REJECTED",
            r#"{"coefficients":[[1,0]]}"#,
        ),
        (
            "decode/farkas/unknown_field",
            "deny_unknown_fields: extra key REJECTED",
            r#"{"coefficients":[[1,1]],"extra":2}"#,
        ),
        (
            "decode/farkas/numer_overflows_i64",
            "coefficients are i64",
            r#"{"coefficients":[[9223372036854775808,1]]}"#,
        ),
        // ---- MISSING FIELD ----
        (
            "decode/x/farkas_missing_field",
            "MISSING FIELD coefficients",
            r#"{}"#,
        ),
        (
            "decode/x/farkas_null_field",
            "coefficients is null",
            r#"{"coefficients":null}"#,
        ),
        (
            "decode/x/farkas_empty_ok",
            "control: empty vector accepted",
            r#"{"coefficients":[]}"#,
        ),
        // ---- ARITY / TYPE ----
        (
            "decode/x/farkas_pair_short",
            "pair with one element",
            r#"{"coefficients":[[1]]}"#,
        ),
        (
            "decode/x/farkas_pair_long",
            "pair with three elements",
            r#"{"coefficients":[[1,2,3]]}"#,
        ),
        (
            "decode/x/farkas_pair_not_seq",
            "coefficient is a bare integer",
            r#"{"coefficients":[1]}"#,
        ),
        (
            "decode/x/farkas_float_numer",
            "float numerator",
            r#"{"coefficients":[[1.5,2]]}"#,
        ),
        (
            "decode/x/farkas_denom_overflows_i64",
            "denominator above i64::MAX",
            r#"{"coefficients":[[1,9223372036854775808]]}"#,
        ),
        // ---- ERROR ORDER ----
        (
            "decode/x/farkas_order_overflow_and_zero_denom",
            "ORDER: numerator overflow AND zero denominator",
            r#"{"coefficients":[[9223372036854775808,0]]}"#,
        ),
        (
            "decode/x/farkas_order_second_pair_bad",
            "ORDER: first pair fine, second has a zero denominator",
            r#"{"coefficients":[[1,2],[3,0]]}"#,
        ),
        (
            "decode/x/farkas_order_zero_denom_then_overflow",
            "ORDER: zero denominator in pair 1, overflow in pair 2",
            r#"{"coefficients":[[1,0],[9223372036854775808,1]]}"#,
        ),
        // ---- EXTREMES ----
        (
            "decode/x/farkas_denom_i64_min",
            "denominator i64::MIN",
            r#"{"coefficients":[[1,-9223372036854775808]]}"#,
        ),
        (
            "decode/x/farkas_zero_over_zero",
            "0/0",
            r#"{"coefficients":[[0,0]]}"#,
        ),
    ]
}

fn build_decode() -> Vec<DecodeCase> {
    let mut out = Vec::new();
    for (name, note, json) in decode_constants() {
        out.push(DecodeCase {
            name: name.to_string(),
            ty: "Constant".to_string(),
            note: note.to_string(),
            json: json.to_string(),
            outcome: probe::<Constant, _>(json, constant_raw),
        });
    }
    for (name, note, json) in decode_farkas() {
        out.push(DecodeCase {
            name: name.to_string(),
            ty: "FarkasAnnotation".to_string(),
            note: note.to_string(),
            json: json.to_string(),
            outcome: probe::<FarkasAnnotation, _>(json, farkas_raw),
        });
    }
    out
}

// -------------------------------------------------------------------- gate

/// Captured by running THIS FILE against the incumbent — i.e. on a tree where
/// `num-bigint/serde` and `num-rational/serde` were still enabled and no local
/// codec existed. That was the only moment the real behaviour could be
/// OBSERVED rather than invented.
const PARITY: &str = include_str!("fixtures/serde_bignum_parity.json");

fn build_report() -> Report {
    Report {
        schema: "ay.serde_bignum_parity.v1".to_string(),
        encode: build_encode(),
        decode: build_decode(),
    }
}

/// Rewrite `tests/fixtures/serde_bignum_parity.json` from the live codec.
///
/// Regeneration is ONLY meaningful against the incumbent, which no longer
/// exists on this branch. Regenerating here would record whatever the current
/// codec happens to do and call it parity — the exact failure this file
/// exists to prevent. It stays for the case of adding cases while temporarily
/// re-enabling the upstream features to re-observe them.
///
/// Compiled only under the `regen-serde-fixtures` feature — no environment
/// read, no `#[ignore]`: without the feature it does not exist, with it it
/// runs. `cargo test -p ay-core --features regen-serde-fixtures --test
/// serde_bignum_parity regenerate_parity_fixture -- --nocapture`.
#[cfg(feature = "regen-serde-fixtures")]
#[test]
fn regenerate_parity_fixture() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/serde_bignum_parity.json");
    let text = serde_json::to_string_pretty(&build_report()).expect("render");
    std::fs::write(&path, format!("{text}\n")).expect("write");
    eprintln!("REGENERATED {}", path.display());
}

/// THE GATE: the local codec must be indistinguishable from the incumbent on
/// every recorded case — encoded bytes, decoded values, ACCEPT/REJECT
/// decisions, and the full rejection message including its position suffix.
#[test]
fn parity_with_incumbent_is_exact() {
    let golden: Report = serde_json::from_str(PARITY).expect("parity fixture parses");
    let live = build_report();

    assert_eq!(
        golden.encode.iter().map(|c| &c.name).collect::<Vec<_>>(),
        live.encode.iter().map(|c| &c.name).collect::<Vec<_>>(),
        "encode case set drifted"
    );
    assert_eq!(
        golden.decode.iter().map(|c| &c.name).collect::<Vec<_>>(),
        live.decode.iter().map(|c| &c.name).collect::<Vec<_>>(),
        "decode case set drifted"
    );

    for (g, l) in golden.encode.iter().zip(live.encode.iter()) {
        assert_eq!(
            g.json, l.json,
            "ENCODING DRIFT for {}: proof evidence written by the incumbent would be \
             unreadable or silently reinterpreted.\n  incumbent:   {}\n  replacement: {}",
            g.name, g.json, l.json
        );
        assert_eq!(
            g.raw, l.raw,
            "STRUCTURAL DRIFT for {} (Ratio's PartialEq compares by VALUE, so only the \
             raw numer/denom pair catches a codec that reduces)",
            g.name
        );
        assert_eq!(
            g.decoded_raw, l.decoded_raw,
            "ROUND-TRIP VALUE DRIFT for {}",
            g.name
        );
        assert_eq!(
            g.reencoded, l.reencoded,
            "RE-ENCODE DRIFT for {}: decode-then-encode is no longer byte-identity",
            g.name
        );
    }

    for (g, l) in golden.decode.iter().zip(live.decode.iter()) {
        match (&g.outcome, &l.outcome) {
            (
                Outcome::Accept {
                    raw: gr,
                    reencoded: gre,
                },
                Outcome::Accept {
                    raw: lr,
                    reencoded: lre,
                },
            ) => {
                assert_eq!(gr, lr, "decoded value drifted for {}: {}", g.name, g.note);
                assert_eq!(gre, lre, "re-encoding drifted for {}: {}", g.name, g.note);
            }
            (Outcome::Reject { message: gm, .. }, Outcome::Reject { message: lm, .. }) => {
                assert_eq!(
                    gm, lm,
                    "REJECTION MESSAGE DRIFT for {}: both reject, but they say different \
                     things. A message names WHICH fault was found and WHERE, so a drift \
                     here means an operator diagnosing a corrupt artifact is sent \
                     somewhere else.\n  incumbent:   {gm}\n  replacement: {lm}\n  note: {}",
                    g.name, g.note
                );
            }
            (Outcome::Accept { .. }, Outcome::Reject { message, .. }) => panic!(
                "REGRESSION for {}: the incumbent ACCEPTED these bytes, the current codec \
                 REJECTS them with {message:?}. Stored evidence just became unreadable.\
                 \n  note: {}",
                g.name, g.note
            ),
            (Outcome::Reject { .. }, Outcome::Accept { raw, .. }) => panic!(
                "SOUNDNESS REGRESSION for {}: the incumbent REJECTED these bytes, the \
                 current codec ACCEPTS them as {raw}. A malformed artifact is now \
                 readable.\n  note: {}",
                g.name, g.note
            ),
            (_, Outcome::Panic { message }) => panic!(
                "PANIC for {}: the codec panicked with {message:?} where the incumbent did \
                 not. A malformed artifact must be an Err, never an abort.\n  note: {}",
                g.name, g.note
            ),
            (Outcome::Panic { message }, _) => panic!(
                "the INCUMBENT panicked for {} with {message:?} — the fixture recorded a \
                 panic, so this case cannot be used as a parity target.\n  note: {}",
                g.name, g.note
            ),
        }
    }
}
