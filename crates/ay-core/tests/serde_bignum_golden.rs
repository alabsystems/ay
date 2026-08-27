// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GOLDEN serde fixtures for the three bignum-bearing proof-artifact types.
//!
//! # Why this file exists
//!
//! `Constant`, `RationalWrapper` and `FarkasAnnotation` are PROOF ARTIFACTS:
//! they are written to disk and read back. Their `Serialize`/`Deserialize`
//! impls are currently supplied by `num-bigint`'s and `num-rational`'s
//! `serde` features. Those features are being dropped (they are the sole
//! reason `num-bigint`/`num-rational` are third-party serde blockers), and
//! the impls will be replaced by a local `#[serde(with = ...)]` codec.
//!
//! If the replacement codec encodes even one case differently, previously
//! written evidence becomes unreadable or — far worse — silently
//! reinterpreted. This file pins the INCUMBENT encoding byte-for-byte so
//! that drift is a test failure rather than a format change.
//!
//! The fixture was generated while `num-bigint/serde` and
//! `num-rational/serde` were still enabled. That was the only moment the
//! real format could be OBSERVED; every later "expected" value would be
//! something a human invented.
//!
//! # Regenerating
//!
//! Do not regenerate to make a red test green — a diff here means the
//! encoding changed, which is the thing this test exists to catch. The
//! escape hatch exists only for deliberately adding new cases:
//!
//! ```text
//! cargo test -p ay-core --features regen-serde-fixtures \
//!     --test serde_bignum_golden regenerate_golden_fixture -- --nocapture
//! ```
//!
//! The regenerator is a compile-time `#[cfg(feature = ...)]` target, not an
//! environment read and not an `#[ignore]`d test: without the feature it does
//! not exist, with it it runs. The gate tests below are unconditional either
//! way, so the feature only ever ADDS the regenerator.
//!
//! # What the incumbent format is (observed, not assumed)
//!
//! * `BigInt`  -> 2-tuple `[sign, limbs]`. `sign` is an `i8`: `-1` / `0` /
//!   `1` for Minus / NoSign / Plus. `limbs` is a sequence of **base-2^32**
//!   digits, least significant first.
//! * On a 64-bit target `BigUint` stores 64-bit limbs and splits each into
//!   `(lo, hi)` on the way out — **but the final limb's high word is
//!   omitted when it is zero**. That trailing-word suppression is the
//!   single likeliest place for a hand-written codec to diverge.
//! * `Ratio<T>` -> 2-tuple `[numer, denom]`, and **neither direction
//!   normalizes**. `Deserialize` uses `Ratio::new_raw`, so `[2,4]` decodes
//!   to a ratio whose numerator really is `2`. A codec that reduces on
//!   decode changes stored evidence.
//! * `RationalWrapper` is a newtype struct and is therefore TRANSPARENT in
//!   JSON: it encodes exactly as the inner `Ratio`.
//! * `Constant` is an externally tagged enum (`{"Int": ...}`), and its
//!   `BitVec` arm is a struct variant (`{"BitVec":{"value":...,"width":...}}`).
//!
//! `raw` fields below record numerator/denominator SEPARATELY on purpose:
//! `Ratio`'s `PartialEq` compares by VALUE (`self.cmp(other) == Equal`), so
//! `2/4 == 1/2` is true and a round-trip equality assertion is blind to a
//! normalizing codec. Only the raw pair catches it.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use ay_core::{Constant, FarkasAnnotation, RationalWrapper};
use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use serde::{Deserialize, Serialize};
use std::str::FromStr;

const GOLDEN: &str = include_str!("fixtures/serde_bignum_golden.json");

// ---------------------------------------------------------------- fixture

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct EncodeCase {
    /// Stable identifier; also the key the codec's own tests should quote.
    name: String,
    /// Which of the three load-bearing definitions carries this case.
    ty: String,
    /// Why the case is in the set.
    note: String,
    /// The exact bytes `serde_json::to_string` produced. THE GATE.
    json: String,
    /// Structural rendering of the value: for ratios this is the
    /// unreduced `numer/denom` pair, which value-based `PartialEq` hides.
    raw: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum DecodeOutcome {
    /// The incumbent decoder accepted these bytes.
    Accept {
        /// Structural rendering of what it produced.
        raw: String,
        /// Re-encoding the decoded value. When this differs from the input
        /// the input was NON-CANONICAL and the decoder normalized it.
        reencoded: String,
    },
    /// The incumbent decoder rejected these bytes.
    Reject {
        /// Substring the error message must contain. Not the whole message:
        /// serde_json owns the position suffix and may reword it.
        message_contains: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct DecodeCase {
    name: String,
    ty: String,
    note: String,
    json: String,
    outcome: DecodeOutcome,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct Golden {
    schema: String,
    generated_by: String,
    /// The exact producers of the incumbent encoding.
    num_bigint: String,
    num_rational: String,
    serde_format: String,
    host: String,
    encode: Vec<EncodeCase>,
    decode: Vec<DecodeCase>,
}

// ------------------------------------------------------- structural render

fn bigint_raw(v: &BigInt) -> String {
    v.to_string()
}

fn ratio_raw_big(v: &BigRational) -> String {
    format!("numer={} denom={}", v.numer(), v.denom())
}

fn ratio_raw_i64(v: &Rational64) -> String {
    format!("numer={} denom={}", v.numer(), v.denom())
}

fn constant_raw(c: &Constant) -> String {
    match c {
        Constant::Bool(b) => format!("Bool({b})"),
        Constant::Int(i) => format!("Int({})", bigint_raw(i)),
        Constant::Rational(r) => format!("Rational({})", ratio_raw_big(&r.0)),
        Constant::BitVec { value, width } => {
            format!("BitVec(value={} width={width})", bigint_raw(value))
        }
        Constant::String(s) => format!("String({s:?})"),
        // `Constant` is `#[non_exhaustive]`; a future arm must be added above.
        other => panic!("unhandled Constant arm in fixture renderer: {other:?}"),
    }
}

fn farkas_raw(f: &FarkasAnnotation) -> String {
    let parts: Vec<String> = f.coefficients.iter().map(ratio_raw_i64).collect();
    format!("coefficients=[{}]", parts.join(", "))
}

// ------------------------------------------------------------- case values

fn bi(s: &str) -> BigInt {
    BigInt::from_str(s).expect("decimal literal parses")
}

/// `BigInt` cases, carried through `Constant::Int` because that is the path
/// production actually serializes them on.
fn bigint_cases() -> Vec<(&'static str, &'static str, BigInt)> {
    vec![
        (
            "bigint/zero",
            "sign NoSign (0) and an EMPTY limb vector",
            bi("0"),
        ),
        ("bigint/one", "smallest positive; limb vector [1]", bi("1")),
        (
            "bigint/neg_one",
            "SIGN CARRIER: differs from bigint/one only in the sign field",
            bi("-1"),
        ),
        (
            "bigint/u32_max",
            "exactly fills one base-2^32 limb; the 64-bit hi word is zero and is OMITTED",
            bi("4294967295"),
        ),
        (
            "bigint/two_pow_32",
            "first value needing a second base-2^32 limb: [0, 1]",
            bi("4294967296"),
        ),
        (
            "bigint/two_pow_64_minus_1",
            "LIMB STRADDLE (2^64 - 1): both u32 words of the sole 64-bit limb are nonzero",
            bi("18446744073709551615"),
        ),
        (
            "bigint/two_pow_64",
            "LIMB STRADDLE (2^64): a second 64-bit limb opens; hi word of it is zero and OMITTED",
            bi("18446744073709551616"),
        ),
        (
            "bigint/two_pow_64_plus_1",
            "LIMB STRADDLE (2^64 + 1)",
            bi("18446744073709551617"),
        ),
        (
            "bigint/neg_two_pow_64",
            "SIGN CARRIER at the limb boundary: -(2^64)",
            bi("-18446744073709551616"),
        ),
        (
            "bigint/i64_min",
            "SIGN CARRIER: -2^63, the value a two's-complement codec most often mishandles",
            bi("-9223372036854775808"),
        ),
        (
            "bigint/two_pow_128_plus_1",
            "INTERIOR ZERO limbs: a codec that trims zeros anywhere but the tail breaks here",
            bi("340282366920938463463374607431768211457"),
        ),
        (
            "bigint/large_positive",
            "multi-limb ordinary magnitude",
            bi("123456789012345678901234567890"),
        ),
        (
            "bigint/large_negative",
            "SIGN CARRIER: negation of bigint/large_positive; only the sign field differs",
            bi("-123456789012345678901234567890"),
        ),
    ]
}

/// `Ratio<BigInt>` cases, carried through `RationalWrapper`.
fn bigrational_cases() -> Vec<(&'static str, &'static str, BigRational)> {
    vec![
        (
            "bigrational/zero",
            "0/1 — denominator is 1, NOT 0, and the numerator's sign is NoSign",
            BigRational::new(bi("0"), bi("1")),
        ),
        ("bigrational/one", "1/1", BigRational::new(bi("1"), bi("1"))),
        (
            "bigrational/neg_numer",
            "SIGN CARRIER: -3/4, sign rides the NUMERATOR",
            BigRational::new(bi("-3"), bi("4")),
        ),
        (
            "bigrational/neg_denom_normalized",
            "constructed 3/-4 via Ratio::new, which REDUCES and moves the sign to the numerator",
            BigRational::new(bi("3"), bi("-4")),
        ),
        (
            "bigrational/neg_denom_raw",
            "DENORMALIZED via Ratio::new_raw: the denominator really is negative on the wire",
            BigRational::new_raw(bi("3"), bi("-4")),
        ),
        (
            "bigrational/unreduced_raw",
            "UNREDUCED via Ratio::new_raw: 2/4 is stored as 2/4, not 1/2",
            BigRational::new_raw(bi("2"), bi("4")),
        ),
        (
            "bigrational/multilimb",
            "both members straddle the limb boundary",
            BigRational::new_raw(bi("18446744073709551617"), bi("-36893488147419103232")),
        ),
    ]
}

/// `Ratio<i64>` cases, carried through `FarkasAnnotation`.
///
/// THIS IS THE TYPE EVERY EARLIER SCAN MISSED: `Rational64 = Ratio<i64>`
/// contains no `BigInt` and not even the substring "Big", so a scan for
/// bignum-typed members is structurally blind to it. It needs its OWN
/// codec — the `BigInt` one does not apply.
fn rational64_cases() -> Vec<(&'static str, &'static str, Vec<Rational64>)> {
    vec![
        (
            "farkas/empty",
            "empty coefficient vector — the degenerate annotation",
            vec![],
        ),
        ("farkas/zero", "0/1", vec![Rational64::new(0, 1)]),
        ("farkas/one", "1/1", vec![Rational64::new(1, 1)]),
        (
            "farkas/neg_numer",
            "SIGN CARRIER: -3/4",
            vec![Rational64::new(-3, 4)],
        ),
        (
            "farkas/neg_denom_normalized",
            "3/-4 via Ratio::new — REDUCES, sign moves to the numerator",
            vec![Rational64::new(3, -4)],
        ),
        (
            "farkas/neg_denom_raw",
            "DENORMALIZED via Ratio::new_raw: negative denominator survives to the wire",
            vec![Rational64::new_raw(3, -4)],
        ),
        (
            "farkas/unreduced_raw",
            "UNREDUCED via Ratio::new_raw: 2/4 stays 2/4",
            vec![Rational64::new_raw(2, 4)],
        ),
        (
            "farkas/i64_extremes",
            "SIGN CARRIER: i64::MIN numerator and i64::MAX denominator, unreduced",
            vec![Rational64::new_raw(i64::MIN, i64::MAX)],
        ),
        (
            "farkas/realistic_vector",
            "a plausible Farkas certificate: several coefficients, mixed signs",
            vec![
                Rational64::new(1, 1),
                Rational64::new(-3, 4),
                Rational64::new(0, 1),
                Rational64::new_raw(7, 2),
            ],
        ),
    ]
}

/// Whole-struct `Constant` cases, pinning the ENUM TAGGING.
fn constant_cases() -> Vec<(&'static str, &'static str, Constant)> {
    vec![
        (
            "constant/bool_true",
            "externally tagged newtype variant",
            Constant::Bool(true),
        ),
        (
            "constant/string",
            "externally tagged newtype variant carrying a String",
            Constant::String("hello \"world\"".to_string()),
        ),
        (
            "constant/int_neg",
            "SIGN CARRIER inside the enum tag",
            Constant::Int(bi("-18446744073709551617")),
        ),
        (
            "constant/rational_neg_denom_raw",
            "RationalWrapper is a newtype struct and is TRANSPARENT: no extra nesting",
            Constant::Rational(RationalWrapper(BigRational::new_raw(bi("3"), bi("-4")))),
        ),
        (
            "constant/bitvec_zero_width8",
            "STRUCT VARIANT: named fields `value` and `width`, in declaration order",
            Constant::BitVec {
                value: bi("0"),
                width: 8,
            },
        ),
        (
            "constant/bitvec_straddle_width65",
            "STRUCT VARIANT at the limb boundary",
            Constant::BitVec {
                value: bi("18446744073709551617"),
                width: 65,
            },
        ),
    ]
}

// -------------------------------------------------------- decoder behaviour

/// Non-canonical and invalid inputs. A hand-written codec must reproduce
/// these ACCEPT/REJECT decisions, not just the happy path.
fn decode_probe_constants() -> Vec<(&'static str, &'static str, &'static str)> {
    vec![
        (
            "decode/bigint/nosign_with_limbs",
            "NON-CANONICAL: sign 0 with a nonempty limb vector. from_biguint CLEARS the limbs.",
            r#"{"Int":[0,[1,2]]}"#,
        ),
        (
            "decode/bigint/plus_with_empty_limbs",
            "NON-CANONICAL: sign 1 with no limbs. from_biguint DEMOTES the sign to 0.",
            r#"{"Int":[1,[]]}"#,
        ),
        (
            "decode/bigint/trailing_zero_limb",
            "NON-CANONICAL: a trailing zero limb is trimmed, so re-encoding differs from input.",
            r#"{"Int":[-1,[3,0]]}"#,
        ),
        (
            "decode/bigint/bad_sign",
            "INVALID: sign outside {-1,0,1} must be REJECTED, not clamped.",
            r#"{"Int":[2,[1]]}"#,
        ),
        (
            "decode/bigint/limb_overflows_u32",
            "INVALID: limbs are u32; a value above u32::MAX must be REJECTED.",
            r#"{"Int":[1,[4294967296]]}"#,
        ),
        (
            "decode/bigint/negative_limb",
            "INVALID: limbs are unsigned.",
            r#"{"Int":[1,[-1]]}"#,
        ),
        (
            "decode/rational/unreduced_preserved",
            "The decoder uses Ratio::new_raw and does NOT reduce: 2/4 stays 2/4.",
            r#"{"Rational":[[1,[2]],[1,[4]]]}"#,
        ),
        (
            "decode/rational/zero_denominator",
            "INVALID: a zero denominator must be REJECTED.",
            r#"{"Rational":[[1,[1]],[0,[]]]}"#,
        ),
        (
            "decode/bitvec/unknown_field",
            "deny_unknown_fields is on the struct variant: an extra key must be REJECTED.",
            r#"{"BitVec":{"value":[0,[]],"width":8,"extra":1}}"#,
        ),
    ]
}

fn decode_probe_farkas() -> Vec<(&'static str, &'static str, &'static str)> {
    vec![
        (
            "decode/farkas/unreduced_preserved",
            "Ratio<i64> decode does NOT reduce either: 2/4 stays 2/4.",
            r#"{"coefficients":[[2,4]]}"#,
        ),
        (
            "decode/farkas/neg_denom_preserved",
            "A negative denominator survives decode unchanged; no sign migration.",
            r#"{"coefficients":[[3,-4]]}"#,
        ),
        (
            "decode/farkas/zero_denominator",
            "INVALID: zero denominator must be REJECTED.",
            r#"{"coefficients":[[1,0]]}"#,
        ),
        (
            "decode/farkas/unknown_field",
            "deny_unknown_fields on FarkasAnnotation: an extra key must be REJECTED.",
            r#"{"coefficients":[[1,1]],"extra":2}"#,
        ),
        (
            "decode/farkas/numer_overflows_i64",
            "INVALID: coefficients are i64.",
            r#"{"coefficients":[[9223372036854775808,1]]}"#,
        ),
    ]
}

// ----------------------------------------------------------------- builders

fn build_encode_cases() -> Vec<EncodeCase> {
    let mut out = Vec::new();

    for (name, note, value) in bigint_cases() {
        let c = Constant::Int(value);
        out.push(EncodeCase {
            name: name.to_string(),
            ty: "Constant::Int(BigInt)".to_string(),
            note: note.to_string(),
            json: serde_json::to_string(&c).expect("encode Constant::Int"),
            raw: constant_raw(&c),
        });
    }

    for (name, note, value) in bigrational_cases() {
        let w = RationalWrapper(value);
        out.push(EncodeCase {
            name: name.to_string(),
            ty: "RationalWrapper(BigRational)".to_string(),
            note: note.to_string(),
            json: serde_json::to_string(&w).expect("encode RationalWrapper"),
            raw: format!("RationalWrapper({})", ratio_raw_big(&w.0)),
        });
    }

    for (name, note, coefficients) in rational64_cases() {
        let f = FarkasAnnotation::new(coefficients);
        out.push(EncodeCase {
            name: name.to_string(),
            ty: "FarkasAnnotation{Vec<Rational64>}".to_string(),
            note: note.to_string(),
            json: serde_json::to_string(&f).expect("encode FarkasAnnotation"),
            raw: farkas_raw(&f),
        });
    }

    for (name, note, value) in constant_cases() {
        out.push(EncodeCase {
            name: name.to_string(),
            ty: "Constant".to_string(),
            note: note.to_string(),
            json: serde_json::to_string(&value).expect("encode Constant"),
            raw: constant_raw(&value),
        });
    }

    out
}

fn build_decode_cases() -> Vec<DecodeCase> {
    let mut out = Vec::new();

    for (name, note, json) in decode_probe_constants() {
        let outcome = match serde_json::from_str::<Constant>(json) {
            Ok(v) => DecodeOutcome::Accept {
                raw: constant_raw(&v),
                reencoded: serde_json::to_string(&v).expect("re-encode"),
            },
            Err(e) => DecodeOutcome::Reject {
                message_contains: trim_position(&e.to_string()),
            },
        };
        out.push(DecodeCase {
            name: name.to_string(),
            ty: "Constant".to_string(),
            note: note.to_string(),
            json: json.to_string(),
            outcome,
        });
    }

    for (name, note, json) in decode_probe_farkas() {
        let outcome = match serde_json::from_str::<FarkasAnnotation>(json) {
            Ok(v) => DecodeOutcome::Accept {
                raw: farkas_raw(&v),
                reencoded: serde_json::to_string(&v).expect("re-encode"),
            },
            Err(e) => DecodeOutcome::Reject {
                message_contains: trim_position(&e.to_string()),
            },
        };
        out.push(DecodeCase {
            name: name.to_string(),
            ty: "FarkasAnnotation".to_string(),
            note: note.to_string(),
            json: json.to_string(),
            outcome,
        });
    }

    out
}

/// Drop serde_json's ` at line N column M` suffix: the semantic half of the
/// message is what a replacement codec must reproduce, the position is not.
fn trim_position(message: &str) -> String {
    match message.find(" at line ") {
        Some(i) => message[..i].to_string(),
        None => message.to_string(),
    }
}

/// Only the regenerator builds a whole `Golden`; the gates compare the parsed
/// fixture against `build_encode_cases`/`build_decode_cases` directly.
#[cfg(feature = "regen-serde-fixtures")]
fn build_golden() -> Golden {
    Golden {
        schema: "ay.serde_bignum_golden.v1".to_string(),
        generated_by: "crates/ay-core/tests/serde_bignum_golden.rs".to_string(),
        num_bigint: "0.4.6 (feature \"serde\" ENABLED)".to_string(),
        num_rational: "0.4.2 (feature \"serde\" ENABLED)".to_string(),
        serde_format: "serde_json (the ONLY serde format in the ay workspace: no bincode, \
                       messagepack, cbor or postcard dependency or call site exists)"
            .to_string(),
        host: "aarch64-apple-darwin (64-bit BigDigit; see the cfg_digit note in the module docs)"
            .to_string(),
        encode: build_encode_cases(),
        decode: build_decode_cases(),
    }
}

// -------------------------------------------------------------------- tests

fn load_golden() -> Golden {
    serde_json::from_str(GOLDEN).expect("golden fixture parses")
}

/// Rewrite `tests/fixtures/serde_bignum_golden.json` from the live encoder;
/// see the module header for the command and for when this is legitimate.
/// Review the resulting diff: anything that is not a deliberately added case
/// is the encoding drift this file exists to report.
#[cfg(feature = "regen-serde-fixtures")]
#[test]
fn regenerate_golden_fixture() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/serde_bignum_golden.json");
    std::fs::create_dir_all(path.parent().unwrap()).expect("create fixtures dir");
    let text = serde_json::to_string_pretty(&build_golden()).expect("render golden");
    std::fs::write(&path, format!("{text}\n")).expect("write golden");
    eprintln!("REGENERATED {}", path.display());
}

/// THE GATE: every recorded encoding must still be produced byte-for-byte.
#[test]
fn encoding_matches_golden_byte_for_byte() {
    let golden = load_golden();
    let live = build_encode_cases();

    let names_golden: Vec<&str> = golden.encode.iter().map(|c| c.name.as_str()).collect();
    let names_live: Vec<&str> = live.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(
        names_golden, names_live,
        "case set drifted; add cases with the regen-serde-fixtures feature (see the module \
         header), never by editing the fixture"
    );

    for (g, l) in golden.encode.iter().zip(live.iter()) {
        assert_eq!(
            g.json, l.json,
            "ENCODING DRIFT for {}: previously-written proof evidence would be \
             unreadable or silently reinterpreted.\n  golden: {}\n  live:   {}\n  note: {}",
            g.name, g.json, l.json, g.note
        );
        assert_eq!(
            g.raw, l.raw,
            "STRUCTURAL DRIFT for {}: the value itself changed shape (note that Ratio's \
             PartialEq compares by VALUE, so only this raw numer/denom pair catches \
             a codec that reduces or migrates the sign).\n  note: {}",
            g.name, g.note
        );
    }
}

/// Decoding the golden bytes must reproduce the golden value, and
/// re-encoding must return to the same bytes.
#[test]
fn golden_bytes_round_trip() {
    let golden = load_golden();

    for case in &golden.encode {
        if case.ty.starts_with("Constant") {
            let v: Constant = serde_json::from_str(&case.json)
                .unwrap_or_else(|e| panic!("decode {}: {e}", case.name));
            assert_eq!(
                constant_raw(&v),
                case.raw,
                "decoded value for {}",
                case.name
            );
            assert_eq!(
                serde_json::to_string(&v).expect("re-encode"),
                case.json,
                "re-encode is not identity for {}",
                case.name
            );
        } else if case.ty.starts_with("RationalWrapper") {
            let v: RationalWrapper = serde_json::from_str(&case.json)
                .unwrap_or_else(|e| panic!("decode {}: {e}", case.name));
            assert_eq!(
                format!("RationalWrapper({})", ratio_raw_big(&v.0)),
                case.raw,
                "decoded value for {}",
                case.name
            );
            assert_eq!(
                serde_json::to_string(&v).expect("re-encode"),
                case.json,
                "re-encode is not identity for {}",
                case.name
            );
        } else {
            let v: FarkasAnnotation = serde_json::from_str(&case.json)
                .unwrap_or_else(|e| panic!("decode {}: {e}", case.name));
            assert_eq!(farkas_raw(&v), case.raw, "decoded value for {}", case.name);
            assert_eq!(
                serde_json::to_string(&v).expect("re-encode"),
                case.json,
                "re-encode is not identity for {}",
                case.name
            );
        }
    }
}

/// THE RECIPE, proven rather than assumed.
///
/// The `BigUint` encoder does not simply dump its limb vector. On a 64-bit
/// host it splits each 64-bit limb into `(lo, hi)` u32 words but OMITS the
/// final limb's high word when that word is zero. That conditional is the
/// single likeliest place for a hand-written codec to diverge, and getting
/// it wrong is invisible for small values and wrong for large ones.
///
/// This test establishes that the wire limb array is exactly
/// `magnitude().to_u32_digits()` for every case in the corpus. That matters
/// beyond convenience: `to_u32_digits()` is defined in base 2^32
/// independently of the host's `BigDigit` width, so a codec written against
/// it produces the SAME bytes on a 32-bit host, where num-bigint takes the
/// other `cfg_digit!` branch. The golden fixture is therefore not
/// aarch64-specific.
#[test]
fn wire_limbs_are_exactly_to_u32_digits() {
    for (name, _note, value) in bigint_cases() {
        let encoded = serde_json::to_string(&Constant::Int(value.clone())).expect("encode");
        let parsed: serde_json::Value = serde_json::from_str(&encoded).expect("reparse");
        let pair = parsed
            .get("Int")
            .expect("Int tag")
            .as_array()
            .expect("2-tuple");
        assert_eq!(
            pair.len(),
            2,
            "{name}: BigInt encodes as a 2-tuple [sign, limbs]"
        );

        let wire_limbs: Vec<u64> = pair[1]
            .as_array()
            .expect("limb array")
            .iter()
            .map(|d| d.as_u64().expect("limbs are unsigned"))
            .collect();
        let recipe: Vec<u64> = value
            .magnitude()
            .to_u32_digits()
            .into_iter()
            .map(u64::from)
            .collect();
        assert_eq!(
            wire_limbs, recipe,
            "{name}: the wire limb array must equal magnitude().to_u32_digits()"
        );

        // And the sign really is a bare i8 in {-1, 0, 1}, sign-magnitude —
        // NOT two's complement. `bigint/i64_min` is the case that proves it.
        let sign = pair[0].as_i64().expect("sign is an integer");
        assert!(
            (-1..=1).contains(&sign),
            "{name}: sign {sign} outside the documented -1/0/1 alphabet"
        );
        let expected_sign = match value.sign() {
            num_bigint::Sign::Minus => -1,
            num_bigint::Sign::NoSign => 0,
            num_bigint::Sign::Plus => 1,
        };
        assert_eq!(sign, expected_sign, "{name}: sign field");
    }
}

/// A replacement codec must reproduce the ACCEPT/REJECT decisions and the
/// normalization behaviour on non-canonical input, not just the happy path.
#[test]
fn decoder_behaviour_matches_golden() {
    let golden = load_golden();
    let live = build_decode_cases();

    let names_golden: Vec<&str> = golden.decode.iter().map(|c| c.name.as_str()).collect();
    let names_live: Vec<&str> = live.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(names_golden, names_live, "decode case set drifted");

    for (g, l) in golden.decode.iter().zip(live.iter()) {
        match (&g.outcome, &l.outcome) {
            (
                DecodeOutcome::Accept {
                    raw: gr,
                    reencoded: gre,
                },
                DecodeOutcome::Accept {
                    raw: lr,
                    reencoded: lre,
                },
            ) => {
                assert_eq!(gr, lr, "decoded value drifted for {}: {}", g.name, g.note);
                assert_eq!(gre, lre, "re-encoding drifted for {}: {}", g.name, g.note);
            }
            (DecodeOutcome::Reject { message_contains }, DecodeOutcome::Reject { .. }) => {
                // The decision is the gate; the exact wording belongs to
                // serde_json and to whatever the replacement codec says.
                assert!(
                    !message_contains.is_empty(),
                    "empty rejection message recorded for {}",
                    g.name
                );
            }
            (DecodeOutcome::Accept { .. }, DecodeOutcome::Reject { .. }) => panic!(
                "REGRESSION for {}: the incumbent ACCEPTED these bytes and the current \
                 codec REJECTS them. Stored evidence just became unreadable.\n  note: {}",
                g.name, g.note
            ),
            (DecodeOutcome::Reject { .. }, DecodeOutcome::Accept { raw, .. }) => panic!(
                "SOUNDNESS REGRESSION for {}: the incumbent REJECTED these bytes and the \
                 current codec ACCEPTS them as {raw}. A malformed artifact is now readable.\
                 \n  note: {}",
                g.name, g.note
            ),
        }
    }
}
