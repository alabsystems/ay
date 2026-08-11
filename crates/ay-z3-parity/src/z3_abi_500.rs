// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Isolated runtime probes for the exact Z3 5.0.0 C ABI.
//!
//! This module is deliberately reached through a hidden child-process mode.
//! Loading a shared object runs its initializers and calling an ABI with a
//! mismatched signature can abort the process, so the conformance checker must
//! never perform these operations in its receipt-verification process.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{c_char, c_void, CStr};
use std::io::Read as _;
use std::path::Path;
use std::sync::OnceLock;

use serde::{Deserialize, Serialize};

use crate::loader;

pub(crate) const REQUIRED_SYMBOL_COUNT: usize = 807;
pub(crate) const REQUIRED_SYMBOL_MANIFEST_SHA256: &str =
    "4259cfc87c0916a96ec5201a060edb286ce1553ac4e8e8cf0747aa310a88ecdb";
pub(crate) const Z3_500_FULL_VERSION: &str = "Z3 5.0.0.0";

/// Exact public C declarations exposed by the pinned Z3 5.0.0 `z3.h` include
/// graph. The canonical signature spelling is produced by Clang's C11 AST
/// after including the byte-authenticated header set below.
pub(crate) const PUBLIC_C_DECLARATION_COUNT: usize = 805;
#[cfg(test)]
pub(crate) const AUTHENTICATED_CALLABILITY_COUNT: usize = 217;
pub(crate) const PUBLIC_C_DECLARATION_MANIFEST_SHA256: &str =
    "d4447ff654fd3b6bc6102d8e4959c5f12fb3b0d643f85bd7c4262167130ba2a0";
pub(crate) const PUBLIC_C_HEADER_SET_SHA256: &str =
    "b95c4a5f861e96f9d1704ac148e176d8af9f8f36521dd9b3c88e563e2d11db9b";
pub(crate) const AY_COMPAT_WRAPPER_SHA256: &str =
    "a82e323425593f5ff8305488ab6c80271fd1c9920458b121f9be358430dbbdd8";
pub(crate) const TYPED_C_CALL_SITES_SHA256: &str =
    "3c2dcccda91d56a86ae41e6ba96c77a51d017db0369390943cfe8a6c57e08c41";
pub(crate) const ADDITIONAL_STOCK_C_PROBE_SHA256: &str =
    "8b9ae909dc633a25c3e27f5e960e3e4219f1abb948d8ca2aeca13eaaf277e046";
pub(crate) const REMAINING_STOCK_C_PROBE_SHA256: &str =
    "757f1838f48dc9f7272d26fc885d26ba068d43da9d9b696b30a79b6f40ae6415";
pub(crate) const UNPROBED_REASON_COUNT: usize = 588;
pub(crate) const UNPROBED_REASON_MANIFEST_SHA256: &str =
    "79b27a812ed9ee96cd0ab63304d785ad5deac9c7c2339ce58599aa15fc8ca1cb";

const PUBLIC_C_DECLARATION_MANIFEST: &str = include_str!("../data/z3-5.0.0-c-declarations.txt");
const AY_COMPAT_WRAPPER: &[u8] = include_bytes!("../../ay-ffi/include/ay_z3_compat.h");
const TYPED_C_CALL_SITES: &[u8] = include_bytes!("../../ay-ffi/tests/z3_500_typed_surface.c");
const ADDITIONAL_STOCK_C_PROBE: &[u8] =
    include_bytes!("../../ay-ffi/tests/capi_z3_500_additional_consumer.c");
const REMAINING_STOCK_C_PROBE: &[u8] =
    include_bytes!("../../ay-ffi/tests/capi_z3_500_remaining_consumer.c");
const UNPROBED_REASON_MANIFEST: &str = include_str!("../data/z3-5.0.0-c-unprobed-reasons.tsv");

struct PublicHeader {
    path: &'static str,
    bytes: &'static [u8],
    size: usize,
    sha256: &'static str,
}

pub(crate) struct StockCProbe {
    pub(crate) id: &'static str,
    pub(crate) source: &'static [u8],
    pub(crate) expected_stdout_trailer: &'static [u8],
}

/// The complete `z3.h` include graph from Z3 commit
/// `8e3402b215a810a4154eb183a7dfc4e853eb2f52`. Byte identity closes all public
/// type, enum, callback, macro, and function-declaration spelling, not only
/// exported names.
const PUBLIC_HEADERS: [PublicHeader; 11] = [
    PublicHeader {
        path: "z3.h",
        bytes: include_bytes!("../../ay-ffi/include/z3.h"),
        size: 495,
        sha256: "60cc2bb3e1df2c0fc6105b6a73c032b9d4f47487471616994ba63df8d81898a8",
    },
    PublicHeader {
        path: "z3_macros.h",
        bytes: include_bytes!("../../ay-ffi/include/z3_macros.h"),
        size: 389,
        sha256: "9d92f8136abef10dd8429a28fd9068e9b3e4feb5696072763cd8d0edc1f00b24",
    },
    PublicHeader {
        path: "z3_api.h",
        bytes: include_bytes!("../../ay-ffi/include/z3_api.h"),
        size: 277_924,
        sha256: "2f293263651f980f1810152e37d689f895e9711b266a7bd5f5db0f700cb48dda",
    },
    PublicHeader {
        path: "z3_ast_containers.h",
        bytes: include_bytes!("../../ay-ffi/include/z3_ast_containers.h"),
        size: 5_735,
        sha256: "6687f3ec9483f3774b8951be0f9944ab47f61bedbd42193d075dd88c612fb248",
    },
    PublicHeader {
        path: "z3_algebraic.h",
        bytes: include_bytes!("../../ay-ffi/include/z3_algebraic.h"),
        size: 7_193,
        sha256: "7659d6dec25e49e2dd6546a6ca6c05adb27437a989d857af0cbcc7191adb45a6",
    },
    PublicHeader {
        path: "z3_polynomial.h",
        bytes: include_bytes!("../../ay-ffi/include/z3_polynomial.h"),
        size: 1_056,
        sha256: "e1894c40edb37115cf221a8ef2f7e5557c7360c3c0583f05582f849ebdd78c36",
    },
    PublicHeader {
        path: "z3_rcf.h",
        bytes: include_bytes!("../../ay-ffi/include/z3_rcf.h"),
        size: 9_960,
        sha256: "0cf1d77e67e49df12dd20aac8bf3bf3f46973ebf828ca8f7d14228d6d2cb86ca",
    },
    PublicHeader {
        path: "z3_fixedpoint.h",
        bytes: include_bytes!("../../ay-ffi/include/z3_fixedpoint.h"),
        size: 14_123,
        sha256: "cc8a424163dd6a92a1bfe07dea68edb8fc8dabb58f612b1e85a033a21178dedc",
    },
    PublicHeader {
        path: "z3_optimization.h",
        bytes: include_bytes!("../../ay-ffi/include/z3_optimization.h"),
        size: 13_798,
        sha256: "3f7dac1bd1696bfff5266f422171e10fae413db7b065549e17934d9212acbcc7",
    },
    PublicHeader {
        path: "z3_fpa.h",
        bytes: include_bytes!("../../ay-ffi/include/z3_fpa.h"),
        size: 43_932,
        sha256: "5ebe1a61d128c579f53be2f1f2b4d45e76b7e04081de89a11542719c5976396c",
    },
    PublicHeader {
        path: "z3_spacer.h",
        bytes: include_bytes!("../../ay-ffi/include/z3_spacer.h"),
        size: 4_459,
        sha256: "dd23be86e4fc74cd0adf6ca944834d165b93f6a6f3af81923116db97a7ee1ddd",
    },
];

const MAX_REQUIRED_SYMBOL_INPUT: u64 = 256 * 1024;
const REQUIRED_SYMBOL_MANIFEST: &str = include_str!("../data/z3-5.0.0-symbols.txt");

/// Z3 5.0.0 declaration-kind values added for finite sets.
///
/// `EXT` and `MAP_INVERSE` are internal operators without public C
/// constructors. Their reserved values are nevertheless part of the public
/// `Z3_decl_kind` ABI consumed by stock bindings.
pub(crate) const FINITE_SET_DECL_KINDS: [(&str, u32); 13] = [
    ("finite-set-empty", 0xc000),
    ("finite-set-singleton", 0xc001),
    ("finite-set-union", 0xc002),
    ("finite-set-intersect", 0xc003),
    ("finite-set-difference", 0xc004),
    ("finite-set-in", 0xc005),
    ("finite-set-size", 0xc006),
    ("finite-set-subset", 0xc007),
    ("finite-set-map", 0xc008),
    ("finite-set-filter", 0xc009),
    ("finite-set-range", 0xc00a),
    ("finite-set-ext", 0xc00b),
    ("finite-set-map-inverse", 0xc00c),
];

const SORT_PROBES: [(&str, &str); 9] = [
    ("finite-sort-is-finite", "true"),
    ("int-sort-is-not-finite", "true"),
    ("finite-sort-basis-is-int", "true"),
    ("finite-sort-kind", "1000"),
    ("finite-sort-name", "FiniteSet"),
    ("finite-sort-text", "(FiniteSet Int)"),
    ("finite-sort-differs-from-legacy-array-set", "true"),
    ("nested-finite-sort-text", "(FiniteSet (FiniteSet Int))"),
    ("nested-finite-sort-basis-round-trip", "true"),
];

#[derive(Clone, Copy)]
struct AstExpectation {
    id: &'static str,
    decl_name: &'static str,
    arity: u32,
    canonical_text: &'static str,
}

const AST_EXPECTATIONS: [AstExpectation; 11] = [
    AstExpectation {
        id: "empty",
        decl_name: "set.empty",
        arity: 0,
        canonical_text: "(as set.empty (FiniteSet Int))",
    },
    AstExpectation {
        id: "singleton",
        decl_name: "set.singleton",
        arity: 1,
        canonical_text: "(set.singleton 1)",
    },
    AstExpectation {
        id: "union",
        decl_name: "set.union",
        arity: 2,
        canonical_text: "(set.union (set.singleton 1) (set.singleton 2))",
    },
    AstExpectation {
        id: "intersect",
        decl_name: "set.intersect",
        arity: 2,
        canonical_text:
            "(set.intersect (set.union (set.singleton 1) (set.singleton 2)) (set.singleton 1))",
    },
    AstExpectation {
        id: "difference",
        decl_name: "set.difference",
        arity: 2,
        canonical_text:
            "(set.difference (set.union (set.singleton 1) (set.singleton 2)) (set.singleton 1))",
    },
    AstExpectation {
        id: "in",
        decl_name: "set.in",
        arity: 2,
        canonical_text: "(set.in 1 (as set.empty (FiniteSet Int)))",
    },
    AstExpectation {
        id: "size",
        decl_name: "set.size",
        arity: 1,
        canonical_text: "(set.size (as set.empty (FiniteSet Int)))",
    },
    AstExpectation {
        id: "subset",
        decl_name: "set.subset",
        arity: 2,
        canonical_text:
            "(set.subset (set.singleton 1) (set.union (set.singleton 1) (set.singleton 2)))",
    },
    AstExpectation {
        id: "map",
        decl_name: "set.map",
        arity: 2,
        canonical_text: "(set.map (lambda ((x Int)) (+ x 1)) (set.singleton 1))",
    },
    AstExpectation {
        id: "filter",
        decl_name: "set.filter",
        arity: 2,
        canonical_text:
            "(set.filter (lambda ((x Int)) (not (= 1 x))) (set.union (set.singleton 1) (set.singleton 2)))",
    },
    AstExpectation {
        id: "range",
        decl_name: "set.range",
        arity: 2,
        canonical_text: "(set.range 1 3)",
    },
];

const SEMANTIC_PROBES: [(&str, &str); 19] = [
    ("empty-size-zero", "proved"),
    ("empty-excludes-one", "proved"),
    ("singleton-includes-one", "proved"),
    ("singleton-excludes-two", "proved"),
    ("singleton-size-one", "proved"),
    ("union-includes-one", "proved"),
    ("union-includes-two", "proved"),
    ("intersect-is-singleton-one", "proved"),
    ("difference-is-singleton-two", "proved"),
    ("singleton-subset-union", "proved"),
    ("singleton-not-subset-empty", "proved"),
    ("range-produces-finite-int-set", "true"),
    ("range-includes-high", "proved"),
    ("range-excludes-successor", "proved"),
    ("range-size-three", "proved"),
    ("map-produces-finite-int-set", "true"),
    ("filter-produces-finite-int-set", "true"),
    ("filter-retains-two", "proved"),
    ("filter-removes-one", "proved"),
];

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct LibraryObservation {
    pub(crate) exported_z3_symbols: Vec<String>,
    pub(crate) required_resolvable_symbols: Vec<String>,
    pub(crate) full_version: Option<String>,
    pub(crate) ay_build_stamp: Option<String>,
    pub(crate) probes: BTreeMap<String, String>,
}

pub(crate) fn expected_probe_values() -> BTreeMap<String, String> {
    let mut expected = BTreeMap::new();
    for (name, value) in SORT_PROBES {
        expected.insert(name.to_string(), value.to_string());
    }
    for (name, value) in FINITE_SET_DECL_KINDS {
        expected.insert(format!("decl-kind.{name}"), value.to_string());
    }
    for ast in AST_EXPECTATIONS {
        expected.insert(
            format!("ast.{}.decl-name", ast.id),
            ast.decl_name.to_string(),
        );
        expected.insert(format!("ast.{}.arity", ast.id), ast.arity.to_string());
        expected.insert(
            format!("ast.{}.app-arg-count", ast.id),
            ast.arity.to_string(),
        );
        expected.insert(format!("ast.{}.args-match", ast.id), "true".to_string());
        expected.insert(
            format!("ast.{}.canonical-text", ast.id),
            ast.canonical_text.to_string(),
        );
    }
    expected.insert(
        "ast.empty.decl-parameter-count".to_string(),
        "1".to_string(),
    );
    expected.insert(
        "ast.empty.decl-parameter-kind-0".to_string(),
        "4".to_string(),
    );
    expected.insert(
        "ast.empty.decl-parameter-sort-0-is-result-sort".to_string(),
        "true".to_string(),
    );
    for (name, value) in SEMANTIC_PROBES {
        expected.insert(format!("semantics.{name}"), value.to_string());
    }
    expected
}

pub(crate) fn symbol_manifest_sha256(symbols: &[String]) -> String {
    let mut bytes = Vec::new();
    for symbol in symbols {
        bytes.extend_from_slice(symbol.as_bytes());
        bytes.push(b'\n');
    }
    crate::smtlib_conformance::sha256_bytes(&bytes)
}

/// Immutable expected observations for the public C include surface.
pub(crate) fn expected_c_surface_values() -> BTreeMap<String, String> {
    let mut expected = BTreeMap::new();
    expected.insert(
        "declarations".to_string(),
        format!("count={PUBLIC_C_DECLARATION_COUNT};sha256={PUBLIC_C_DECLARATION_MANIFEST_SHA256}"),
    );
    expected.insert(
        "header-set".to_string(),
        format!(
            "count={};sha256={PUBLIC_C_HEADER_SET_SHA256}",
            PUBLIC_HEADERS.len()
        ),
    );
    expected.insert(
        "header.ay_z3_compat.h".to_string(),
        format!("bytes=1132;sha256={AY_COMPAT_WRAPPER_SHA256}"),
    );
    expected.insert(
        "typed-call-sites".to_string(),
        format!("declarations=805;bytes=283312;sha256={TYPED_C_CALL_SITES_SHA256}"),
    );
    expected.insert(
        "stock-probe.additional".to_string(),
        format!("callability-markers=111;bytes=10384;sha256={ADDITIONAL_STOCK_C_PROBE_SHA256}"),
    );
    expected.insert(
        "stock-probe.remaining".to_string(),
        format!("callability-markers=115;bytes=15825;sha256={REMAINING_STOCK_C_PROBE_SHA256}"),
    );
    expected.insert(
        "stock-probe.unprobed-reasons".to_string(),
        format!(
            "count={UNPROBED_REASON_COUNT};bytes=103086;sha256={UNPROBED_REASON_MANIFEST_SHA256}"
        ),
    );
    for header in &PUBLIC_HEADERS {
        expected.insert(
            format!("header.{}", header.path),
            format!("bytes={};sha256={}", header.size, header.sha256),
        );
    }
    expected
}

/// Observations calculated from the bytes compiled into this validator.
/// Comparing this map with [`expected_c_surface_values`] rejects any missing
/// header or drift in function declarations, opaque types, enums, callbacks,
/// macros, or extension declarations.
pub(crate) fn observed_c_surface_values() -> BTreeMap<String, String> {
    let declaration_lines = PUBLIC_C_DECLARATION_MANIFEST.lines().count();
    let declaration_sha =
        crate::smtlib_conformance::sha256_bytes(PUBLIC_C_DECLARATION_MANIFEST.as_bytes());
    let mut observed = BTreeMap::new();
    observed.insert(
        "declarations".to_string(),
        format!("count={declaration_lines};sha256={declaration_sha}"),
    );
    observed.insert(
        "header.ay_z3_compat.h".to_string(),
        format!(
            "bytes={};sha256={}",
            AY_COMPAT_WRAPPER.len(),
            crate::smtlib_conformance::sha256_bytes(AY_COMPAT_WRAPPER)
        ),
    );
    observed.insert(
        "typed-call-sites".to_string(),
        format!(
            "declarations={};bytes={};sha256={}",
            TYPED_C_CALL_SITES
                .windows(b"typedef ".len())
                .filter(|window| *window == b"typedef ")
                .count(),
            TYPED_C_CALL_SITES.len(),
            crate::smtlib_conformance::sha256_bytes(TYPED_C_CALL_SITES)
        ),
    );
    for (id, source) in [
        ("stock-probe.additional", ADDITIONAL_STOCK_C_PROBE),
        ("stock-probe.remaining", REMAINING_STOCK_C_PROBE),
    ] {
        observed.insert(
            id.to_string(),
            format!(
                "callability-markers={};bytes={};sha256={}",
                stock_c_callability_markers(source).len(),
                source.len(),
                crate::smtlib_conformance::sha256_bytes(source)
            ),
        );
    }
    observed.insert(
        "stock-probe.unprobed-reasons".to_string(),
        format!(
            "count={};bytes={};sha256={}",
            UNPROBED_REASON_MANIFEST.lines().count(),
            UNPROBED_REASON_MANIFEST.len(),
            crate::smtlib_conformance::sha256_bytes(UNPROBED_REASON_MANIFEST.as_bytes())
        ),
    );
    let mut header_manifest = Vec::new();
    for header in &PUBLIC_HEADERS {
        let sha256 = crate::smtlib_conformance::sha256_bytes(header.bytes);
        observed.insert(
            format!("header.{}", header.path),
            format!("bytes={};sha256={sha256}", header.bytes.len()),
        );
        header_manifest.extend_from_slice(header.path.as_bytes());
        header_manifest.push(b'\t');
        header_manifest.extend_from_slice(header.bytes.len().to_string().as_bytes());
        header_manifest.push(b'\t');
        header_manifest.extend_from_slice(sha256.as_bytes());
        header_manifest.push(b'\n');
    }
    observed.insert(
        "header-set".to_string(),
        format!(
            "count={};sha256={}",
            PUBLIC_HEADERS.len(),
            crate::smtlib_conformance::sha256_bytes(&header_manifest)
        ),
    );
    observed
}

/// Exact public declaration names wrapped in `AY_CALL` runtime markers.
///
/// The stock-program child must emit this complete sorted inventory. A marker
/// left in a comment, dead branch, or short-circuited expression therefore
/// makes the exact transcript fail and cannot be credited as callability.
fn stock_c_callability_markers(source: &[u8]) -> BTreeSet<String> {
    let Ok(source) = std::str::from_utf8(source) else {
        return BTreeSet::new();
    };
    let public = public_c_declarations()
        .iter()
        .filter_map(|row| row.split_once('|').map(|(name, _)| name))
        .collect::<BTreeSet<_>>();
    source
        .match_indices("AY_CALL(")
        .filter_map(|(offset, marker)| {
            let tail = &source[offset + marker.len()..];
            let end = tail
                .find(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))?;
            let name = &tail[..end];
            (tail.as_bytes().get(end) == Some(&b',') && public.contains(name))
                .then(|| name.to_string())
        })
        .collect()
}

pub(crate) fn public_header_files() -> Vec<(&'static str, &'static [u8])> {
    PUBLIC_HEADERS
        .iter()
        .map(|header| (header.path, header.bytes))
        .collect()
}

pub(crate) fn stock_c_probes() -> [StockCProbe; 2] {
    [
        StockCProbe {
            id: "additional",
            source: ADDITIONAL_STOCK_C_PROBE,
            expected_stdout_trailer: b"exact Z3 5.0.0 additional family probes passed\n",
        },
        StockCProbe {
            id: "remaining",
            source: REMAINING_STOCK_C_PROBE,
            expected_stdout_trailer: b"exact Z3 5.0.0 remaining safe-call probes passed\n",
        },
    ]
}

pub(crate) fn stock_c_probe_callability_symbols(probe: &StockCProbe) -> BTreeSet<String> {
    stock_c_callability_markers(probe.source)
}

pub(crate) fn stock_c_probe_expected_stdout(probe: &StockCProbe) -> Vec<u8> {
    let mut stdout = Vec::new();
    for symbol in stock_c_probe_callability_symbols(probe) {
        stdout.extend_from_slice(b"AY-CALL ");
        stdout.extend_from_slice(symbol.as_bytes());
        stdout.push(b'\n');
    }
    stdout.extend_from_slice(probe.expected_stdout_trailer);
    stdout
}

/// Public functions authenticated by an executed `AY_CALL` marker in both
/// self-checking stock C programs. The older scoped dylib probe still provides
/// aggregate finite-set behavior evidence, but it has no per-call runtime
/// marker and therefore receives no item-level callability credit.
pub(crate) fn callability_runtime_symbols() -> BTreeSet<String> {
    let mut symbols = BTreeSet::new();
    for probe in stock_c_probes() {
        symbols.extend(stock_c_probe_callability_symbols(&probe));
    }
    symbols
}

/// APIs with a complete authenticated input/state/error/output semantic
/// contract differential. Finite successful calls do not satisfy this bar.
pub(crate) fn semantic_contract_runtime_symbols() -> BTreeSet<String> {
    BTreeSet::new()
}

pub(crate) fn public_c_declarations() -> &'static [String] {
    static DECLARATIONS: OnceLock<Vec<String>> = OnceLock::new();
    DECLARATIONS.get_or_init(|| {
        PUBLIC_C_DECLARATION_MANIFEST
            .lines()
            .map(str::to_string)
            .collect()
    })
}

pub(crate) fn c_surface_is_exact() -> bool {
    if observed_c_surface_values() != expected_c_surface_values() {
        return false;
    }
    let declarations = public_c_declarations();
    // The manifest is a `name|signature` table sorted as WHOLE ROWS. `|`
    // (0x7c) sorts after every character a Z3 symbol can contain, so a name
    // that is a proper prefix of another sorts SECOND: `Z3_mk_seq_foldli|…`
    // precedes `Z3_mk_seq_foldl|…`. Requiring the NAME column to ascend would
    // therefore reject the authentic artifact (34 such prefix pairs), so the
    // ordering obligation is pinned where it actually holds — on the row — and
    // the injectivity the name ordering was really buying is asserted
    // separately below. Strict row ordering already forbids a duplicated row.
    let mut previous_row: Option<&str> = None;
    let mut declared_names = Vec::with_capacity(declarations.len());
    for declaration in declarations {
        let Some((name, signature)) = declaration.split_once('|') else {
            return false;
        };
        if name.len() <= 3
            || !name.starts_with("Z3_")
            || !name[3..]
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
            || signature.is_empty()
            || signature.contains('|')
            || previous_row.is_some_and(|prior| prior >= declaration.as_str())
        {
            return false;
        }
        previous_row = Some(declaration);
        declared_names.push(name);
    }
    let exports = required_symbols()
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    declared_names.len() == PUBLIC_C_DECLARATION_COUNT
        && declared_names
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            .len()
            == declared_names.len()
        && declared_names.iter().all(|name| exports.contains(name))
        && exports.len() - declared_names.len() == 2
        && exports.contains("Z3_get_numeral_rational")
        && exports.contains("Z3_mk_bvmsb")
        && unprobed_reason_manifest_is_well_formed(&declared_names)
}

fn unprobed_reason_manifest_is_well_formed(declared_names: &[&str]) -> bool {
    let declared = declared_names.iter().copied().collect::<BTreeSet<_>>();
    let callability = callability_runtime_symbols();
    let expected_missing = declared
        .iter()
        .copied()
        .filter(|name| !callability.contains(*name))
        .collect::<BTreeSet<_>>();
    let mut previous: Option<&str> = None;
    let mut classified = BTreeSet::new();
    for row in UNPROBED_REASON_MANIFEST.lines() {
        let mut fields = row.split('\t');
        let (Some(name), Some(category), Some(reason), None) =
            (fields.next(), fields.next(), fields.next(), fields.next())
        else {
            return false;
        };
        if !declared.contains(name)
            || previous.is_some_and(|prior| prior >= name)
            || category.is_empty()
            || !category
                .bytes()
                .all(|byte| byte.is_ascii_lowercase() || byte == b'-')
            || reason.is_empty()
        {
            return false;
        }
        previous = Some(name);
        classified.insert(name);
    }
    classified.len() == UNPROBED_REASON_COUNT
        && classified == expected_missing
        && classified.len() + callability.len() == PUBLIC_C_DECLARATION_COUNT
}

pub(crate) fn required_symbols() -> &'static [String] {
    static SYMBOLS: OnceLock<Vec<String>> = OnceLock::new();
    SYMBOLS.get_or_init(|| {
        REQUIRED_SYMBOL_MANIFEST
            .lines()
            .map(str::to_string)
            .collect()
    })
}

/// Hidden child entry point. Required symbols are supplied one-per-line on
/// stdin; an empty stdin asks only for the library's own export inventory.
pub(crate) fn run_probe_child(args: &[String]) -> i32 {
    if args.len() != 1 {
        eprintln!("z3-abi-probe needs exactly one shared-library path");
        return 2;
    }
    let mut input = Vec::new();
    if let Err(error) = std::io::stdin()
        .take(MAX_REQUIRED_SYMBOL_INPUT + 1)
        .read_to_end(&mut input)
    {
        eprintln!("reading required-symbol manifest: {error}");
        return 2;
    }
    if input.len() as u64 > MAX_REQUIRED_SYMBOL_INPUT {
        eprintln!("required-symbol manifest exceeds fixed input limit");
        return 2;
    }
    let required = match parse_required_symbols(&input) {
        Ok(required) => required,
        Err(error) => {
            eprintln!("{error}");
            return 2;
        }
    };
    let observation = match probe_library(Path::new(&args[0]), &required) {
        Ok(observation) => observation,
        Err(error) => {
            eprintln!("{error}");
            return 2;
        }
    };
    match serde_json::to_string(&observation) {
        Ok(json) => {
            println!("{json}");
            0
        }
        Err(error) => {
            eprintln!("serializing Z3 ABI observation: {error}");
            2
        }
    }
}

fn parse_required_symbols(input: &[u8]) -> Result<Vec<String>, String> {
    let text = std::str::from_utf8(input)
        .map_err(|error| format!("required-symbol manifest is not UTF-8: {error}"))?;
    let mut symbols = Vec::new();
    let mut previous: Option<&str> = None;
    for symbol in text.lines() {
        if symbol.len() <= 3
            || !symbol.starts_with("Z3_")
            || !symbol[3..]
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        {
            return Err(format!("invalid required Z3 symbol {symbol:?}"));
        }
        if previous.is_some_and(|value| value >= symbol) {
            return Err("required-symbol manifest must be sorted and duplicate-free".to_string());
        }
        previous = Some(symbol);
        symbols.push(symbol.to_string());
    }
    Ok(symbols)
}

fn probe_library(path: &Path, required: &[String]) -> Result<LibraryObservation, String> {
    let exported_z3_symbols = loader::nm_z3_symbols(path)?.into_iter().collect::<Vec<_>>();
    let library = loader::open_local(path)?;
    let resolution_targets = if required.is_empty() {
        &exported_z3_symbols
    } else {
        required
    };
    let required_resolvable_symbols = resolution_targets
        .iter()
        .filter(|name| loader::has_symbol(&library, name))
        .cloned()
        .collect::<Vec<_>>();
    let full_version = loader::full_version(&library);
    let ay_build_stamp = loader::ay_build_stamp(&library);

    let mut probes = expected_probe_values()
        .into_keys()
        .map(|id| (id, "unavailable".to_string()))
        .collect::<BTreeMap<_, _>>();
    // These are reserved enum values, not constructible public AST nodes.
    probes.insert(
        "decl-kind.finite-set-ext".to_string(),
        0xc00bu32.to_string(),
    );
    probes.insert(
        "decl-kind.finite-set-map-inverse".to_string(),
        0xc00cu32.to_string(),
    );
    match Api::load(&library) {
        Ok(api) => match run_finite_set_probes(&api) {
            Ok(observed) => {
                probes.extend(observed);
            }
            Err(error) => {
                let normalized = normalize_probe_error(&error);
                for value in probes.values_mut() {
                    if value == "unavailable" {
                        *value = normalized.clone();
                    }
                }
            }
        },
        Err(error) => {
            let normalized = normalize_probe_error(&error);
            for value in probes.values_mut() {
                if value == "unavailable" {
                    *value = normalized.clone();
                }
            }
        }
    }

    Ok(LibraryObservation {
        exported_z3_symbols,
        required_resolvable_symbols,
        full_version,
        ay_build_stamp,
        probes,
    })
}

fn normalize_probe_error(error: &str) -> String {
    let compact = error
        .chars()
        .map(|ch| if ch.is_ascii_control() { ' ' } else { ch })
        .collect::<String>();
    format!("error:{}", compact.chars().take(256).collect::<String>())
}

type Ptr = *mut c_void;
type MkConfig = unsafe extern "C" fn() -> Ptr;
type DelConfig = unsafe extern "C" fn(Ptr);
type MkContext = unsafe extern "C" fn(Ptr) -> Ptr;
type DelContext = unsafe extern "C" fn(Ptr);
type MkSort = unsafe extern "C" fn(Ptr) -> Ptr;
type MkFiniteSetSort = unsafe extern "C" fn(Ptr, Ptr) -> Ptr;
type IsFiniteSetSort = unsafe extern "C" fn(Ptr, Ptr) -> bool;
type GetFiniteSetSortBasis = unsafe extern "C" fn(Ptr, Ptr) -> Ptr;
type IsEqSort = unsafe extern "C" fn(Ptr, Ptr, Ptr) -> bool;
type GetSortKind = unsafe extern "C" fn(Ptr, Ptr) -> u32;
type GetSortName = unsafe extern "C" fn(Ptr, Ptr) -> Ptr;
type GetSymbolString = unsafe extern "C" fn(Ptr, Ptr) -> *const c_char;
type AstOrSortToString = unsafe extern "C" fn(Ptr, Ptr) -> *const c_char;
type MkInt = unsafe extern "C" fn(Ptr, i32, Ptr) -> Ptr;
type MkUnaryAst = unsafe extern "C" fn(Ptr, Ptr) -> Ptr;
type MkBinaryAst = unsafe extern "C" fn(Ptr, Ptr, Ptr) -> Ptr;
type MkNaryAst = unsafe extern "C" fn(Ptr, u32, *const Ptr) -> Ptr;
type MkStringSymbol = unsafe extern "C" fn(Ptr, *const c_char) -> Ptr;
type MkConst = unsafe extern "C" fn(Ptr, Ptr, Ptr) -> Ptr;
type ToApp = unsafe extern "C" fn(Ptr, Ptr) -> Ptr;
type MkLambdaConst = unsafe extern "C" fn(Ptr, u32, *const Ptr, Ptr) -> Ptr;
type GetAppDecl = unsafe extern "C" fn(Ptr, Ptr) -> Ptr;
type GetAppNumArgs = unsafe extern "C" fn(Ptr, Ptr) -> u32;
type GetAppArg = unsafe extern "C" fn(Ptr, Ptr, u32) -> Ptr;
type GetDeclKind = unsafe extern "C" fn(Ptr, Ptr) -> u32;
type GetDeclName = unsafe extern "C" fn(Ptr, Ptr) -> Ptr;
type GetArity = unsafe extern "C" fn(Ptr, Ptr) -> u32;
type IsEqAst = unsafe extern "C" fn(Ptr, Ptr, Ptr) -> bool;
type GetDeclNumParameters = unsafe extern "C" fn(Ptr, Ptr) -> u32;
type GetDeclParameterKind = unsafe extern "C" fn(Ptr, Ptr, u32) -> u32;
type GetDeclSortParameter = unsafe extern "C" fn(Ptr, Ptr, u32) -> Ptr;
type GetSort = unsafe extern "C" fn(Ptr, Ptr) -> Ptr;
type MkSolver = unsafe extern "C" fn(Ptr) -> Ptr;
type SolverRef = unsafe extern "C" fn(Ptr, Ptr);
type SolverAssert = unsafe extern "C" fn(Ptr, Ptr, Ptr);
type SolverCheck = unsafe extern "C" fn(Ptr, Ptr) -> i32;

#[derive(Clone, Copy)]
struct Api {
    mk_config: MkConfig,
    del_config: DelConfig,
    mk_context: MkContext,
    del_context: DelContext,
    mk_int_sort: MkSort,
    mk_finite_set_sort: MkFiniteSetSort,
    is_finite_set_sort: IsFiniteSetSort,
    get_finite_set_sort_basis: GetFiniteSetSortBasis,
    is_eq_sort: IsEqSort,
    get_sort_kind: GetSortKind,
    get_sort_name: GetSortName,
    get_symbol_string: GetSymbolString,
    sort_to_string: AstOrSortToString,
    mk_set_sort: MkFiniteSetSort,
    mk_int: MkInt,
    mk_finite_set_empty: MkUnaryAst,
    mk_finite_set_singleton: MkUnaryAst,
    mk_finite_set_union: MkBinaryAst,
    mk_finite_set_intersect: MkBinaryAst,
    mk_finite_set_difference: MkBinaryAst,
    mk_finite_set_member: MkBinaryAst,
    mk_finite_set_size: MkUnaryAst,
    mk_finite_set_subset: MkBinaryAst,
    mk_finite_set_map: MkBinaryAst,
    mk_finite_set_filter: MkBinaryAst,
    mk_finite_set_range: MkBinaryAst,
    mk_eq: MkBinaryAst,
    mk_not: MkUnaryAst,
    mk_add: MkNaryAst,
    mk_string_symbol: MkStringSymbol,
    mk_const: MkConst,
    to_app: ToApp,
    mk_lambda_const: MkLambdaConst,
    get_app_decl: GetAppDecl,
    get_app_num_args: GetAppNumArgs,
    get_app_arg: GetAppArg,
    get_decl_kind: GetDeclKind,
    get_decl_name: GetDeclName,
    get_arity: GetArity,
    is_eq_ast: IsEqAst,
    ast_to_string: AstOrSortToString,
    get_decl_num_parameters: GetDeclNumParameters,
    get_decl_parameter_kind: GetDeclParameterKind,
    get_decl_sort_parameter: GetDeclSortParameter,
    get_sort: GetSort,
    mk_solver: MkSolver,
    solver_inc_ref: SolverRef,
    solver_dec_ref: SolverRef,
    solver_assert: SolverAssert,
    solver_check: SolverCheck,
}

impl Api {
    fn load(library: &loader::Library) -> Result<Self, String> {
        // SAFETY: every symbol is resolved by its exact Z3 5.0.0 C API name
        // and assigned the matching signature from z3_api.h. Calls remain
        // within this child process while `library` is alive.
        unsafe {
            Ok(Self {
                mk_config: load_symbol(library, b"Z3_mk_config\0")?,
                del_config: load_symbol(library, b"Z3_del_config\0")?,
                mk_context: load_symbol(library, b"Z3_mk_context\0")?,
                del_context: load_symbol(library, b"Z3_del_context\0")?,
                mk_int_sort: load_symbol(library, b"Z3_mk_int_sort\0")?,
                mk_finite_set_sort: load_symbol(library, b"Z3_mk_finite_set_sort\0")?,
                is_finite_set_sort: load_symbol(library, b"Z3_is_finite_set_sort\0")?,
                get_finite_set_sort_basis: load_symbol(library, b"Z3_get_finite_set_sort_basis\0")?,
                is_eq_sort: load_symbol(library, b"Z3_is_eq_sort\0")?,
                get_sort_kind: load_symbol(library, b"Z3_get_sort_kind\0")?,
                get_sort_name: load_symbol(library, b"Z3_get_sort_name\0")?,
                get_symbol_string: load_symbol(library, b"Z3_get_symbol_string\0")?,
                sort_to_string: load_symbol(library, b"Z3_sort_to_string\0")?,
                mk_set_sort: load_symbol(library, b"Z3_mk_set_sort\0")?,
                mk_int: load_symbol(library, b"Z3_mk_int\0")?,
                mk_finite_set_empty: load_symbol(library, b"Z3_mk_finite_set_empty\0")?,
                mk_finite_set_singleton: load_symbol(library, b"Z3_mk_finite_set_singleton\0")?,
                mk_finite_set_union: load_symbol(library, b"Z3_mk_finite_set_union\0")?,
                mk_finite_set_intersect: load_symbol(library, b"Z3_mk_finite_set_intersect\0")?,
                mk_finite_set_difference: load_symbol(library, b"Z3_mk_finite_set_difference\0")?,
                mk_finite_set_member: load_symbol(library, b"Z3_mk_finite_set_member\0")?,
                mk_finite_set_size: load_symbol(library, b"Z3_mk_finite_set_size\0")?,
                mk_finite_set_subset: load_symbol(library, b"Z3_mk_finite_set_subset\0")?,
                mk_finite_set_map: load_symbol(library, b"Z3_mk_finite_set_map\0")?,
                mk_finite_set_filter: load_symbol(library, b"Z3_mk_finite_set_filter\0")?,
                mk_finite_set_range: load_symbol(library, b"Z3_mk_finite_set_range\0")?,
                mk_eq: load_symbol(library, b"Z3_mk_eq\0")?,
                mk_not: load_symbol(library, b"Z3_mk_not\0")?,
                mk_add: load_symbol(library, b"Z3_mk_add\0")?,
                mk_string_symbol: load_symbol(library, b"Z3_mk_string_symbol\0")?,
                mk_const: load_symbol(library, b"Z3_mk_const\0")?,
                to_app: load_symbol(library, b"Z3_to_app\0")?,
                mk_lambda_const: load_symbol(library, b"Z3_mk_lambda_const\0")?,
                get_app_decl: load_symbol(library, b"Z3_get_app_decl\0")?,
                get_app_num_args: load_symbol(library, b"Z3_get_app_num_args\0")?,
                get_app_arg: load_symbol(library, b"Z3_get_app_arg\0")?,
                get_decl_kind: load_symbol(library, b"Z3_get_decl_kind\0")?,
                get_decl_name: load_symbol(library, b"Z3_get_decl_name\0")?,
                get_arity: load_symbol(library, b"Z3_get_arity\0")?,
                is_eq_ast: load_symbol(library, b"Z3_is_eq_ast\0")?,
                ast_to_string: load_symbol(library, b"Z3_ast_to_string\0")?,
                get_decl_num_parameters: load_symbol(library, b"Z3_get_decl_num_parameters\0")?,
                get_decl_parameter_kind: load_symbol(library, b"Z3_get_decl_parameter_kind\0")?,
                get_decl_sort_parameter: load_symbol(library, b"Z3_get_decl_sort_parameter\0")?,
                get_sort: load_symbol(library, b"Z3_get_sort\0")?,
                mk_solver: load_symbol(library, b"Z3_mk_solver\0")?,
                solver_inc_ref: load_symbol(library, b"Z3_solver_inc_ref\0")?,
                solver_dec_ref: load_symbol(library, b"Z3_solver_dec_ref\0")?,
                solver_assert: load_symbol(library, b"Z3_solver_assert\0")?,
                solver_check: load_symbol(library, b"Z3_solver_check\0")?,
            })
        }
    }
}

unsafe fn load_symbol<T: Copy>(
    library: &loader::Library,
    name: &'static [u8],
) -> Result<T, String> {
    // SAFETY: the caller supplies the exact C signature associated with
    // `name`; the copied function pointer is used only while the library lives.
    unsafe {
        library.get::<T>(name).map(|symbol| *symbol).map_err(|_| {
            format!(
                "missing {}",
                CStr::from_bytes_with_nul(name)
                    .map(|value| value.to_string_lossy())
                    .unwrap_or_else(|_| "<invalid-symbol>".into())
            )
        })
    }
}

struct ContextGuard<'a> {
    api: &'a Api,
    context: Ptr,
}

impl Drop for ContextGuard<'_> {
    fn drop(&mut self) {
        // SAFETY: this context was returned by `Z3_mk_context` from the same
        // loaded API and is deleted exactly once after all child probes.
        unsafe {
            (self.api.del_context)(self.context);
        }
    }
}

fn run_finite_set_probes(api: &Api) -> Result<BTreeMap<String, String>, String> {
    // SAFETY: every call uses handles created by this exact API/context and
    // the corresponding Z3 5.0.0 signature. The entire sequence is isolated
    // in the guarded probe child.
    let mut observed = unsafe { run_finite_set_probes_unsafe(api, None) }?;
    for (name, _) in SEMANTIC_PROBES {
        // SAFETY: give every decision probe a fresh context. Reusing AY's shared
        // decision engine across a long sequence of independent solver
        // handles caused accumulated search state to dominate the fixed
        // validator timeout even though each law is individually cheap.
        // Z3 contexts also isolate the reference observations symmetrically.
        let mut one = unsafe { run_finite_set_probes_unsafe(api, Some(name)) }?;
        let key = format!("semantics.{name}");
        let value = one
            .remove(&key)
            .ok_or_else(|| format!("semantic probe {name} produced no observation"))?;
        observed.insert(key, value);
    }
    Ok(observed)
}

unsafe fn run_finite_set_probes_unsafe(
    api: &Api,
    selected_semantic: Option<&str>,
) -> Result<BTreeMap<String, String>, String> {
    // SAFETY: upheld by `run_finite_set_probes`.
    let config = unsafe { (api.mk_config)() };
    let config = require_ptr(config, "Z3_mk_config")?;
    // SAFETY: `config` belongs to this API.
    let context = unsafe { (api.mk_context)(config) };
    // SAFETY: the configuration is no longer needed after context creation.
    unsafe { (api.del_config)(config) };
    let context = require_ptr(context, "Z3_mk_context")?;
    let guard = ContextGuard { api, context };
    let c = guard.context;

    let mut observed = BTreeMap::new();
    let int_sort = require_ptr(
        // SAFETY: `c` is the live context owned by `guard`.
        unsafe { (api.mk_int_sort)(c) },
        "Z3_mk_int_sort",
    )?;
    let set_sort = require_ptr(
        // SAFETY: `int_sort` belongs to `c`.
        unsafe { (api.mk_finite_set_sort)(c, int_sort) },
        "Z3_mk_finite_set_sort",
    )?;
    // SAFETY: both sorts belong to `c`.
    observed.insert(
        "finite-sort-is-finite".to_string(),
        unsafe { (api.is_finite_set_sort)(c, set_sort) }.to_string(),
    );
    // SAFETY: `int_sort` belongs to `c`.
    observed.insert(
        "int-sort-is-not-finite".to_string(),
        (!unsafe { (api.is_finite_set_sort)(c, int_sort) }).to_string(),
    );
    let basis = require_ptr(
        // SAFETY: `set_sort` is a finite-set sort in `c`.
        unsafe { (api.get_finite_set_sort_basis)(c, set_sort) },
        "Z3_get_finite_set_sort_basis",
    )?;
    // SAFETY: all sort handles belong to `c`.
    observed.insert(
        "finite-sort-basis-is-int".to_string(),
        unsafe { (api.is_eq_sort)(c, basis, int_sort) }.to_string(),
    );
    // SAFETY: `set_sort` belongs to `c`.
    observed.insert(
        "finite-sort-kind".to_string(),
        unsafe { (api.get_sort_kind)(c, set_sort) }.to_string(),
    );
    // SAFETY: `set_sort` belongs to `c`.
    let finite_sort_name = require_ptr(
        unsafe { (api.get_sort_name)(c, set_sort) },
        "Z3_get_sort_name",
    )?;
    // SAFETY: the returned symbol belongs to `c`; the static string is copied
    // before another string-producing API call.
    observed.insert(
        "finite-sort-name".to_string(),
        copy_c_string(
            unsafe { (api.get_symbol_string)(c, finite_sort_name) },
            "Z3_get_symbol_string",
        )?,
    );
    // SAFETY: `set_sort` belongs to `c`.
    observed.insert(
        "finite-sort-text".to_string(),
        copy_c_string(
            unsafe { (api.sort_to_string)(c, set_sort) },
            "Z3_sort_to_string",
        )?,
    );
    // SAFETY: `int_sort` belongs to `c`.
    let legacy_set_sort = require_ptr(unsafe { (api.mk_set_sort)(c, int_sort) }, "Z3_mk_set_sort")?;
    // SAFETY: both sort handles belong to `c`.
    observed.insert(
        "finite-sort-differs-from-legacy-array-set".to_string(),
        (!unsafe { (api.is_eq_sort)(c, set_sort, legacy_set_sort) }).to_string(),
    );
    // SAFETY: a finite-set sort is a valid element sort for a nested finite
    // set in the same context.
    let nested_set_sort = require_ptr(
        unsafe { (api.mk_finite_set_sort)(c, set_sort) },
        "nested Z3_mk_finite_set_sort",
    )?;
    // SAFETY: `nested_set_sort` belongs to `c`.
    observed.insert(
        "nested-finite-sort-text".to_string(),
        copy_c_string(
            unsafe { (api.sort_to_string)(c, nested_set_sort) },
            "nested Z3_sort_to_string",
        )?,
    );
    // SAFETY: `nested_set_sort` is a finite-set sort in `c`.
    let nested_basis = require_ptr(
        unsafe { (api.get_finite_set_sort_basis)(c, nested_set_sort) },
        "nested Z3_get_finite_set_sort_basis",
    )?;
    // SAFETY: `nested_basis` and `set_sort` belong to `c`.
    let nested_basis_matches = unsafe { (api.is_eq_sort)(c, nested_basis, set_sort) };
    // SAFETY: `nested_basis` was just confirmed by construction as a
    // finite-set sort.
    let nested_inner_basis = require_ptr(
        unsafe { (api.get_finite_set_sort_basis)(c, nested_basis) },
        "inner Z3_get_finite_set_sort_basis",
    )?;
    // SAFETY: both sort handles belong to `c`.
    observed.insert(
        "nested-finite-sort-basis-round-trip".to_string(),
        (nested_basis_matches && unsafe { (api.is_eq_sort)(c, nested_inner_basis, int_sort) })
            .to_string(),
    );

    let zero = mk_int(api, c, int_sort, 0)?;
    let one = mk_int(api, c, int_sort, 1)?;
    let two = mk_int(api, c, int_sort, 2)?;
    let three = mk_int(api, c, int_sort, 3)?;
    let four = mk_int(api, c, int_sort, 4)?;
    let empty = require_ptr(
        // SAFETY: `set_sort` belongs to `c`.
        unsafe { (api.mk_finite_set_empty)(c, set_sort) },
        "Z3_mk_finite_set_empty",
    )?;
    let singleton_one = require_ptr(
        // SAFETY: `one` belongs to `c`.
        unsafe { (api.mk_finite_set_singleton)(c, one) },
        "Z3_mk_finite_set_singleton",
    )?;
    let singleton_two = require_ptr(
        // SAFETY: `two` belongs to `c`.
        unsafe { (api.mk_finite_set_singleton)(c, two) },
        "Z3_mk_finite_set_singleton",
    )?;
    let union = require_ptr(
        // SAFETY: both finite sets belong to `c`.
        unsafe { (api.mk_finite_set_union)(c, singleton_one, singleton_two) },
        "Z3_mk_finite_set_union",
    )?;
    let intersect = require_ptr(
        // SAFETY: both finite sets belong to `c`.
        unsafe { (api.mk_finite_set_intersect)(c, union, singleton_one) },
        "Z3_mk_finite_set_intersect",
    )?;
    let difference = require_ptr(
        // SAFETY: both finite sets belong to `c`.
        unsafe { (api.mk_finite_set_difference)(c, union, singleton_one) },
        "Z3_mk_finite_set_difference",
    )?;
    let member_one_empty = require_ptr(
        // SAFETY: arguments belong to `c` and have the documented sorts.
        unsafe { (api.mk_finite_set_member)(c, one, empty) },
        "Z3_mk_finite_set_member",
    )?;
    let size_empty = require_ptr(
        // SAFETY: `empty` belongs to `c`.
        unsafe { (api.mk_finite_set_size)(c, empty) },
        "Z3_mk_finite_set_size",
    )?;
    let subset = require_ptr(
        // SAFETY: both finite sets belong to `c`.
        unsafe { (api.mk_finite_set_subset)(c, singleton_one, union) },
        "Z3_mk_finite_set_subset",
    )?;
    let range = require_ptr(
        // SAFETY: integer bounds belong to `c`.
        unsafe { (api.mk_finite_set_range)(c, one, three) },
        "Z3_mk_finite_set_range",
    )?;

    let symbol_name = c"x";
    // SAFETY: the symbol string is static and NUL-terminated.
    let symbol = require_ptr(
        unsafe { (api.mk_string_symbol)(c, symbol_name.as_ptr()) },
        "Z3_mk_string_symbol",
    )?;
    // SAFETY: symbol and sort belong to `c`.
    let x = require_ptr(
        unsafe { (api.mk_const)(c, symbol, int_sort) },
        "Z3_mk_const",
    )?;
    // SAFETY: a constant AST is an application in the same context.
    let x_app = require_ptr(unsafe { (api.to_app)(c, x) }, "Z3_to_app")?;
    let add_args = [x, one];
    // SAFETY: both add arguments belong to `c`.
    let increment_body = require_ptr(
        unsafe { (api.mk_add)(c, add_args.len() as u32, add_args.as_ptr()) },
        "Z3_mk_add",
    )?;
    let bound = [x_app];
    // SAFETY: bound application and body belong to `c`.
    let increment = require_ptr(
        unsafe { (api.mk_lambda_const)(c, 1, bound.as_ptr(), increment_body) },
        "Z3_mk_lambda_const",
    )?;
    // SAFETY: lambda and finite set belong to `c`.
    let mapped = require_ptr(
        unsafe { (api.mk_finite_set_map)(c, increment, singleton_one) },
        "Z3_mk_finite_set_map",
    )?;
    let filter_equal_one = mk_eq(api, c, one, x)?;
    // SAFETY: the equality belongs to `c`.
    let filter_body = require_ptr(unsafe { (api.mk_not)(c, filter_equal_one) }, "Z3_mk_not")?;
    // SAFETY: bound application and body belong to `c`.
    let predicate = require_ptr(
        unsafe { (api.mk_lambda_const)(c, 1, bound.as_ptr(), filter_body) },
        "Z3_mk_lambda_const",
    )?;
    // SAFETY: lambda and finite set belong to `c`.
    let filtered = require_ptr(
        unsafe { (api.mk_finite_set_filter)(c, predicate, union) },
        "Z3_mk_finite_set_filter",
    )?;

    record_ast_observation(&mut observed, api, c, "empty", empty, &[])?;
    record_ast_observation(&mut observed, api, c, "singleton", singleton_one, &[one])?;
    record_ast_observation(
        &mut observed,
        api,
        c,
        "union",
        union,
        &[singleton_one, singleton_two],
    )?;
    record_ast_observation(
        &mut observed,
        api,
        c,
        "intersect",
        intersect,
        &[union, singleton_one],
    )?;
    record_ast_observation(
        &mut observed,
        api,
        c,
        "difference",
        difference,
        &[union, singleton_one],
    )?;
    record_ast_observation(&mut observed, api, c, "in", member_one_empty, &[one, empty])?;
    record_ast_observation(&mut observed, api, c, "size", size_empty, &[empty])?;
    record_ast_observation(
        &mut observed,
        api,
        c,
        "subset",
        subset,
        &[singleton_one, union],
    )?;
    record_ast_observation(
        &mut observed,
        api,
        c,
        "map",
        mapped,
        &[increment, singleton_one],
    )?;
    record_ast_observation(
        &mut observed,
        api,
        c,
        "filter",
        filtered,
        &[predicate, union],
    )?;
    record_ast_observation(&mut observed, api, c, "range", range, &[one, three])?;

    let empty_decl = app_decl(api, c, empty)?;
    // SAFETY: `empty_decl` belongs to `c`.
    let empty_parameter_count = unsafe { (api.get_decl_num_parameters)(c, empty_decl) };
    observed.insert(
        "ast.empty.decl-parameter-count".to_string(),
        empty_parameter_count.to_string(),
    );
    if empty_parameter_count > 0 {
        // SAFETY: parameter zero exists and `empty_decl` belongs to `c`.
        let parameter_kind = unsafe { (api.get_decl_parameter_kind)(c, empty_decl, 0) };
        observed.insert(
            "ast.empty.decl-parameter-kind-0".to_string(),
            parameter_kind.to_string(),
        );
        // SAFETY: exact Z3 5.0.0 reports parameter zero as a SORT parameter.
        // A subject that violates that contract may reject this typed accessor;
        // the guarded child turns such an ABI failure into a failed gate.
        let parameter_sort = require_ptr(
            unsafe { (api.get_decl_sort_parameter)(c, empty_decl, 0) },
            "Z3_get_decl_sort_parameter",
        )?;
        // SAFETY: `empty` belongs to `c`.
        let result_sort = require_ptr(unsafe { (api.get_sort)(c, empty) }, "Z3_get_sort(empty)")?;
        // SAFETY: both sorts belong to `c`.
        observed.insert(
            "ast.empty.decl-parameter-sort-0-is-result-sort".to_string(),
            unsafe { (api.is_eq_sort)(c, parameter_sort, result_sort) }.to_string(),
        );
    }

    for (name, ast) in [
        ("finite-set-empty", empty),
        ("finite-set-singleton", singleton_one),
        ("finite-set-union", union),
        ("finite-set-intersect", intersect),
        ("finite-set-difference", difference),
        ("finite-set-in", member_one_empty),
        ("finite-set-size", size_empty),
        ("finite-set-subset", subset),
        ("finite-set-map", mapped),
        ("finite-set-filter", filtered),
        ("finite-set-range", range),
    ] {
        observed.insert(
            format!("decl-kind.{name}"),
            decl_kind(api, c, ast)?.to_string(),
        );
    }

    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "empty-size-zero",
        mk_eq(api, c, size_empty, zero)?,
        true,
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "empty-excludes-one",
        member_one_empty,
        false,
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "singleton-includes-one",
        mk_member(api, c, one, singleton_one)?,
        true,
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "singleton-excludes-two",
        mk_member(api, c, two, singleton_one)?,
        false,
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "singleton-size-one",
        mk_eq(api, c, mk_size(api, c, singleton_one)?, one)?,
        true,
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "union-includes-one",
        mk_member(api, c, one, union)?,
        true,
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "union-includes-two",
        mk_member(api, c, two, union)?,
        true,
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "intersect-is-singleton-one",
        mk_eq(api, c, intersect, singleton_one)?,
        true,
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "difference-is-singleton-two",
        mk_eq(
            api,
            c,
            require_ptr(
                // SAFETY: both finite sets belong to `c`.
                unsafe { (api.mk_finite_set_difference)(c, singleton_two, empty) },
                "Z3_mk_finite_set_difference",
            )?,
            singleton_two,
        )?,
        true,
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "singleton-subset-union",
        subset,
        true,
    )?;
    let reverse_subset = require_ptr(
        // SAFETY: both finite sets belong to `c`.
        unsafe { (api.mk_finite_set_subset)(c, singleton_two, empty) },
        "Z3_mk_finite_set_subset",
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "singleton-not-subset-empty",
        reverse_subset,
        false,
    )?;
    if selected_semantic == Some("range-produces-finite-int-set") {
        observed.insert(
            "semantics.range-produces-finite-int-set".to_string(),
            has_finite_int_sort(api, c, range, int_sort)?.to_string(),
        );
    }
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "range-includes-high",
        mk_member(api, c, three, range)?,
        true,
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "range-excludes-successor",
        mk_member(api, c, four, range)?,
        false,
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "range-size-three",
        mk_eq(api, c, mk_size(api, c, range)?, three)?,
        true,
    )?;
    if selected_semantic == Some("map-produces-finite-int-set") {
        observed.insert(
            "semantics.map-produces-finite-int-set".to_string(),
            has_finite_int_sort(api, c, mapped, int_sort)?.to_string(),
        );
    }
    if selected_semantic == Some("filter-produces-finite-int-set") {
        observed.insert(
            "semantics.filter-produces-finite-int-set".to_string(),
            has_finite_int_sort(api, c, filtered, int_sort)?.to_string(),
        );
    }
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "filter-retains-two",
        mk_member(api, c, two, filtered)?,
        true,
    )?;
    record_law(
        &mut observed,
        selected_semantic,
        api,
        c,
        "filter-removes-one",
        mk_member(api, c, one, filtered)?,
        false,
    )?;

    Ok(observed)
}

fn require_ptr(value: Ptr, operation: &str) -> Result<Ptr, String> {
    if value.is_null() {
        Err(format!("{operation} returned NULL"))
    } else {
        Ok(value)
    }
}

fn copy_c_string(value: *const c_char, operation: &str) -> Result<String, String> {
    if value.is_null() {
        return Err(format!("{operation} returned NULL"));
    }
    // SAFETY: the Z3 string-producing APIs return a NUL-terminated pointer
    // valid until the next string-producing call on this context. Copying it
    // immediately prevents the borrowed pointer from escaping.
    let value = unsafe { CStr::from_ptr(value) };
    value
        .to_str()
        .map(str::to_string)
        .map_err(|error| format!("{operation} returned non-UTF-8 text: {error}"))
}

fn compact_whitespace(value: &str) -> String {
    value.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn app_decl(api: &Api, context: Ptr, ast: Ptr) -> Result<Ptr, String> {
    // SAFETY: `ast` is an application owned by the active probe context.
    let app = require_ptr(unsafe { (api.to_app)(context, ast) }, "Z3_to_app")?;
    // SAFETY: `app` belongs to the active probe context.
    require_ptr(
        unsafe { (api.get_app_decl)(context, app) },
        "Z3_get_app_decl",
    )
}

fn record_ast_observation(
    observed: &mut BTreeMap<String, String>,
    api: &Api,
    context: Ptr,
    id: &str,
    ast: Ptr,
    constructor_args: &[Ptr],
) -> Result<(), String> {
    // SAFETY: `ast` is an application owned by the active probe context.
    let app = require_ptr(unsafe { (api.to_app)(context, ast) }, "Z3_to_app")?;
    // SAFETY: `app` belongs to the active probe context.
    let decl = require_ptr(
        unsafe { (api.get_app_decl)(context, app) },
        "Z3_get_app_decl",
    )?;
    // SAFETY: `decl` belongs to the active probe context.
    let decl_name = require_ptr(
        unsafe { (api.get_decl_name)(context, decl) },
        "Z3_get_decl_name",
    )?;
    // SAFETY: the returned symbol belongs to `context`; copy its string before
    // making another string-producing call.
    observed.insert(
        format!("ast.{id}.decl-name"),
        copy_c_string(
            unsafe { (api.get_symbol_string)(context, decl_name) },
            "Z3_get_symbol_string",
        )?,
    );
    // SAFETY: `decl` belongs to the active probe context.
    observed.insert(
        format!("ast.{id}.arity"),
        unsafe { (api.get_arity)(context, decl) }.to_string(),
    );
    // SAFETY: `app` belongs to the active probe context.
    let app_arg_count = unsafe { (api.get_app_num_args)(context, app) };
    observed.insert(format!("ast.{id}.app-arg-count"), app_arg_count.to_string());
    let args_match = app_arg_count as usize == constructor_args.len()
        && constructor_args
            .iter()
            .enumerate()
            .all(|(index, expected)| {
                // SAFETY: the index is below the observed application arity,
                // and all compared AST handles belong to `context`.
                let actual = unsafe { (api.get_app_arg)(context, app, index as u32) };
                !actual.is_null() && unsafe { (api.is_eq_ast)(context, actual, *expected) }
            });
    observed.insert(format!("ast.{id}.args-match"), args_match.to_string());
    // SAFETY: `ast` belongs to the active probe context.
    let text = copy_c_string(
        unsafe { (api.ast_to_string)(context, ast) },
        "Z3_ast_to_string",
    )?;
    observed.insert(
        format!("ast.{id}.canonical-text"),
        compact_whitespace(&text),
    );
    Ok(())
}

fn mk_int(api: &Api, context: Ptr, sort: Ptr, value: i32) -> Result<Ptr, String> {
    // SAFETY: context and sort are owned by the active probe context.
    require_ptr(unsafe { (api.mk_int)(context, value, sort) }, "Z3_mk_int")
}

fn mk_eq(api: &Api, context: Ptr, left: Ptr, right: Ptr) -> Result<Ptr, String> {
    // SAFETY: both terms are owned by the active probe context.
    require_ptr(unsafe { (api.mk_eq)(context, left, right) }, "Z3_mk_eq")
}

fn mk_member(api: &Api, context: Ptr, element: Ptr, set: Ptr) -> Result<Ptr, String> {
    // SAFETY: both terms are owned by the active probe context and sorted for
    // the finite-set membership constructor.
    require_ptr(
        unsafe { (api.mk_finite_set_member)(context, element, set) },
        "Z3_mk_finite_set_member",
    )
}

fn mk_size(api: &Api, context: Ptr, set: Ptr) -> Result<Ptr, String> {
    // SAFETY: the finite-set term is owned by the active probe context.
    require_ptr(
        unsafe { (api.mk_finite_set_size)(context, set) },
        "Z3_mk_finite_set_size",
    )
}

fn decl_kind(api: &Api, context: Ptr, ast: Ptr) -> Result<u32, String> {
    let decl = app_decl(api, context, ast)?;
    // SAFETY: `decl` belongs to the active probe context.
    Ok(unsafe { (api.get_decl_kind)(context, decl) })
}

fn has_finite_int_sort(api: &Api, context: Ptr, ast: Ptr, int_sort: Ptr) -> Result<bool, String> {
    // SAFETY: `ast` belongs to the active probe context.
    let sort = require_ptr(unsafe { (api.get_sort)(context, ast) }, "Z3_get_sort")?;
    // SAFETY: all sort handles belong to the active probe context.
    if !unsafe { (api.is_finite_set_sort)(context, sort) } {
        return Ok(false);
    }
    // SAFETY: `sort` was just confirmed as a finite-set sort.
    let basis = require_ptr(
        unsafe { (api.get_finite_set_sort_basis)(context, sort) },
        "Z3_get_finite_set_sort_basis",
    )?;
    // SAFETY: both sorts belong to the active probe context.
    Ok(unsafe { (api.is_eq_sort)(context, basis, int_sort) })
}

fn record_law(
    observed: &mut BTreeMap<String, String>,
    selected_semantic: Option<&str>,
    api: &Api,
    context: Ptr,
    name: &str,
    proposition: Ptr,
    expected_true: bool,
) -> Result<(), String> {
    if selected_semantic != Some(name) {
        return Ok(());
    }
    let value = prove_boolean(api, context, proposition, expected_true)?;
    observed.insert(format!("semantics.{name}"), value);
    Ok(())
}

fn prove_boolean(
    api: &Api,
    context: Ptr,
    proposition: Ptr,
    expected_true: bool,
) -> Result<String, String> {
    // SAFETY: solver and AST calls use objects from the same live context.
    unsafe {
        let solver = require_ptr((api.mk_solver)(context), "Z3_mk_solver")?;
        (api.solver_inc_ref)(context, solver);
        let assertion = if expected_true {
            match require_ptr((api.mk_not)(context, proposition), "Z3_mk_not") {
                Ok(assertion) => assertion,
                Err(error) => {
                    (api.solver_dec_ref)(context, solver);
                    return Err(error);
                }
            }
        } else {
            proposition
        };
        (api.solver_assert)(context, solver, assertion);
        let verdict = (api.solver_check)(context, solver);
        (api.solver_dec_ref)(context, solver);
        Ok(match verdict {
            -1 => "proved".to_string(),
            0 => "unknown".to_string(),
            1 => "counterexample".to_string(),
            other => format!("invalid-lbool:{other}"),
        })
    }
}

pub(crate) fn required_symbol_set_is_exact(symbols: &[String]) -> bool {
    symbols == required_symbols()
        && symbols.len() == REQUIRED_SYMBOL_COUNT
        && symbol_manifest_sha256(symbols) == REQUIRED_SYMBOL_MANIFEST_SHA256
}

#[cfg(test)]
mod tests {
    use super::{
        c_surface_is_exact, callability_runtime_symbols, expected_c_surface_values,
        expected_probe_values, observed_c_surface_values, parse_required_symbols,
        public_c_declarations, required_symbol_set_is_exact, required_symbols,
        stock_c_probe_callability_symbols, stock_c_probes, symbol_manifest_sha256,
        AUTHENTICATED_CALLABILITY_COUNT, FINITE_SET_DECL_KINDS, PUBLIC_C_DECLARATION_COUNT,
        PUBLIC_C_DECLARATION_MANIFEST_SHA256, PUBLIC_C_HEADER_SET_SHA256, REQUIRED_SYMBOL_COUNT,
        REQUIRED_SYMBOL_MANIFEST_SHA256,
    };

    #[test]
    fn required_symbols_are_strictly_sorted_z3_names() {
        assert_eq!(
            parse_required_symbols(b"Z3_alpha\nZ3_beta\n").expect("valid symbols"),
            ["Z3_alpha", "Z3_beta"]
        );
        assert!(parse_required_symbols(b"Z3_beta\nZ3_alpha\n").is_err());
        assert!(parse_required_symbols(b"Z3_alpha\nZ3_alpha\n").is_err());
        assert!(parse_required_symbols(b"not_z3\n").is_err());
    }

    #[test]
    fn finite_set_decl_kind_registry_is_closed() {
        assert_eq!(FINITE_SET_DECL_KINDS.len(), 13);
        for (index, (_, value)) in FINITE_SET_DECL_KINDS.iter().enumerate() {
            assert_eq!(*value, 0xc000 + index as u32);
        }
        let expected = expected_probe_values();
        assert_eq!(expected.len(), 99);
        assert_eq!(
            expected["decl-kind.finite-set-map-inverse"],
            0xc00cu32.to_string()
        );
    }

    #[test]
    fn manifest_commitment_includes_terminal_newlines() {
        let symbols = vec!["Z3_alpha".to_string(), "Z3_beta".to_string()];
        assert_eq!(
            symbol_manifest_sha256(&symbols),
            crate::smtlib_conformance::sha256_bytes(b"Z3_alpha\nZ3_beta\n")
        );
        assert!(!required_symbol_set_is_exact(&symbols));
    }

    #[test]
    fn checked_in_z3_500_manifest_is_exact() {
        let symbols = required_symbols();
        assert_eq!(symbols.len(), REQUIRED_SYMBOL_COUNT);
        assert_eq!(
            symbol_manifest_sha256(symbols),
            REQUIRED_SYMBOL_MANIFEST_SHA256
        );
        assert!(symbols.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(required_symbol_set_is_exact(symbols));
    }

    #[test]
    fn checked_in_z3_500_public_c_surface_is_exact() {
        assert!(c_surface_is_exact());
        assert_eq!(public_c_declarations().len(), PUBLIC_C_DECLARATION_COUNT);
        assert_eq!(expected_c_surface_values(), observed_c_surface_values());
        assert_eq!(
            expected_c_surface_values()["declarations"],
            format!(
                "count={PUBLIC_C_DECLARATION_COUNT};sha256={PUBLIC_C_DECLARATION_MANIFEST_SHA256}"
            )
        );
        assert_eq!(
            expected_c_surface_values()["header-set"],
            format!("count=11;sha256={PUBLIC_C_HEADER_SET_SHA256}")
        );

        // The manifest's ordering obligation is on the WHOLE ROW, and the
        // symbol column is injective. Pinned as two separate properties
        // because they are not the same one: `|` sorts after every symbol
        // character, so prefix pairs (`Z3_mk_seq_foldli` before
        // `Z3_mk_seq_foldl`) make the row order and the name order disagree.
        let rows = public_c_declarations();
        assert!(
            rows.windows(2).all(|pair| pair[0] < pair[1]),
            "declaration rows must be strictly ascending"
        );
        let names = rows
            .iter()
            .map(|row| row.split_once('|').expect("declaration row").0)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            names.len(),
            rows.len(),
            "one row per declared symbol; no symbol appears twice"
        );
        assert!(
            rows.windows(2)
                .any(|pair| pair[1].split_once('|').expect("row").0
                    < pair[0].split_once('|').expect("row").0),
            "the artifact really is row-sorted, not name-sorted: at least one \
             prefix pair must descend by name"
        );
    }

    #[test]
    fn authenticated_callability_inventory_is_exact_and_public() {
        let probes = stock_c_probes();
        let additional = stock_c_probe_callability_symbols(&probes[0]);
        let remaining = stock_c_probe_callability_symbols(&probes[1]);
        assert_eq!(additional.len(), 111);
        assert_eq!(remaining.len(), 115);
        assert_eq!(additional.intersection(&remaining).count(), 9);

        let callability = callability_runtime_symbols();
        assert_eq!(callability.len(), AUTHENTICATED_CALLABILITY_COUNT);
        let declared = public_c_declarations()
            .iter()
            .map(|row| row.split_once('|').expect("declaration row").0)
            .collect::<std::collections::BTreeSet<_>>();
        assert!(callability
            .iter()
            .all(|symbol| declared.contains(symbol.as_str())));
        assert_eq!(PUBLIC_C_DECLARATION_COUNT - callability.len(), 588);
    }
}
