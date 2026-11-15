// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! z3's string-literal text conventions, pinned to z3 5.1.0's answers
//! (`zstring.cpp`, `api_seq.cpp`; the C04/C10 critic probe S11/S12: with z3
//! `Length(StringVal('é')) == 1` and `StringVal('a\u{62}c') == 'abc'` are sat).

use std::ffi::{c_int, c_uint, CStr, CString};
use std::ptr;

use super::{decode_bytes, decode_escaped, encode_escaped, encode_lstring};
use crate::z3_compat::*;

#[test]
fn decode_escaped_follows_zstring() {
    assert_eq!(decode_escaped(br"a\u{62}c"), "abc");
    assert_eq!(decode_escaped(br"\u{e9}"), "\u{e9}");
    assert_eq!(decode_escaped(br"\u00e9x"), "\u{e9}x");
    assert_eq!(decode_escaped(br"\u{0}"), "\0");
    assert_eq!(decode_escaped(br"\u{2ffff}"), "\u{2ffff}");
    // Five hex digits at most, and nothing above 0x2FFFF: kept verbatim.
    assert_eq!(decode_escaped(br"\u{000041}"), r"\u{000041}");
    assert_eq!(decode_escaped(br"\u{30000}"), r"\u{30000}");
    // Not escapes in z3: empty braces, too few digits, \x, a lone backslash.
    for raw in [r"\u{}", r"\u{4", r"\u12", r"\x41", r"a\b", r"\"] {
        assert_eq!(decode_escaped(raw.as_bytes()), raw, "{raw}");
    }
    // A surrogate escape is an SMT-LIB character, stored in its carrier.
    let surrogate = decode_escaped(br"\u{d800}");
    assert_eq!(surrogate.chars().count(), 1);
    let stored = surrogate.chars().next().unwrap_or('?');
    assert_eq!(ay_core::smtlib_code_point(stored), 0xD800);
    // Raw bytes are characters, not UTF-8: "é" in UTF-8 is two characters.
    assert_eq!(decode_escaped("é".as_bytes()), "\u{c3}\u{a9}");
}

#[test]
fn decode_bytes_decodes_no_escape() {
    assert_eq!(decode_bytes(br"\u{0}"), r"\u{0}");
    assert_eq!(decode_bytes(b"a\0b"), "a\0b");
    assert_eq!(decode_bytes("é".as_bytes()), "\u{c3}\u{a9}");
}

#[test]
fn encoders_follow_z3_getters() {
    let text = "a\u{e9}\0\\u\\x\u{100}\u{2ffff}~\u{7f}";
    let escaped = r"a\u{e9}\u{0}\u{5c}u\x\u{100}\u{2ffff}~\u{7f}";
    assert_eq!(encode_escaped(text), escaped);
    let mut lstring = b"a\xe9".to_vec();
    lstring.extend_from_slice(br"\u{0}\u{5c}u\x\u{100}\u{2ffff}~");
    lstring.push(0x7f);
    assert_eq!(encode_lstring(text), lstring);
    // Escaping is invertible: each getter's output decodes to the literal.
    assert_eq!(decode_escaped(encode_escaped(text).as_bytes()), text);
    assert_eq!(decode_escaped(&encode_lstring(text)), text);
}

/// Fresh context; caller frees via `Z3_del_context`.
unsafe fn ctx() -> Z3_context {
    // SAFETY: standard config/context construction; config freed immediately.
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

unsafe fn check(c: Z3_context, fact: Z3_ast) -> c_int {
    // SAFETY: `c` is live and `fact` belongs to it.
    unsafe {
        let solver = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, solver);
        Z3_solver_assert(c, solver, fact);
        let r = Z3_solver_check(c, solver);
        Z3_solver_dec_ref(c, solver);
        r
    }
}

/// S12: `StringVal('a\\u{62}c') == 'abc'` and S11: `Length(StringVal('é')) == 1`
/// are sat on z3 (AY answered unsat before the decoder).
#[test]
fn mk_string_escapes_decide_like_z3() {
    // SAFETY: every handle lives in one context; C strings are NUL-terminated.
    unsafe {
        let c = ctx();
        let escaped = Z3_mk_string(c, c"a\\u{62}c".as_ptr());
        let abc = Z3_mk_string(c, c"abc".as_ptr());
        assert_eq!(check(c, Z3_mk_eq(c, escaped, abc)), Z3_L_TRUE);

        // What z3py's StringVal('é') sends.
        let e_acute = Z3_mk_string(c, c"\\u{e9}".as_ptr());
        assert_eq!(Z3_get_string_length(c, e_acute), 1);
        let len = Z3_mk_seq_length(c, e_acute);
        let one = Z3_mk_int(c, 1, Z3_mk_int_sort(c));
        assert_eq!(check(c, Z3_mk_eq(c, len, one)), Z3_L_TRUE);
        let two = Z3_mk_int(c, 2, Z3_mk_int_sort(c));
        assert_eq!(check(c, Z3_mk_eq(c, len, two)), Z3_L_FALSE);

        // Raw UTF-8 bytes are two characters in z3, through both constructors.
        let raw = CString::new("é").expect("no NUL");
        assert_eq!(Z3_get_string_length(c, Z3_mk_string(c, raw.as_ptr())), 2);
        let bytes = Z3_mk_lstring(c, 2, raw.as_ptr());
        assert_eq!(Z3_get_string_length(c, bytes), 2);
        // Z3_mk_lstring decodes no escape.
        let lit = Z3_mk_lstring(c, 5, c"\\u{0}".as_ptr());
        assert_eq!(Z3_get_string_length(c, lit), 5);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        Z3_del_context(c);
    }
}

#[test]
fn string_getters_escape_like_z3() {
    // SAFETY: every handle lives in one context; returned strings are
    // context-owned and read before the context is deleted.
    unsafe {
        let c = ctx();
        let codes: [c_uint; 4] = [0x61, 0xE9, 0, 0x100];
        let s = Z3_mk_u32string(c, 4, codes.as_ptr());
        let text = CStr::from_ptr(Z3_get_string(c, s));
        assert_eq!(text.to_bytes(), br"a\u{e9}\u{0}\u{100}");
        let mut len: c_uint = 0;
        let bytes = Z3_get_lstring(c, s, &raw mut len);
        let bytes = std::slice::from_raw_parts(bytes.cast::<u8>(), len as usize);
        assert_eq!(bytes, b"a\xe9\\u{0}\\u{100}");
        // Null text is an error in z3, not the empty string.
        assert_eq!(Z3_mk_string(c, ptr::null()), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_set_error(c, Z3_OK);
        assert_eq!(Z3_mk_lstring(c, 3, ptr::null()), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_del_context(c);
    }
}
