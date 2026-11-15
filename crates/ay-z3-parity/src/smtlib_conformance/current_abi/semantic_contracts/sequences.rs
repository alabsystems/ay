// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Selected string, general sequence and regular-expression C API witnesses.
//!
//! The pinned api_seq.cpp and util/zstring.cpp distinguish the byte-oriented
//! mk_string/mk_lstring entry points from mk_u32string code points. In
//! particular, a UTF-8 byte sequence is not decoded by those C constructors,
//! and get_lstring is not a general UTF-8 encoder. Every fixture preserves
//! that distinction and retains its ASTs in a reference-counted context.
//! These finite literal/state checks leave arbitrary languages, symbolic
//! problems, invalid Unicode domains, resource limits and interleavings open.

use super::{Aspect, Claim, Family};

pub(super) const REMAINING_SCOPE: &str = "String and sequence checks cover only the named small literals, byte/code-point conversions, one ground Seq(Int) model and selected safe error cases. Arbitrary symbolic sequences, large or cyclic regex languages, all Unicode/invalid-encoding inputs, higher-order sequence operations, alternate encoding settings, unbounded solver/resource behavior, callbacks and every unlisted state or argument domain remain unqualified.";

pub(super) const FAMILIES: &[Family] = &[
    Family {
        id: "contract-string-codec",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/sequence_helpers.h"),
            include_str!("../contracts/string_codec.c")
        ),
        checks: &[
            "string.codec.context-created",
            "string.codec.string-sort",
            "string.codec.ascii-roundtrip",
            "string.codec.unicode-escape-construction",
            "string.codec.codepoint-extraction",
            "string.codec.utf8-bytes-are-not-decoded",
            "string.codec.length-string-byte-extraction",
            "string.codec.embedded-nul-versus-c-terminator",
            "string.codec.nul-is-escaped-on-extraction",
            "string.codec.length-constructor-does-not-unescape",
            "string.codec.wide-codepoints-are-escaped",
            "string.codec.retained-literals-survive-churn",
        ],
    },
    Family {
        id: "contract-string-operations",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/sequence_helpers.h"),
            include_str!("../contracts/string_operations.c")
        ),
        checks: &[
            "string.operations.context-created",
            "string.operations.setup",
            "string.operations.concat-and-empty",
            "string.operations.length",
            "string.operations.extract-and-clamped-tail",
            "string.operations.extract-outside-is-empty",
            "string.operations.at-singleton-and-outside",
            "string.operations.index-offset-and-absence",
            "string.operations.prefix-suffix-contains",
            "string.operations.replace-first-only",
            "string.operations.codepoint-roundtrip-and-domain",
        ],
    },
    Family {
        id: "contract-sequence-operations",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/sequence_helpers.h"),
            include_str!("../contracts/sequence_operations.c")
        ),
        checks: &[
            "sequence.operations.context-created",
            "sequence.operations.sort-basis",
            "sequence.operations.empty-and-unit",
            "sequence.operations.concat-length",
            "sequence.operations.extract",
            "sequence.operations.at-and-nth",
            "sequence.operations.index-offset",
            "sequence.operations.contains-prefix-suffix",
            "sequence.operations.boundary-is-empty",
            "sequence.operations.solver-created",
            "sequence.operations.solver-satisfiable",
            "sequence.operations.exact-model-value",
            "sequence.operations.retained-after-solver-release",
        ],
    },
    Family {
        id: "contract-regex-membership",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/sequence_helpers.h"),
            include_str!("../contracts/regex_membership.c")
        ),
        checks: &[
            "regex.membership.context-created",
            "regex.membership.sort-basis",
            "regex.membership.literal-exact-language",
            "regex.membership.union",
            "regex.membership.concat-order",
            "regex.membership.star-versus-plus",
            "regex.membership.optional",
            "regex.membership.bounded-loop",
            "regex.membership.character-range",
            "regex.membership.difference-and-intersection",
            "regex.membership.complement-and-allchar",
            "regex.membership.empty-versus-full",
        ],
    },
    Family {
        id: "contract-string-errors",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/sequence_helpers.h"),
            include_str!("../contracts/string_errors.c")
        ),
        checks: &[
            "string.errors.context-created",
            "string.errors.setup",
            "string.errors.wrong-content-length-refused",
            "string.errors.content-call-recovers",
            "string.errors.null-length-refused",
            "string.errors.null-nonempty-buffer-refused",
            "string.errors.empty-null-buffer-accepted",
            "string.errors.nonstring-length-refused",
            "string.errors.nonsequence-basis-refused",
            "string.errors.valid-call-after-errors",
        ],
    },
];

pub(super) const CLAIMS: &[Claim] = &[
    Claim { family: "contract-string-codec", check: "string.codec.string-sort", aspect: Aspect::Output, functions: &["Z3_mk_string_sort", "Z3_is_string_sort", "Z3_is_seq_sort"], statement: "The string sort is classified as both String and a sequence sort." },
    Claim { family: "contract-string-codec", check: "string.codec.ascii-roundtrip", aspect: Aspect::Output, functions: &["Z3_mk_string", "Z3_is_string", "Z3_get_string", "Z3_get_string_length"], statement: "The ASCII literal abc is recognized as a string literal with exact three-character length and byte spelling." },
    Claim { family: "contract-string-codec", check: "string.codec.unicode-escape-construction", aspect: Aspect::Output, functions: &["Z3_mk_u32string", "Z3_mk_string"], statement: "Code points [0x61,0x100,0x1f600] equal the escaped C input a\\u{100}\\u{1f600}, with length three." },
    Claim { family: "contract-string-codec", check: "string.codec.codepoint-extraction", aspect: Aspect::Output, functions: &["Z3_get_string_contents", "Z3_get_string"], statement: "The retained three-code-point literal returns the original unsigned code points and escaped high-character spelling." },
    Claim { family: "contract-string-codec", check: "string.codec.utf8-bytes-are-not-decoded", aspect: Aspect::Output, functions: &["Z3_mk_string", "Z3_mk_lstring", "Z3_mk_u32string", "Z3_get_string_length", "Z3_get_string_contents"], statement: "C input bytes C3 A9 form two byte-valued characters with both byte-oriented constructors and differ from the single code point E9." },
    Claim { family: "contract-string-codec", check: "string.codec.length-string-byte-extraction", aspect: Aspect::Output, functions: &["Z3_get_lstring"], statement: "Extracting the byte-valued characters C3 A9 returns exactly those two bytes, not a new UTF-8 encoding." },
    Claim { family: "contract-string-codec", check: "string.codec.embedded-nul-versus-c-terminator", aspect: Aspect::Output, functions: &["Z3_mk_lstring", "Z3_mk_string", "Z3_get_string_length", "Z3_get_string_contents"], statement: "Explicit-length A,NUL,B has three characters including zero; the NUL-terminated constructor stops after A, and the literals are distinct." },
    Claim { family: "contract-string-codec", check: "string.codec.nul-is-escaped-on-extraction", aspect: Aspect::Output, functions: &["Z3_get_lstring"], statement: "Explicit-length A,NUL,B is returned as seven bytes A\\u{0}B by get_lstring." },
    Claim { family: "contract-string-codec", check: "string.codec.length-constructor-does-not-unescape", aspect: Aspect::Output, functions: &["Z3_mk_lstring", "Z3_mk_string"], statement: "The five raw bytes \\u{0} stay five characters under mk_lstring, while mk_string interprets them as one zero character." },
    Claim { family: "contract-string-codec", check: "string.codec.wide-codepoints-are-escaped", aspect: Aspect::Output, functions: &["Z3_get_lstring"], statement: "Code points 0x100 and0x1f600 are returned as escape sequences, with an exact explicit byte length." },
    Claim { family: "contract-string-codec", check: "string.codec.retained-literals-survive-churn", aspect: Aspect::Lifetime, functions: &["Z3_mk_context_rc", "Z3_inc_ref", "Z3_dec_ref", "Z3_get_string_contents", "Z3_get_string_length"], statement: "Explicitly retained Unicode and embedded-NUL literals survive256 distinct temporary string allocations with balanced reference releases." },
    Claim { family: "contract-string-operations", check: "string.operations.concat-and-empty", aspect: Aspect::Output, functions: &["Z3_mk_seq_empty", "Z3_mk_seq_concat", "Z3_simplify"], statement: "Concatenating ab, empty and cd produces abcd and rejects the different abab literal." },
    Claim { family: "contract-string-operations", check: "string.operations.length", aspect: Aspect::Output, functions: &["Z3_mk_seq_length"], statement: "The concatenated abcd length simplifies to4 and rejects3." },
    Claim { family: "contract-string-operations", check: "string.operations.extract-and-clamped-tail", aspect: Aspect::Output, functions: &["Z3_mk_seq_extract"], statement: "Extracting abcd at offset1 length2 gives bc; offset3 length5 is clamped to d." },
    Claim { family: "contract-string-operations", check: "string.operations.extract-outside-is-empty", aspect: Aspect::Output, functions: &["Z3_mk_seq_extract"], statement: "Negative and beyond-end extraction offsets yield the empty string for the checked literals." },
    Claim { family: "contract-string-operations", check: "string.operations.at-singleton-and-outside", aspect: Aspect::Output, functions: &["Z3_mk_seq_at"], statement: "At index1 of abcd yields singleton b; index5 yields the empty string." },
    Claim { family: "contract-string-operations", check: "string.operations.index-offset-and-absence", aspect: Aspect::Output, functions: &["Z3_mk_seq_index", "Z3_mk_seq_last_index"], statement: "Searching ab in abab returns0 from offset0 and2 from offset1, last index2; searching absent cd returns minus1." },
    Claim { family: "contract-string-operations", check: "string.operations.prefix-suffix-contains", aspect: Aspect::Output, functions: &["Z3_mk_seq_prefix", "Z3_mk_seq_suffix", "Z3_mk_seq_contains"], statement: "abcd has prefix ab, suffix cd and substring bc; it rejects prefix cd and substring abab." },
    Claim { family: "contract-string-operations", check: "string.operations.replace-first-only", aspect: Aspect::Output, functions: &["Z3_mk_seq_replace"], statement: "Replacing ab by X in abab yields Xab, not an all-occurrences XX replacement." },
    Claim { family: "contract-string-operations", check: "string.operations.codepoint-roundtrip-and-domain", aspect: Aspect::Output, functions: &["Z3_mk_string_from_code", "Z3_mk_string_to_code"], statement: "Code point256 roundtrips; a multi-character string maps to minus1 and negative code maps to empty." },
    Claim { family: "contract-sequence-operations", check: "sequence.operations.sort-basis", aspect: Aspect::Output, functions: &["Z3_mk_seq_sort", "Z3_get_seq_sort_basis", "Z3_is_seq_sort", "Z3_is_string_sort"], statement: "Seq(Int) is recognized as a sequence with Int basis and is not classified as String." },
    Claim { family: "contract-sequence-operations", check: "sequence.operations.empty-and-unit", aspect: Aspect::Output, functions: &["Z3_mk_seq_empty", "Z3_mk_seq_unit"], statement: "Unit7 and unit9 have Seq(Int) sort and are distinct." },
    Claim { family: "contract-sequence-operations", check: "sequence.operations.concat-length", aspect: Aspect::Output, functions: &["Z3_mk_seq_concat", "Z3_mk_seq_length"], statement: "Concatenating [7], empty,[9],[7] produces a length3 general sequence and rejects length2." },
    Claim { family: "contract-sequence-operations", check: "sequence.operations.extract", aspect: Aspect::Output, functions: &["Z3_mk_seq_extract"], statement: "The general-sequence middle slice is[9], and a long tail extraction is clamped to[7]." },
    Claim { family: "contract-sequence-operations", check: "sequence.operations.at-and-nth", aspect: Aspect::Output, functions: &["Z3_mk_seq_at", "Z3_mk_seq_nth"], statement: "At index1 yields sequence[9], whereas nth index1 yields Int9 and rejects7; out-of-range nth is not asserted." },
    Claim { family: "contract-sequence-operations", check: "sequence.operations.index-offset", aspect: Aspect::Output, functions: &["Z3_mk_seq_index", "Z3_mk_seq_last_index"], statement: "General-sequence search for[7] returns0 from offset0,2 from offset1, and last index2." },
    Claim { family: "contract-sequence-operations", check: "sequence.operations.contains-prefix-suffix", aspect: Aspect::Output, functions: &["Z3_mk_seq_contains", "Z3_mk_seq_prefix", "Z3_mk_seq_suffix"], statement: "The general sequence contains[9], begins and ends with[7], and rejects prefix[9]." },
    Claim { family: "contract-sequence-operations", check: "sequence.operations.boundary-is-empty", aspect: Aspect::Output, functions: &["Z3_mk_seq_at"], statement: "General-sequence at index5 yields empty for the checked length3 sequence." },
    Claim { family: "contract-sequence-operations", check: "sequence.operations.exact-model-value", aspect: Aspect::Output, functions: &["Z3_solver_assert", "Z3_solver_check", "Z3_solver_get_model", "Z3_model_eval"], statement: "A model of a Seq(Int) variable equated to[7,9,7] returns that exact sequence without model completion." },
    Claim { family: "contract-sequence-operations", check: "sequence.operations.retained-after-solver-release", aspect: Aspect::Lifetime, functions: &["Z3_solver_dec_ref", "Z3_model_inc_ref", "Z3_model_dec_ref", "Z3_model_eval"], statement: "An explicitly retained general-sequence model still evaluates the retained variable after its solver is released." },
    Claim { family: "contract-regex-membership", check: "regex.membership.sort-basis", aspect: Aspect::Output, functions: &["Z3_mk_re_sort", "Z3_is_re_sort", "Z3_get_re_sort_basis"], statement: "RegEx(String) is a regex sort with String basis and is not a sequence sort." },
    Claim { family: "contract-regex-membership", check: "regex.membership.literal-exact-language", aspect: Aspect::Output, functions: &["Z3_mk_seq_to_re", "Z3_mk_seq_in_re"], statement: "The literal regex ab accepts ab and rejects ba and empty." },
    Claim { family: "contract-regex-membership", check: "regex.membership.union", aspect: Aspect::Output, functions: &["Z3_mk_re_union"], statement: "The union of literal ab and xy accepts each member and rejects ba." },
    Claim { family: "contract-regex-membership", check: "regex.membership.concat-order", aspect: Aspect::Output, functions: &["Z3_mk_re_concat"], statement: "Regex concatenation a then b accepts ab and rejects ba." },
    Claim { family: "contract-regex-membership", check: "regex.membership.star-versus-plus", aspect: Aspect::Output, functions: &["Z3_mk_re_star", "Z3_mk_re_plus"], statement: "Star(ab) accepts empty while plus(ab) rejects it; each accepts abab and star rejects aba." },
    Claim { family: "contract-regex-membership", check: "regex.membership.optional", aspect: Aspect::Output, functions: &["Z3_mk_re_option"], statement: "Optional(ab) accepts empty and ab but rejects abab." },
    Claim { family: "contract-regex-membership", check: "regex.membership.bounded-loop", aspect: Aspect::Output, functions: &["Z3_mk_re_loop"], statement: "The2..3 loop of ab accepts two and three repetitions and rejects one repetition and empty." },
    Claim { family: "contract-regex-membership", check: "regex.membership.character-range", aspect: Aspect::Output, functions: &["Z3_mk_re_range"], statement: "Range a..c accepts a,b,c and rejects d and multi-character ab." },
    Claim { family: "contract-regex-membership", check: "regex.membership.difference-and-intersection", aspect: Aspect::Output, functions: &["Z3_mk_re_diff", "Z3_mk_re_intersect"], statement: "Range a..c minus a accepts b and rejects a; intersecting the range with b accepts only b among b,c." },
    Claim { family: "contract-regex-membership", check: "regex.membership.complement-and-allchar", aspect: Aspect::Output, functions: &["Z3_mk_re_complement", "Z3_mk_re_allchar"], statement: "Complement(ab) rejects ab and accepts ba; allchar accepts a but rejects ab." },
    Claim { family: "contract-regex-membership", check: "regex.membership.empty-versus-full", aspect: Aspect::Output, functions: &["Z3_mk_re_empty", "Z3_mk_re_full"], statement: "The empty language rejects both empty word and ab; the full language accepts both." },
    Claim { family: "contract-string-errors", check: "string.errors.wrong-content-length-refused", aspect: Aspect::Errors, functions: &["Z3_get_string_contents", "Z3_set_error_handler", "Z3_get_error_code"], statement: "Requesting three code points from ab reports INVALID_ARG through handler and error-code API without changing the provided sentinel buffer." },
    Claim { family: "contract-string-errors", check: "string.errors.content-call-recovers", aspect: Aspect::Errors, functions: &["Z3_get_string_contents"], statement: "A subsequent correct length2 call clears the error and writes only the two requested characters, preserving a trailing sentinel." },
    Claim { family: "contract-string-errors", check: "string.errors.null-length-refused", aspect: Aspect::Errors, functions: &["Z3_get_lstring"], statement: "A null output-length pointer is rejected with the pinned INVALID_ARG handler and error code." },
    Claim { family: "contract-string-errors", check: "string.errors.null-nonempty-buffer-refused", aspect: Aspect::Errors, functions: &["Z3_mk_lstring"], statement: "The pinned length constructor safely rejects a null nonempty input buffer with null and INVALID_ARG." },
    Claim { family: "contract-string-errors", check: "string.errors.empty-null-buffer-accepted", aspect: Aspect::Errors, functions: &["Z3_mk_lstring", "Z3_get_string_length"], statement: "A null buffer with explicit length0 is accepted as an empty literal, distinguishing it from the nonempty-null error." },
    Claim { family: "contract-string-errors", check: "string.errors.nonstring-length-refused", aspect: Aspect::Errors, functions: &["Z3_get_string_length"], statement: "The length getter on Int7 returns0 and reports INVALID_ARG rather than treating it as a string literal." },
    Claim { family: "contract-string-errors", check: "string.errors.nonsequence-basis-refused", aspect: Aspect::Errors, functions: &["Z3_get_seq_sort_basis"], statement: "Retrieving a sequence basis from Int sort returns null and reports INVALID_ARG." },
    Claim { family: "contract-string-errors", check: "string.errors.valid-call-after-errors", aspect: Aspect::Errors, functions: &["Z3_get_string_length"], statement: "After the invalid basis call, reading length of retained ab succeeds with2 and clears the error code." },
];
