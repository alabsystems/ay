// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

#[test]
fn replace_re_union_replaces_the_leftmost_match() {
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        |ts| {
            let a = re_lit(ts, "a");
            let b = re_lit(ts, "b");
            app(ts, "re.union", &[a, b], Sort::RegLan)
        },
        "abc",
        "X",
        "Xbc",
    ));
}

#[test]
fn replace_re_union_skips_to_the_first_position_that_matches() {
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        |ts| {
            let one = re_lit(ts, "1");
            let two = re_lit(ts, "2");
            app(ts, "re.union", &[one, two], Sort::RegLan)
        },
        "a1b2c",
        "X",
        "aXb2c",
    ));
}

#[test]
fn replace_re_all_union_replaces_every_match() {
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| {
            let one = re_lit(ts, "1");
            let two = re_lit(ts, "2");
            app(ts, "re.union", &[one, two], Sort::RegLan)
        },
        "a1b2c",
        "X",
        "aXbXc",
    ));
}

// ── the two halves of "leftmost, THEN shortest" ──

#[test]
fn replace_re_takes_the_shortest_match_at_the_leftmost_position() {
    // `(re.union (str.to_re "ab") (str.to_re "a"))` matches both "ab" and "a"
    // at position 0. The clause minimizes |w| there, so "a" is replaced and
    // "bc" survives. A longest-match (PCRE-style greedy) reading would yield
    // "Xc" instead.
    let build = |ts: &mut TermStore| {
        let ab = re_lit(ts, "ab");
        let a = re_lit(ts, "a");
        app(ts, "re.union", &[ab, a], Sort::RegLan)
    };
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        build,
        "abc",
        "X",
        "Xbc",
    ));
    assert_violates(&replace_re_verdict(
        "str.replace_re",
        build,
        "abc",
        "X",
        "Xc",
    ));
}

#[test]
fn replace_re_prefers_a_leftmost_long_match_over_a_later_short_one() {
    // In "xab" the union matches "ab" at 1 and "b" at 2. `|x|` is minimized
    // FIRST, so the length-2 match at position 1 wins over the length-1 match
    // at position 2 — shortness only breaks ties within one position.
    let build = |ts: &mut TermStore| {
        let ab = re_lit(ts, "ab");
        let b = re_lit(ts, "b");
        app(ts, "re.union", &[ab, b], Sort::RegLan)
    };
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        build,
        "xab",
        "X",
        "xX",
    ));
    assert_violates(&replace_re_verdict(
        "str.replace_re",
        build,
        "xab",
        "X",
        "xaX",
    ));
}

#[test]
fn replace_re_plus_takes_the_shortest_repetition() {
    // `(re.+ (re.range "0" "9"))` matches "1", "12" and "123" at position 1;
    // the shortest is the one replaced.
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        |ts| {
            let d = re_range(ts, "0", "9");
            app(ts, "re.+", &[d], Sort::RegLan)
        },
        "a123b",
        "N",
        "aN23b",
    ));
}

#[test]
fn replace_re_all_plus_takes_the_shortest_repetition_each_time() {
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| {
            let d = re_range(ts, "0", "9");
            app(ts, "re.+", &[d], Sort::RegLan)
        },
        "a12b34",
        "N",
        "aNNbNN",
    ));
}

// ── first-only vs all, and the no-rescan rule ──

#[test]
fn replace_re_rewrites_only_the_first_occurrence() {
    let build = |ts: &mut TermStore| re_lit(ts, "X");
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        build,
        "aXbXc",
        "Y",
        "aYbXc",
    ));
    // The wrong-answer class this gate exists to catch: claiming replace_re
    // behaves like replace_re_all must be REFUTED, not merely unconfirmed.
    assert_violates(&replace_re_verdict(
        "str.replace_re",
        build,
        "aXbXc",
        "Y",
        "aYbYc",
    ));
}

#[test]
fn replace_re_all_rewrites_every_occurrence() {
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| re_lit(ts, "X"),
        "aXbXc",
        "Y",
        "aYbYc",
    ));
}

#[test]
fn replace_re_all_matches_are_non_overlapping_left_to_right() {
    // "aaa" has an "aa" at 0 and at 1; the recursion continues on the SUFFIX
    // after the first match, so only one replacement fires.
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| re_lit(ts, "aa"),
        "aaa",
        "X",
        "Xa",
    ));
}

#[test]
fn replace_re_all_never_rescans_the_text_it_just_inserted() {
    // The clause recurses on `z`, never on `t ++ z`. Rescanning would not
    // terminate here; it must produce "aab", not diverge or over-replace.
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| re_lit(ts, "a"),
        "ab",
        "aa",
        "aab",
    ));
}

// ── no match, empty subject, and char (not byte) indexing ──

#[test]
fn replace_re_without_a_match_returns_the_subject() {
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        |ts| {
            let x = re_lit(ts, "x");
            let z = re_lit(ts, "z");
            app(ts, "re.union", &[x, z], Sort::RegLan)
        },
        "hello",
        "Q",
        "hello",
    ));
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| {
            let x = re_lit(ts, "x");
            let z = re_lit(ts, "z");
            app(ts, "re.union", &[x, z], Sort::RegLan)
        },
        "hello",
        "Q",
        "hello",
    ));
}

#[test]
fn replace_re_on_the_empty_subject_is_the_identity() {
    // With a non-nullable regex the empty string admits no decomposition.
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        |ts| re_lit(ts, "a"),
        "",
        "X",
        "",
    ));
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| re_lit(ts, "a"),
        "",
        "X",
        "",
    ));
}

#[test]
fn replace_re_splices_at_code_point_boundaries_not_byte_boundaries() {
    // Every character here is multi-byte, so a byte-indexed splice would cut a
    // code point in half or land on the wrong one.
    assert_confirmed(&replace_re_verdict(
        "str.replace_re",
        |ts| re_lit(ts, "\u{3b2}"),
        "\u{3b1}\u{3b2}\u{3b3}",
        "X",
        "\u{3b1}X\u{3b3}",
    ));
    assert_confirmed(&replace_re_verdict(
        "str.replace_re_all",
        |ts| re_range(ts, "\u{3b1}", "\u{3b2}"),
        "\u{3b1}\u{3b2}\u{3b3}",
        "-",
        "--\u{3b3}",
    ));
}

#[test]
fn replace_re_reads_its_subject_from_the_model() {
    // Not ground: the subject is a leaf the model pins, which is the shape the
    // gate actually meets when re-checking a solver model.
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::String);
    let digit = re_range(&mut ts, "0", "9");
    let regex = app(&mut ts, "re.+", &[digit], Sort::RegLan);
    let t = ts.mk_string("#".to_string());
    let call = app(&mut ts, "str.replace_re_all", &[x, regex, t], Sort::String);
    let want = ts.mk_string("a#b#".to_string());
    let eq = app(&mut ts, "=", &[call, want], Sort::Bool);

    let satisfying = StubModel::new().with(x, ModelValue::Str("a1b2".to_string()));
    assert_confirmed(&verdict(&ts, &satisfying, &[eq]));

    let violating = StubModel::new().with(x, ModelValue::Str("a1b".to_string()));
    assert_violates(&verdict(&ts, &violating, &[eq]));

    // An unpinned subject must not be guessed.
    assert_cannot(&verdict(&ts, &StubModel::new(), &[eq]));
}

// ── deliberately fail-closed shapes ──────────────────────────────────────
//
// Each of these returns CannotConfirm. That is a completeness cost only: the
// gate never assumes an assertion it cannot compute, so a refusal can only
// leave a verdict at `unknown`, never publish a wrong `sat`.

#[test]
fn replace_re_fails_closed_on_a_star_regex() {
    // `re.*` accepts the empty word. `str.replace_re`'s clause has no
    // `w != ""` side condition and `str.replace_re_all`'s does, so the two
    // disagree about what the empty match means; the gate declines both.
    for op in ["str.replace_re", "str.replace_re_all"] {
        assert_cannot(&replace_re_verdict(
            op,
            |ts| {
                let a = re_lit(ts, "a");
                app(ts, "re.*", &[a], Sort::RegLan)
            },
            "bbb",
            "X",
            "Xbbb",
        ));
    }
}

#[test]
fn replace_re_fails_closed_on_an_empty_literal_regex() {
    for op in ["str.replace_re", "str.replace_re_all"] {
        assert_cannot(&replace_re_verdict(
            op,
            |ts| re_lit(ts, ""),
            "abc",
            "X",
            "Xabc",
        ));
    }
}

#[test]
fn replace_re_fails_closed_on_re_all_and_re_opt() {
    for op in ["str.replace_re", "str.replace_re_all"] {
        assert_cannot(&replace_re_verdict(
            op,
            |ts| app(ts, "re.all", &[], Sort::RegLan),
            "abc",
            "X",
            "Xabc",
        ));
        assert_cannot(&replace_re_verdict(
            op,
            |ts| {
                let a = re_lit(ts, "a");
                app(ts, "re.opt", &[a], Sort::RegLan)
            },
            "abc",
            "X",
            "Xabc",
        ));
    }
}

#[test]
fn replace_re_detects_nullability_below_the_top_level() {
    // The union is nullable only because one alternative is; the check is a
    // real emptiness probe of the whole regex, not a syntactic top-level test.
    assert_cannot(&replace_re_verdict(
        "str.replace_re",
        |ts| {
            let a = re_lit(ts, "a");
            let eps = re_lit(ts, "");
            app(ts, "re.union", &[a, eps], Sort::RegLan)
        },
        "bab",
        "X",
        "Xbab",
    ));
}

#[test]
fn replace_re_fails_closed_on_an_unsupported_regex_operator() {
    assert_cannot(&replace_re_verdict(
        "str.replace_re",
        |ts| app(ts, "re.future", &[], Sort::RegLan),
        "abc",
        "X",
        "Xbc",
    ));
}

#[test]
fn replace_re_fails_closed_on_a_non_reglan_pattern_argument() {
    let mut ts = TermStore::new();
    let s = ts.mk_string("abc".to_string());
    let pattern = ts.mk_string("a".to_string());
    let t = ts.mk_string("X".to_string());
    let call = app(&mut ts, "str.replace_re", &[s, pattern, t], Sort::String);
    let want = ts.mk_string("Xbc".to_string());
    let eq = app(&mut ts, "=", &[call, want], Sort::Bool);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn replace_re_fails_closed_outside_the_smtlib_alphabet() {
    // U+30000 is above the SMT-LIB Unicode Strings alphabet bound (0x2FFFF).
    // Both the subject and the spliced-in replacement are held to it, so the
    // gate can never confirm a value it would refuse to read back.
    assert_cannot(&replace_re_verdict(
        "str.replace_re",
        |ts| re_lit(ts, "a"),
        "\u{30000}a",
        "X",
        "\u{30000}X",
    ));
    assert_cannot(&replace_re_verdict(
        "str.replace_re",
        |ts| re_lit(ts, "a"),
        "za",
        "\u{30000}",
        "z\u{30000}",
    ));
}

#[test]
fn replace_re_fails_closed_on_wrong_arity() {
    let mut ts = TermStore::new();
    let s = ts.mk_string("abc".to_string());
    let regex = re_lit(&mut ts, "a");
    let call = app(&mut ts, "str.replace_re", &[s, regex], Sort::String);
    let want = ts.mk_string("abc".to_string());
    let eq = app(&mut ts, "=", &[call, want], Sort::Bool);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[eq]));
}
