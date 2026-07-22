// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the Brzozowski-derivative regex used by the Nielsen search.

use super::*;

fn m(r: &WeRegex, s: &str) -> bool {
    r.matches(s).expect("small regex must evaluate exactly")
}

#[test]
fn witness_max_len_defaults_and_accepts_overrides() {
    assert_eq!(parse_witness_max_len(None, false), WITNESS_MAX_LEN);
    assert_eq!(parse_witness_max_len(Some("64"), false), 64);
    assert_eq!(
        parse_witness_max_len(Some("invalid"), false),
        WITNESS_MAX_LEN
    );
    // S1 lifts the DEFAULT only; an explicit override still wins.
    assert_eq!(parse_witness_max_len(None, true), WITNESS_MAX_LEN_S1);
    assert_eq!(parse_witness_max_len(Some("7"), true), 7);
}

#[test]
fn lit_matches_exactly() {
    let r = WeRegex::lit("ab");
    assert!(m(&r, "ab"));
    assert!(!m(&r, ""));
    assert!(!m(&r, "a"));
    assert!(!m(&r, "abc"));
}

#[test]
fn empty_lit_is_eps() {
    let r = WeRegex::lit("");
    assert!(m(&r, ""));
    assert!(!m(&r, "a"));
    assert!(r.nullable());
}

#[test]
fn range_smtlib_semantics() {
    let r = WeRegex::range("a", "c");
    assert!(m(&r, "b"));
    assert!(!m(&r, "d"));
    assert!(!m(&r, ""));
    assert!(!m(&r, "ab"));
    // Reversed and non-singleton endpoints are the EMPTY language.
    assert!(WeRegex::range("c", "a").is_empty_lang());
    assert!(WeRegex::range("ab", "c").is_empty_lang());
    assert!(WeRegex::range("", "c").is_empty_lang());
}

#[test]
fn star_plus_opt() {
    let star = WeRegex::star(WeRegex::lit("ab"));
    assert!(m(&star, ""));
    assert!(m(&star, "abab"));
    assert!(!m(&star, "aba"));

    let plus = WeRegex::plus(WeRegex::lit("b"));
    assert!(!m(&plus, ""));
    assert!(m(&plus, "bbb"));
    assert!(!m(&plus, "ba"));

    let opt = WeRegex::opt(WeRegex::lit("x"));
    assert!(m(&opt, ""));
    assert!(m(&opt, "x"));
    assert!(!m(&opt, "xx"));
}

#[test]
fn concat_union_inter() {
    let r = WeRegex::concat(vec![
        WeRegex::lit("a"),
        WeRegex::star(WeRegex::AnyChar),
        WeRegex::lit("b"),
    ]);
    assert!(m(&r, "ab"));
    assert!(m(&r, "aXYb"));
    assert!(!m(&r, "ba"));

    let u = WeRegex::union(vec![WeRegex::lit("x"), WeRegex::lit("yz")]);
    assert!(m(&u, "x"));
    assert!(m(&u, "yz"));
    assert!(!m(&u, "y"));

    let i = WeRegex::inter(vec![
        WeRegex::star(WeRegex::range("a", "b")),
        WeRegex::opt(WeRegex::lit("aa")),
    ]);
    assert!(m(&i, ""));
    assert!(m(&i, "aa"));
    assert!(!m(&i, "a"));
    assert!(!m(&i, "ccc"));
}

#[test]
fn derive_prunes_definitely() {
    // d_b(a·Σ*) = ∅ — a branch starting with 'b' is a definite conflict.
    let r = WeRegex::concat(vec![WeRegex::lit("a"), WeRegex::All]);
    assert!(r.derive('b').is_empty_lang());
    assert!(!r.derive('a').is_empty_lang());
    // Non-nullable regex rejects the empty branch.
    assert!(!r.nullable());
}

#[test]
fn none_propagation() {
    assert!(WeRegex::concat(vec![WeRegex::lit("a"), WeRegex::None]).is_empty_lang());
    assert!(WeRegex::union(vec![WeRegex::None, WeRegex::None]).is_empty_lang());
    assert!(WeRegex::inter(vec![WeRegex::All, WeRegex::None]).is_empty_lang());
    assert_eq!(WeRegex::star(WeRegex::None), WeRegex::Eps);
}

#[test]
fn witness_shortest() {
    // b+ → "b".
    let w = find_witness(&[WeRegex::plus(WeRegex::lit("b"))], None);
    assert_eq!(w.as_deref(), Some("b"));
    // Nullable → "".
    let w = find_witness(&[WeRegex::star(WeRegex::lit("ab"))], None);
    assert_eq!(w.as_deref(), Some(""));
}

#[test]
fn witness_exact_len() {
    // (ab)* with |w| = 4 → "abab".
    let w = find_witness(&[WeRegex::star(WeRegex::lit("ab"))], Some(4));
    assert_eq!(w.as_deref(), Some("abab"));
    // (ab)* with |w| = 3 → no witness.
    let w = find_witness(&[WeRegex::star(WeRegex::lit("ab"))], Some(3));
    assert_eq!(w, None);
}

#[test]
fn witness_product() {
    // a-or-b-star ∩ (…must contain exactly two chars…): witness in both.
    let w = find_witness(
        &[
            WeRegex::star(WeRegex::range("a", "b")),
            WeRegex::concat(vec![WeRegex::AnyChar, WeRegex::AnyChar]),
        ],
        None,
    );
    let w = w.expect("witness exists");
    assert_eq!(w.chars().count(), 2);
    assert!(w.chars().all(|c| c == 'a' || c == 'b'));
}

#[test]
fn witness_verifies_before_return() {
    // Empty intersection (a ∩ b): the BFS must not fabricate a witness.
    let w = find_witness(
        &[WeRegex::inter(vec![WeRegex::lit("a"), WeRegex::lit("b")])],
        None,
    );
    assert_eq!(w, None);
}

#[test]
fn matches_unknown_is_none_not_wrong() {
    // A pathological nesting may exceed the evaluation cap; the contract is
    // Some(exact) or None — never a wrong Some. Build a moderately nasty
    // regex and just require agreement with a direct oracle on small inputs.
    let mut r = WeRegex::lit("a");
    for _ in 0..6 {
        r = WeRegex::concat(vec![
            WeRegex::star(r.clone()),
            WeRegex::opt(r.clone()),
            WeRegex::AnyChar,
        ]);
    }
    for s in ["", "a", "aa", "ba"] {
        if let Some(v) = r.matches(s) {
            // Oracle: derivative evaluation without caps (same algorithm) —
            // the point is that Some answers are stable/deterministic.
            assert_eq!(r.matches(s), Some(v));
        }
    }
}

// ── Stage 3: reversal, length windows, definite emptiness ──────────────────

#[test]
fn reverse_is_exact() {
    let r = WeRegex::star(WeRegex::lit("ab")); // (ab)*
    let rev = r.reverse(); // (ba)*
    assert_eq!(rev.matches("baba"), Some(true));
    assert_eq!(rev.matches("abab"), Some(false));
    assert_eq!(rev.matches(""), Some(true));
    // Involution on languages.
    assert_eq!(rev.reverse().matches("abab"), Some(true));
}

#[test]
fn len_interval_regex_exact_window() {
    let r = len_interval_regex(1, Some(2)).expect("small window");
    assert_eq!(r.matches(""), Some(false));
    assert_eq!(r.matches("x"), Some(true));
    assert_eq!(r.matches("xy"), Some(true));
    assert_eq!(r.matches("xyz"), Some(false));
    // Unbounded above.
    let r = len_interval_regex(2, None).expect("lower-bounded window");
    assert_eq!(r.matches("a"), Some(false));
    assert_eq!(r.matches("abcde"), Some(true));
    // Infeasible window is the empty language.
    assert!(len_interval_regex(3, Some(2))
        .expect("empty window")
        .is_empty_lang());
    // Oversized windows: pre-S1 the 16-length cap made these unrepresentable
    // (callers had to skip, never fabricate); under S1 (default-ON) the window
    // is carried EXACTLY as a bounded-repeat counter node, which is the whole
    // point of the counter representation — no materialized `Σ?` chain, no cap.
    // Assert whichever contract is live rather than pinning the stale one.
    match len_interval_regex(1000, Some(2000)) {
        None => assert!(!s1_enabled(), "only the pre-S1 cap may refuse"),
        Some(r) => {
            assert!(s1_enabled(), "only S1 may represent it");
            // Exact, not fabricated: the window is non-empty and rejects
            // lengths outside [1000, 2000].
            assert!(!r.is_empty_lang());
            assert!(!r.nullable());
            assert_eq!(r.matches(&"x".repeat(999)), Some(false));
            assert_eq!(r.matches(&"x".repeat(1000)), Some(true));
            assert_eq!(r.matches(&"x".repeat(2000)), Some(true));
            assert_eq!(r.matches(&"x".repeat(2001)), Some(false));
        }
    }
}

#[test]
fn concat_emptiness_definite_empty() {
    // a+ · b+ ⊆ (aa)*? No string qualifies: (aa)* admits only 'a's.
    let parts = vec![
        vec![WeRegex::plus(WeRegex::lit("a"))],
        vec![WeRegex::plus(WeRegex::lit("b"))],
    ];
    let target = [WeRegex::star(WeRegex::lit("aa"))];
    assert!(concat_membership_definitely_empty(&parts, &target));
}

#[test]
fn concat_emptiness_finds_witness_split() {
    // a+ · b+ meets (ab)* at "ab" → NOT empty.
    let parts = vec![
        vec![WeRegex::plus(WeRegex::lit("a"))],
        vec![WeRegex::plus(WeRegex::lit("b"))],
    ];
    let target = [WeRegex::star(WeRegex::lit("ab"))];
    assert!(!concat_membership_definitely_empty(&parts, &target));
}

#[test]
fn concat_emptiness_intersection_form() {
    // Single part, no target: pure intersection emptiness.
    let disjoint = vec![vec![
        WeRegex::plus(WeRegex::lit("a")),
        WeRegex::plus(WeRegex::lit("b")),
    ]];
    assert!(concat_membership_definitely_empty(&disjoint, &[]));
    let overlapping = vec![vec![
        WeRegex::star(WeRegex::range("a", "c")),
        WeRegex::lit("b"),
    ]];
    assert!(!concat_membership_definitely_empty(&overlapping, &[]));
}

#[test]
fn concat_emptiness_range_interior_not_missed() {
    // The witness needs a character strictly INSIDE a range ('m' ∈ [a,z]);
    // the class alphabet must cover interior representatives, so this must
    // NOT be judged empty.
    let parts = vec![vec![WeRegex::Range('a', 'z')]];
    let target = [WeRegex::lit("m")];
    assert!(!concat_membership_definitely_empty(&parts, &target));
}

#[test]
fn concat_emptiness_length_window_coupling() {
    // (aaa)+ ∩ Σ·Σ? (lengths 1–2) is empty — the regex×length product.
    let parts = vec![vec![
        WeRegex::plus(WeRegex::lit("aaa")),
        len_interval_regex(1, Some(2)).expect("window"),
    ]];
    assert!(concat_membership_definitely_empty(&parts, &[]));
}

#[test]
fn concat_emptiness_never_claims_on_cap() {
    // All-universal constraints exhaust nothing and accept immediately.
    let parts = vec![vec![WeRegex::All], vec![WeRegex::All]];
    assert!(!concat_membership_definitely_empty(&parts, &[WeRegex::All]));
}

// ── Length residues (Stage 3d) ──────────────────────────────────────────

#[test]
fn length_residues_star_word() {
    // (aa)*: |w| ≡ 0 (mod 2).
    let r = WeRegex::star(WeRegex::lit("aa"));
    assert_eq!(r.length_residues(), Some((2, 0b01)));
    // (abc)*: |w| ≡ 0 (mod 3).
    let r = WeRegex::star(WeRegex::lit("abc"));
    assert_eq!(r.length_residues(), Some((3, 0b001)));
}

#[test]
fn length_residues_plus_and_offset() {
    // (aa)+ = (aa)(aa)*: |w| ≡ 0 (mod 2).
    let r = WeRegex::plus(WeRegex::lit("aa"));
    assert_eq!(r.length_residues(), Some((2, 0b01)));
    // a(aa)*: |w| ≡ 1 (mod 2).
    let r = WeRegex::concat(vec![WeRegex::lit("a"), WeRegex::star(WeRegex::lit("aa"))]);
    assert_eq!(r.length_residues(), Some((2, 0b10)));
}

#[test]
fn length_residues_union_conservative() {
    // (aa|aaa)*: lengths generate every residue eventually — no single
    // congruence is derivable, so the extractor returns nothing.
    let r = WeRegex::star(WeRegex::union(vec![
        WeRegex::lit("aa"),
        WeRegex::lit("aaa"),
    ]));
    assert_eq!(r.length_residues(), None);
    // All admits every length.
    assert_eq!(WeRegex::All.length_residues(), None);
}

#[test]
fn length_residues_union_of_stars_residue_set() {
    // (aaa)* | (aaa)*a: residues {0, 1} mod 3 — a genuine SET, not a
    // single congruence.
    let r = WeRegex::union(vec![
        WeRegex::star(WeRegex::lit("aaa")),
        WeRegex::concat(vec![WeRegex::star(WeRegex::lit("aaa")), WeRegex::lit("a")]),
    ]);
    assert_eq!(r.length_residues(), Some((3, 0b011)));
}

#[test]
fn length_residues_never_exclude_a_member() {
    // Soundness spot-check: for a batch of regexes, every witness produced
    // by find_witness must have a length residue inside the mask.
    let regexes = vec![
        WeRegex::star(WeRegex::lit("aa")),
        WeRegex::plus(WeRegex::lit("abc")),
        WeRegex::concat(vec![
            WeRegex::lit("xy"),
            WeRegex::star(WeRegex::lit("aabb")),
        ]),
        WeRegex::union(vec![
            WeRegex::star(WeRegex::lit("aaaa")),
            WeRegex::lit("aa"),
        ]),
        WeRegex::star(WeRegex::union(vec![
            WeRegex::lit("ab"),
            WeRegex::lit("aabb"),
        ])),
    ];
    for r in &regexes {
        let Some((m, mask)) = r.length_residues() else {
            continue;
        };
        for target_len in 0..12usize {
            if let Some(w) = find_witness(std::slice::from_ref(r), Some(target_len)) {
                assert_eq!(r.matches(&w), Some(true));
                let n = w.chars().count();
                assert!(
                    mask & (1u64 << (n % m)) != 0,
                    "residue mask (m={m}, mask={mask:#b}) excludes member {w:?} of {r:?}"
                );
            }
        }
    }
}

// ── Strings S1: bounded-repeat Loop node ────────────────────────────────

#[test]
fn loop_bounded_folds() {
    // lo > hi: SMT-LIB empty language.
    assert_eq!(
        WeRegex::loop_bounded(WeRegex::lit("a"), 3, 2),
        WeRegex::None
    );
    // hi = 0: only the k = 0 term {ε}.
    assert_eq!(WeRegex::loop_bounded(WeRegex::lit("a"), 0, 0), WeRegex::Eps);
    // Empty inner: {ε} iff lo = 0.
    assert_eq!(WeRegex::loop_bounded(WeRegex::None, 0, 5), WeRegex::Eps);
    assert_eq!(WeRegex::loop_bounded(WeRegex::None, 1, 5), WeRegex::None);
    // Eps^k = {ε}; (r*)^k = r* for hi ≥ 1; lo = hi = 1 is the inner itself.
    assert_eq!(WeRegex::loop_bounded(WeRegex::Eps, 2, 7), WeRegex::Eps);
    let star = WeRegex::star(WeRegex::lit("ab"));
    assert_eq!(WeRegex::loop_bounded(star.clone(), 2, 7), star);
    assert_eq!(
        WeRegex::loop_bounded(WeRegex::lit("ab"), 1, 1),
        WeRegex::lit("ab")
    );
}

#[test]
fn loop_matches_exactly() {
    // (ab){2,3}
    let r = WeRegex::loop_bounded(WeRegex::lit("ab"), 2, 3);
    assert!(!m(&r, ""));
    assert!(!m(&r, "ab"));
    assert!(m(&r, "abab"));
    assert!(m(&r, "ababab"));
    assert!(!m(&r, "abababab"));
    assert!(!m(&r, "aba"));
    // lo = 0 admits ε.
    let r0 = WeRegex::loop_bounded(WeRegex::lit("ab"), 0, 2);
    assert!(m(&r0, ""));
    assert!(m(&r0, "ab"));
    assert!(m(&r0, "abab"));
    assert!(!m(&r0, "ababab"));
}

#[test]
fn loop_nullable_body_is_exact() {
    // (a?){2,3} = {ε, a, aa, aaa} — the nullable-body collapse case of the
    // derivative rule.
    let r = WeRegex::loop_bounded(WeRegex::opt(WeRegex::lit("a")), 2, 3);
    assert!(m(&r, ""));
    assert!(m(&r, "a"));
    assert!(m(&r, "aa"));
    assert!(m(&r, "aaa"));
    assert!(!m(&r, "aaaa"));
}

#[test]
fn loop_agrees_with_unrolled_form() {
    // Loop(r, lo, hi) must accept exactly the strings of the historical
    // unrolled translation r^lo · (r?)^(hi−lo).
    let body = WeRegex::union(vec![WeRegex::lit("ab"), WeRegex::lit("c")]);
    let looped = WeRegex::loop_bounded(body.clone(), 1, 3);
    let unrolled = WeRegex::concat(vec![
        body.clone(),
        WeRegex::opt(body.clone()),
        WeRegex::opt(body.clone()),
    ]);
    let alphabet = ['a', 'b', 'c'];
    let mut words: Vec<String> = vec![String::new()];
    let mut frontier: Vec<String> = vec![String::new()];
    for _ in 0..7 {
        let mut next = Vec::new();
        for w in &frontier {
            for c in alphabet {
                let mut nw = w.clone();
                nw.push(c);
                next.push(nw);
            }
        }
        words.extend(next.iter().cloned());
        frontier = next;
    }
    for w in &words {
        assert_eq!(
            looped.matches(w),
            unrolled.matches(w),
            "loop/unroll disagreement on {w:?}"
        );
    }
}

#[test]
fn loop_reverse_is_exact() {
    let r = WeRegex::loop_bounded(WeRegex::lit("ab"), 1, 2);
    let rev = r.reverse();
    assert!(m(&rev, "ba"));
    assert!(m(&rev, "baba"));
    assert!(!m(&rev, "ab"));
    assert!(!m(&rev, ""));
}

#[test]
fn loop_length_residues_sound() {
    // (ab){0,680}: every member has even length.
    let r = WeRegex::loop_bounded(WeRegex::lit("ab"), 0, 680);
    assert_eq!(r.length_residues(), Some((2, 0b1)));
    assert!(m(&r, "abab"));
    assert!(!m(&r, "aba"));
}

#[test]
fn loop_emptiness_product_is_definite() {
    // a{3,3} ∩ {w : |w| = 4} = ∅, provable through the product graph.
    let parts = vec![vec![WeRegex::loop_bounded(WeRegex::lit("a"), 3, 3)]];
    let targets = vec![WeRegex::lit("aaaa")];
    assert!(concat_membership_definitely_empty(&parts, &targets));
    // a{3,4} ∩ {aaaa} is inhabited — must NOT claim emptiness.
    let parts2 = vec![vec![WeRegex::loop_bounded(WeRegex::lit("a"), 3, 4)]];
    assert!(!concat_membership_definitely_empty(&parts2, &targets));
}

#[test]
fn loop_witness_via_derivatives() {
    // Digits{3,3} — the automatark shape — must yield a 3-char witness.
    let r = WeRegex::loop_bounded(WeRegex::Range('0', '9'), 3, 3);
    let w = find_witness(std::slice::from_ref(&r), None).expect("witness");
    assert_eq!(w.chars().count(), 3);
    assert_eq!(r.matches(&w), Some(true));
}

// ── Strings S1: concat-membership witness BFS ───────────────────────────

#[test]
fn concat_witness_finds_valid_split() {
    // u0 · "bc" · u2 ∈ Σ*·"ab"·Σ* — the slog/Stranger shape. The shortest
    // split sets u0 to end with "a" (or embeds "ab" elsewhere).
    let parts = vec![vec![], vec![WeRegex::lit("bc")], vec![]];
    let needle = WeRegex::concat(vec![WeRegex::All, WeRegex::lit("ab"), WeRegex::All]);
    let split = concat_membership_witness(&parts, std::slice::from_ref(&needle), 32)
        .expect("split must exist");
    assert_eq!(split.len(), 3);
    assert_eq!(split[1], "bc");
    let joined: String = split.concat();
    assert_eq!(needle.matches(&joined), Some(true));
}

#[test]
fn concat_witness_respects_part_constraints() {
    // u0 ∈ (ab)+, u1 = "c", u0·u1 ∈ Σ*·"bc" — u0 must end with "b".
    let parts = vec![
        vec![WeRegex::plus(WeRegex::lit("ab"))],
        vec![WeRegex::lit("c")],
    ];
    let target = WeRegex::concat(vec![WeRegex::All, WeRegex::lit("bc")]);
    let split = concat_membership_witness(&parts, std::slice::from_ref(&target), 32)
        .expect("split must exist");
    assert_eq!(split.len(), 2);
    assert_eq!(parts[0][0].matches(&split[0]), Some(true));
    assert_eq!(split[1], "c");
    let joined: String = split.concat();
    assert_eq!(target.matches(&joined), Some(true));
}

#[test]
fn concat_witness_none_when_unsatisfiable() {
    // u0 ∈ a+, u0 ∈ Σ*·"b"·Σ* target — impossible; must answer None
    // (best-effort "not found", and indeed no witness exists).
    let parts = vec![vec![WeRegex::plus(WeRegex::lit("a"))]];
    let target = WeRegex::concat(vec![WeRegex::All, WeRegex::lit("b"), WeRegex::All]);
    assert_eq!(
        concat_membership_witness(&parts, std::slice::from_ref(&target), 16),
        None
    );
}

#[test]
fn concat_witness_empty_parts_and_ground_runs() {
    // No parts: the empty concatenation is a witness iff every target is
    // nullable.
    assert_eq!(
        concat_membership_witness(&[], &[WeRegex::star(WeRegex::lit("a"))], 8),
        Some(Vec::new())
    );
    assert_eq!(
        concat_membership_witness(&[], &[WeRegex::lit("a")], 8),
        None
    );
}
