// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the regex intersection-emptiness certificate.
//!
//! The negative half is the point: every structural way a certificate can be
//! wrong — a MISSING reachable state, a NON-EXHAUSTIVE alphabet partition, a
//! listed state that IS accepting, and a genuinely NON-empty intersection —
//! must be REJECTED by [`validate_certificate`].

use super::*;
use ay_core::{Sort, Symbol, TermStore};

// ---------------------------------------------------------------------------
// Term-building helpers
// ---------------------------------------------------------------------------

fn re_app(terms: &mut TermStore, name: &str, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::RegLan)
}

fn to_re(terms: &mut TermStore, s: &str) -> TermId {
    let c = terms.mk_string(s.to_string());
    re_app(terms, "str.to_re", vec![c])
}

fn range(terms: &mut TermStore, lo: &str, hi: &str) -> TermId {
    let l = terms.mk_string(lo.to_string());
    let h = terms.mk_string(hi.to_string());
    re_app(terms, "re.range", vec![l, h])
}

fn star(terms: &mut TermStore, r: TermId) -> TermId {
    re_app(terms, "re.*", vec![r])
}

fn concat(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    re_app(terms, "re.++", args)
}

fn union(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    re_app(terms, "re.union", args)
}

fn comp(terms: &mut TermStore, r: TermId) -> TermId {
    re_app(terms, "re.comp", vec![r])
}

fn in_re(terms: &mut TermStore, x: TermId, r: TermId) -> TermId {
    terms.mk_app(Symbol::named("str.in_re"), [x, r], Sort::Bool)
}

/// The clause literal that DENIES `x ∈ r` (i.e. asserts the hypothesis
/// `x ∈ r` when the literal is false).
fn deny_in(terms: &mut TermStore, x: TermId, r: TermId) -> TermId {
    let m = in_re(terms, x, r);
    terms.mk_not(m)
}

/// The clause literal that DENIES `x ∉ r`.
fn deny_not_in(terms: &mut TermStore, x: TermId, r: TermId) -> TermId {
    in_re(terms, x, r)
}

fn str_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::String)
}

// ---------------------------------------------------------------------------
// Certificate plumbing for the negative tests
// ---------------------------------------------------------------------------

/// Translate a set of `(regex, positive)` constraints and install the alphabet
/// partition, exactly as `group_intersection_is_empty` does.
fn prepare(terms: &TermStore, specs: &[(TermId, bool)]) -> Option<(Arena, Vec<ReId>)> {
    let mut tr = Translator::new(terms);
    let mut constraints = Vec::new();
    for &(r, positive) in specs {
        let id = tr.translate(r)?;
        let id = if positive { id } else { tr.arena.mk_not(id) };
        constraints.push(id);
    }
    if tr.arena.poisoned {
        return None;
    }
    let mut arena = tr.arena;
    let blocks = compute_blocks(&arena, &constraints)?;
    arena.block_starts = blocks.iter().map(|&(lo, _)| lo).collect();
    arena.blocks = blocks;
    Some((arena, constraints))
}

// ---------------------------------------------------------------------------
// Positive tests
// ---------------------------------------------------------------------------

#[test]
fn disjoint_literals_intersect_empty_and_validate() {
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let r1 = to_re(&mut terms, "abc");
    let r2 = to_re(&mut terms, "xyz");
    let l1 = deny_in(&mut terms, x, r1);
    let l2 = deny_in(&mut terms, x, r2);
    assert!(
        recognize_regex_intersect_empty(&terms, &[l1, l2]),
        "`x ∈ \"abc\" ∧ x ∈ \"xyz\"` is unsatisfiable — the clause is a tautology"
    );
}

#[test]
fn automatark_shape_prefix_vs_constant_is_empty() {
    // The real corpus shape: `x ∈ "/f" · (¬"\n")* · ".d"` and `x ∈ "other"`.
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let nl = to_re(&mut terms, "\n");
    let not_nl = comp(&mut terms, nl);
    let mid = star(&mut terms, not_nl);
    let pre = to_re(&mut terms, "/f");
    let post = to_re(&mut terms, ".d");
    let r1 = concat(&mut terms, vec![pre, mid, post]);
    let r2 = to_re(&mut terms, "other");
    let l1 = deny_in(&mut terms, x, r1);
    let l2 = deny_in(&mut terms, x, r2);
    assert!(recognize_regex_intersect_empty(&terms, &[l1, l2]));
}

#[test]
fn membership_and_its_own_complement_is_empty() {
    // `x ∈ [0-9]* ∧ x ∉ [0-9]*` — the complement lane.
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let d = range(&mut terms, "0", "9");
    let r = star(&mut terms, d);
    let l1 = deny_in(&mut terms, x, r);
    let l2 = deny_not_in(&mut terms, x, r);
    assert!(recognize_regex_intersect_empty(&terms, &[l1, l2]));
}

#[test]
fn digits_and_letters_of_same_length_is_empty() {
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let d = range(&mut terms, "0", "9");
    let a = range(&mut terms, "a", "z");
    let r1 = concat(&mut terms, vec![d, d, d]);
    let r2 = concat(&mut terms, vec![a, a, a]);
    let l1 = deny_in(&mut terms, x, r1);
    let l2 = deny_in(&mut terms, x, r2);
    assert!(recognize_regex_intersect_empty(&terms, &[l1, l2]));
}

#[test]
fn extra_unrelated_clause_literals_do_not_block_recognition() {
    // A tautologous SUBSET makes the whole clause a tautology.
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let y = str_var(&mut terms, "Y");
    let r1 = to_re(&mut terms, "a");
    let r2 = to_re(&mut terms, "b");
    let other = to_re(&mut terms, "c");
    let l1 = deny_in(&mut terms, x, r1);
    let l2 = deny_in(&mut terms, x, r2);
    let l3 = deny_in(&mut terms, y, other);
    assert!(recognize_regex_intersect_empty(&terms, &[l3, l1, l2]));
}

#[test]
fn single_literal_over_empty_language_is_a_tautology() {
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let none = re_app(&mut terms, "re.none", vec![]);
    let l = deny_in(&mut terms, x, none);
    assert!(recognize_regex_intersect_empty(&terms, &[l]));
}

#[test]
fn strict_validation_accepts_a_genuine_lemma() {
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let r1 = to_re(&mut terms, "abc");
    let r2 = to_re(&mut terms, "abd");
    let l1 = deny_in(&mut terms, x, r1);
    let l2 = deny_in(&mut terms, x, r2);
    assert!(validate_regex_intersect_empty(&terms, ProofId(0), &[l1, l2]).is_ok());
}

// ---------------------------------------------------------------------------
// Negative tests — the four ways a certificate can lie
// ---------------------------------------------------------------------------

/// Build the constraints and a VALID certificate for a genuinely empty
/// intersection, used as the base for each mutation below.
fn empty_case() -> (TermStore, Arena, Vec<ReId>, EmptinessCertificate) {
    // `x ∈ [0-9][0-9][0-9] ∧ x ∈ [0-9][0-9]` — empty (lengths disagree), and
    // deliberately NOT empty at the first character: the product graph really
    // walks through several live states before dying, so a dropped or
    // mislabelled state has something to hide.
    let mut terms = TermStore::new();
    let d = range(&mut terms, "0", "9");
    let r1 = concat(&mut terms, vec![d, d, d]);
    let r2 = concat(&mut terms, vec![d, d]);
    let (mut arena, constraints) = prepare(&terms, &[(r1, true), (r2, true)]).expect("prepared");
    let cert = build_certificate(&mut arena, &constraints).expect("empty intersection");
    assert!(
        cert.states.len() >= 3,
        "base case must have several reachable states, got {}",
        cert.states.len()
    );
    assert!(
        validate_certificate(&mut arena, &constraints, &cert),
        "the unmutated certificate must validate"
    );
    (terms, arena, constraints, cert)
}

#[test]
fn negative_missing_reachable_state_is_rejected() {
    let (_terms, mut arena, constraints, mut cert) = empty_case();
    assert!(
        cert.states.len() > 1,
        "the base case must have a successor state to drop"
    );
    // Drop the LAST state and repoint every transition that targeted it at
    // state 0. Closure is now broken: a live transition's real successor is no
    // longer the listed one.
    let dropped = cert.states.len() - 1;
    cert.states.truncate(dropped);
    cert.transitions.truncate(dropped);
    for row in &mut cert.transitions {
        for t in row.iter_mut() {
            if matches!(*t, Target::State(j) if j >= dropped) {
                *t = Target::State(0);
            }
        }
    }
    assert!(
        !validate_certificate(&mut arena, &constraints, &cert),
        "a certificate missing a reachable state must be REJECTED"
    );
}

#[test]
fn negative_missing_state_reported_as_dead_is_rejected() {
    // The other way to hide a state: claim its incoming transition is dead.
    let (_terms, mut arena, constraints, mut cert) = empty_case();
    let mut patched = false;
    for row in &mut cert.transitions {
        for t in row.iter_mut() {
            if matches!(*t, Target::State(j) if j != 0) {
                *t = Target::Dead;
                patched = true;
            }
        }
    }
    assert!(patched, "the base case must have a live transition to hide");
    assert!(
        !validate_certificate(&mut arena, &constraints, &cert),
        "a live transition re-labelled dead must be REJECTED"
    );
}

#[test]
fn negative_non_exhaustive_alphabet_partition_is_rejected() {
    let (_terms, mut arena, constraints, cert) = empty_case();

    // (a) Drop the last block: the partition no longer reaches the top of the
    //     SMT-LIB code-point range, so characters above it are unexamined.
    let mut truncated = EmptinessCertificate {
        blocks: cert.blocks.clone(),
        states: cert.states.clone(),
        transitions: cert.transitions.clone(),
    };
    truncated.blocks.pop();
    for row in &mut truncated.transitions {
        row.pop();
    }
    arena.blocks = truncated.blocks.clone();
    arena.block_starts = truncated.blocks.iter().map(|&(lo, _)| lo).collect();
    arena.deriv.clear();
    assert!(
        !validate_certificate(&mut arena, &constraints, &truncated),
        "a partition that stops below the top of the alphabet must be REJECTED"
    );

    // (b) Punch a HOLE in the middle: blocks stay ordered and still end at the
    //     top, but one interior code-point run is covered by nothing.
    let (_t2, mut arena2, constraints2, cert2) = empty_case();
    let mut holed = EmptinessCertificate {
        blocks: cert2.blocks.clone(),
        states: cert2.states.clone(),
        transitions: cert2.transitions.clone(),
    };
    assert!(holed.blocks.len() >= 3, "need an interior block to remove");
    holed.blocks.remove(1);
    for row in &mut holed.transitions {
        row.remove(1);
    }
    arena2.blocks = holed.blocks.clone();
    arena2.block_starts = holed.blocks.iter().map(|&(lo, _)| lo).collect();
    arena2.deriv.clear();
    assert!(
        !validate_certificate(&mut arena2, &constraints2, &holed),
        "a partition with an interior gap must be REJECTED"
    );

    // (c) Coarsen the partition so a block STRADDLES a character-class
    //     boundary: it still tiles the range, but one representative no longer
    //     speaks for its whole block.
    let (_t3, mut arena3, constraints3, cert3) = empty_case();
    let mut coarse = EmptinessCertificate {
        blocks: cert3.blocks.clone(),
        states: cert3.states.clone(),
        transitions: cert3.transitions.clone(),
    };
    assert!(coarse.blocks.len() >= 2);
    let merged = (coarse.blocks[0].0, coarse.blocks[1].1);
    coarse.blocks.remove(1);
    coarse.blocks[0] = merged;
    for row in &mut coarse.transitions {
        row.remove(1);
    }
    arena3.blocks = coarse.blocks.clone();
    arena3.block_starts = coarse.blocks.iter().map(|&(lo, _)| lo).collect();
    arena3.deriv.clear();
    assert!(
        !validate_certificate(&mut arena3, &constraints3, &coarse),
        "a block straddling a character-class boundary must be REJECTED"
    );
}

#[test]
fn negative_listed_state_that_is_accepting_is_rejected() {
    // `x ∈ [0-9][0-9]` alone is satisfiable; its product graph reaches an
    // accepting state. Hand-build a "certificate" that lists the reachable
    // states anyway and claim emptiness — validation must refuse it because a
    // listed state accepts the empty word.
    let mut terms = TermStore::new();
    let d = range(&mut terms, "0", "9");
    let r = concat(&mut terms, vec![d, d]);
    let (mut arena, constraints) = prepare(&terms, &[(r, true)]).expect("prepared");

    // Reachability closure done by hand (build_certificate refuses to return
    // one for a non-empty language, which is itself the point).
    let nb = arena.blocks.len();
    let mut states: Vec<Vec<ReId>> = vec![constraints.clone()];
    let mut transitions: Vec<Vec<Target>> = Vec::new();
    let mut q = 0;
    while q < states.len() {
        let st = states[q].clone();
        let mut row = Vec::with_capacity(nb);
        for blk in 0..nb {
            let next: Vec<ReId> = st.iter().map(|&x| arena.derive(x, blk as u32)).collect();
            if next.contains(&arena.nil) {
                row.push(Target::Dead);
                continue;
            }
            let id = states.iter().position(|s| *s == next).unwrap_or_else(|| {
                states.push(next.clone());
                states.len() - 1
            });
            row.push(Target::State(id));
        }
        transitions.push(row);
        q += 1;
    }
    let cert = EmptinessCertificate {
        blocks: arena.blocks.clone(),
        states,
        transitions,
    };
    assert!(
        cert.states
            .iter()
            .any(|s| s.iter().all(|&r| arena.is_nullable(r))),
        "the hand-built closure must contain an accepting state"
    );
    assert!(
        !validate_certificate(&mut arena, &constraints, &cert),
        "a certificate listing an ACCEPTING state must be REJECTED"
    );
}

#[test]
fn negative_non_empty_intersection_is_rejected() {
    // `x ∈ [0-9][0-9] ∧ x ∈ [0-9]*` shares "00" — nothing may certify.
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let d = range(&mut terms, "0", "9");
    let r1 = concat(&mut terms, vec![d, d]);
    let r2 = star(&mut terms, d);
    let l1 = deny_in(&mut terms, x, r1);
    let l2 = deny_in(&mut terms, x, r2);
    assert!(
        !recognize_regex_intersect_empty(&terms, &[l1, l2]),
        "a NON-empty intersection must never be recognized"
    );
    assert!(validate_regex_intersect_empty(&terms, ProofId(0), &[l1, l2]).is_err());

    let (mut arena, constraints) = prepare(&terms, &[(r1, true), (r2, true)]).expect("prepared");
    assert!(
        build_certificate(&mut arena, &constraints).is_none(),
        "the search must refuse to produce a certificate for a non-empty language"
    );
}

#[test]
fn negative_start_state_swapped_is_rejected() {
    // Point the certificate at a DIFFERENT start state (its own successor):
    // the argument would then prove emptiness of the wrong language.
    let (_terms, mut arena, constraints, mut cert) = empty_case();
    assert!(cert.states.len() > 1);
    cert.states.swap(0, 1);
    assert!(
        !validate_certificate(&mut arena, &constraints, &cert),
        "a certificate whose start state is not the constraint vector must be REJECTED"
    );
}

#[test]
fn negative_duplicate_states_are_rejected() {
    let (_terms, mut arena, constraints, mut cert) = empty_case();
    let dup = cert.states[0].clone();
    cert.states.push(dup);
    cert.transitions.push(cert.transitions[0].clone());
    assert!(
        !validate_certificate(&mut arena, &constraints, &cert),
        "duplicate listed states must be REJECTED"
    );
}

#[test]
fn negative_truncated_transition_row_is_rejected() {
    let (_terms, mut arena, constraints, mut cert) = empty_case();
    cert.transitions[0].pop();
    assert!(
        !validate_certificate(&mut arena, &constraints, &cert),
        "a state without a transition for every block must be REJECTED"
    );
}

// ---------------------------------------------------------------------------
// Fail-closed on the clause shape
// ---------------------------------------------------------------------------

#[test]
fn non_ground_regex_is_rejected() {
    // A regex whose leaf is a string VARIABLE has no fixed language here.
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let v = str_var(&mut terms, "V");
    let r1 = re_app(&mut terms, "str.to_re", vec![v]);
    let r2 = to_re(&mut terms, "abc");
    let l1 = deny_in(&mut terms, x, r1);
    let l2 = deny_in(&mut terms, x, r2);
    assert!(!recognize_regex_intersect_empty(&terms, &[l1, l2]));
}

#[test]
fn different_subjects_do_not_combine() {
    // `x ∈ "a"` and `y ∈ "b"` are jointly satisfiable — the group must be keyed
    // by subject, never merged across terms.
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let y = str_var(&mut terms, "Y");
    let r1 = to_re(&mut terms, "a");
    let r2 = to_re(&mut terms, "b");
    let l1 = deny_in(&mut terms, x, r1);
    let l2 = deny_in(&mut terms, y, r2);
    assert!(!recognize_regex_intersect_empty(&terms, &[l1, l2]));
}

#[test]
fn empty_clause_and_non_bool_literals_are_rejected() {
    let mut terms = TermStore::new();
    assert!(!recognize_regex_intersect_empty(&terms, &[]));
    assert!(validate_regex_intersect_empty(&terms, ProofId(0), &[]).is_err());
    let s = str_var(&mut terms, "S");
    assert!(!recognize_regex_intersect_empty(&terms, &[s]));
    assert!(validate_regex_intersect_empty(&terms, ProofId(0), &[s]).is_err());
}

#[test]
fn unknown_regex_operator_fails_closed() {
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let c = terms.mk_string("a".to_string());
    let r1 = re_app(&mut terms, "re.not_a_real_operator", vec![c]);
    let none = re_app(&mut terms, "re.none", vec![]);
    let l1 = deny_in(&mut terms, x, r1);
    let l2 = deny_in(&mut terms, x, none);
    // The `re.none` literal alone still certifies — the unknown operator just
    // cannot contribute. Check the unknown operator on its OWN group.
    assert!(recognize_regex_intersect_empty(&terms, &[l1, l2]));
    let y = str_var(&mut terms, "Y");
    let l3 = deny_in(&mut terms, y, r1);
    assert!(!recognize_regex_intersect_empty(&terms, &[l3]));
}

// ---------------------------------------------------------------------------
// Semantics spot checks (the checker must be right, not merely conservative)
// ---------------------------------------------------------------------------

#[test]
fn complement_covers_characters_outside_the_mentioned_alphabet() {
    // `x ∈ ¬("a"*)` is satisfiable — by "b", or by any code point at all that
    // the regexes never mention. A checker whose alphabet stopped at the
    // mentioned characters would wrongly call this empty.
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let a = to_re(&mut terms, "a");
    let sa = star(&mut terms, a);
    let nsa = comp(&mut terms, sa);
    let l = deny_in(&mut terms, x, nsa);
    assert!(!recognize_regex_intersect_empty(&terms, &[l]));
}

#[test]
fn complement_of_all_strings_is_empty() {
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let all = re_app(&mut terms, "re.all", vec![]);
    let nall = comp(&mut terms, all);
    let l = deny_in(&mut terms, x, nall);
    assert!(recognize_regex_intersect_empty(&terms, &[l]));
}

#[test]
fn bounded_loop_lengths_that_cannot_agree_are_empty() {
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let d = range(&mut terms, "0", "9");
    let l2 = terms.mk_app(
        Symbol::Indexed("re.loop".to_string(), vec![2, 2]),
        [d],
        Sort::RegLan,
    );
    let l3 = terms.mk_app(
        Symbol::Indexed("re.loop".to_string(), vec![3, 3]),
        [d],
        Sort::RegLan,
    );
    let a = deny_in(&mut terms, x, l2);
    let b = deny_in(&mut terms, x, l3);
    assert!(recognize_regex_intersect_empty(&terms, &[a, b]));
}

#[test]
fn bounded_loop_ranges_that_overlap_are_not_empty() {
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let d = range(&mut terms, "0", "9");
    let l23 = terms.mk_app(
        Symbol::Indexed("re.loop".to_string(), vec![2, 3]),
        [d],
        Sort::RegLan,
    );
    let l34 = terms.mk_app(
        Symbol::Indexed("re.loop".to_string(), vec![3, 4]),
        [d],
        Sort::RegLan,
    );
    let a = deny_in(&mut terms, x, l23);
    let b = deny_in(&mut terms, x, l34);
    assert!(!recognize_regex_intersect_empty(&terms, &[a, b]));
}

#[test]
fn union_overlap_keeps_the_intersection_non_empty() {
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let a = to_re(&mut terms, "a");
    let b = to_re(&mut terms, "b");
    let c = to_re(&mut terms, "c");
    let ab = union(&mut terms, vec![a, b]);
    let bc = union(&mut terms, vec![b, c]);
    let l1 = deny_in(&mut terms, x, ab);
    let l2 = deny_in(&mut terms, x, bc);
    assert!(!recognize_regex_intersect_empty(&terms, &[l1, l2]));
}

#[test]
fn union_without_overlap_is_empty() {
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let a = to_re(&mut terms, "a");
    let b = to_re(&mut terms, "b");
    let c = to_re(&mut terms, "c");
    let d = to_re(&mut terms, "d");
    let ab = union(&mut terms, vec![a, b]);
    let cd = union(&mut terms, vec![c, d]);
    let l1 = deny_in(&mut terms, x, ab);
    let l2 = deny_in(&mut terms, x, cd);
    assert!(recognize_regex_intersect_empty(&terms, &[l1, l2]));
}

#[test]
fn empty_word_is_in_both_stars_so_not_empty() {
    let mut terms = TermStore::new();
    let x = str_var(&mut terms, "X");
    let a = to_re(&mut terms, "a");
    let b = to_re(&mut terms, "b");
    let sa = star(&mut terms, a);
    let sb = star(&mut terms, b);
    let l1 = deny_in(&mut terms, x, sa);
    let l2 = deny_in(&mut terms, x, sb);
    assert!(!recognize_regex_intersect_empty(&terms, &[l1, l2]));
}

#[test]
fn blocks_tile_the_whole_alphabet() {
    let mut terms = TermStore::new();
    let d = range(&mut terms, "0", "9");
    let r = star(&mut terms, d);
    let (arena, _c) = prepare(&terms, &[(r, true)]).expect("prepared");
    assert_eq!(arena.blocks[0].0, 0);
    assert_eq!(arena.blocks[arena.blocks.len() - 1].1, ALPHABET_HI);
    for w in arena.blocks.windows(2) {
        assert_eq!(w[1].0, w[0].1 + 1, "blocks must be contiguous");
    }
}

// ---------------------------------------------------------------------------
// Randomized soundness cross-check against a THIRD implementation
// ---------------------------------------------------------------------------

/// Naive membership by recursive splitting — no derivatives, no arena caches,
/// no alphabet partition. A deliberately different algorithm from the one under
/// test, used only to refute a wrong EMPTY verdict (the wrong-UNSAT direction).
fn naive_match(arena: &Arena, id: ReId, w: &[u32]) -> bool {
    match arena.get(id).clone() {
        Node::Nil => false,
        Node::Eps => w.is_empty(),
        Node::Set(iv) => w.len() == 1 && iv.iter().any(|&(lo, hi)| lo <= w[0] && w[0] <= hi),
        Node::Cat(xs) => naive_match_cat(arena, &xs, w),
        Node::Alt(xs) => xs.iter().any(|&x| naive_match(arena, x, w)),
        Node::And(xs) => xs.iter().all(|&x| naive_match(arena, x, w)),
        Node::Star(x) => {
            if w.is_empty() {
                return true;
            }
            (1..=w.len()).any(|k| naive_match(arena, x, &w[..k]) && naive_match(arena, id, &w[k..]))
        }
        Node::Not(x) => !naive_match(arena, x, w),
        Node::Rep(x, lo, hi) => (lo..=hi).any(|k| naive_match_pow(arena, x, k, w)),
    }
}

fn naive_match_cat(arena: &Arena, xs: &[ReId], w: &[u32]) -> bool {
    match xs.split_first() {
        None => w.is_empty(),
        Some((&head, [])) => naive_match(arena, head, w),
        Some((&head, rest)) => (0..=w.len())
            .any(|k| naive_match(arena, head, &w[..k]) && naive_match_cat(arena, rest, &w[k..])),
    }
}

fn naive_match_pow(arena: &Arena, x: ReId, k: u32, w: &[u32]) -> bool {
    if k == 0 {
        return w.is_empty();
    }
    (0..=w.len())
        .any(|i| naive_match(arena, x, &w[..i]) && naive_match_pow(arena, x, k - 1, &w[i..]))
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn gen_regex(terms: &mut TermStore, rng: &mut Rng, depth: u32) -> TermId {
    if depth == 0 || rng.below(3) == 0 {
        return match rng.below(6) {
            0 => to_re(terms, "a"),
            1 => to_re(terms, "b"),
            2 => to_re(terms, "ab"),
            3 => range(terms, "a", "b"),
            4 => re_app(terms, "re.allchar", vec![]),
            _ => to_re(terms, ""),
        };
    }
    let a = gen_regex(terms, rng, depth - 1);
    match rng.below(7) {
        0 => {
            let b = gen_regex(terms, rng, depth - 1);
            concat(terms, vec![a, b])
        }
        1 => {
            let b = gen_regex(terms, rng, depth - 1);
            union(terms, vec![a, b])
        }
        2 => star(terms, a),
        3 => re_app(terms, "re.opt", vec![a]),
        4 => comp(terms, a),
        5 => terms.mk_app(
            Symbol::Indexed("re.loop".to_string(), vec![0, 2]),
            [a],
            Sort::RegLan,
        ),
        _ => {
            let b = gen_regex(terms, rng, depth - 1);
            re_app(terms, "re.inter", vec![a, b])
        }
    }
}

#[test]
fn randomized_empty_verdicts_are_never_refuted_by_a_naive_matcher() {
    // Wrong-UNSAT is the only failure mode that matters here: whenever the
    // checker certifies EMPTY, an independent naive matcher must find no word
    // in the intersection. The enumeration alphabet deliberately includes a
    // code point the regexes never mention ('z' and a high plane character),
    // because complement makes unmentioned characters live.
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let alphabet: [u32; 4] = ['a' as u32, 'b' as u32, 'z' as u32, 0x2_0000];
    let mut certified = 0u32;
    for _ in 0..400 {
        let mut terms = TermStore::new();
        let x = str_var(&mut terms, "X");
        let n = 1 + rng.below(3) as usize;
        let mut specs: Vec<(TermId, bool)> = Vec::new();
        let mut clause: Vec<TermId> = Vec::new();
        for _ in 0..n {
            let r = gen_regex(&mut terms, &mut rng, 3);
            let positive = rng.below(4) != 0;
            specs.push((r, positive));
            clause.push(if positive {
                deny_in(&mut terms, x, r)
            } else {
                deny_not_in(&mut terms, x, r)
            });
        }
        if !recognize_regex_intersect_empty(&terms, &clause) {
            continue;
        }
        certified += 1;
        let Some((arena, constraints)) = prepare(&terms, &specs) else {
            panic!("a certified group must translate");
        };
        // Enumerate every word of length <= 4 over the probe alphabet.
        let mut word: Vec<u32> = Vec::new();
        let mut stack: Vec<Vec<u32>> = vec![Vec::new()];
        while let Some(w) = stack.pop() {
            assert!(
                !constraints.iter().all(|&c| naive_match(&arena, c, &w)),
                "checker certified EMPTY but the naive matcher accepts {w:?}"
            );
            if w.len() < 4 {
                for &c in &alphabet {
                    word.clone_from(&w);
                    word.push(c);
                    stack.push(word.clone());
                }
            }
        }
    }
    assert!(
        certified >= 20,
        "the generator must actually exercise the EMPTY path, got {certified}"
    );
}
