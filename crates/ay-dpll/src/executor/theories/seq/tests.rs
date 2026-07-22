// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for generic sequence theory axiom generation.

use super::*;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::Sort;
use num_bigint::BigInt;
use num_traits::Zero;

/// Helper: create a fresh Executor with seq terms for testing.
fn make_executor() -> Executor {
    Executor::new()
}

/// Helper: create `seq.contains(s, t)` and return `(contains_term, s, t)`.
fn mk_contains(exec: &mut Executor, s: TermId, t: TermId) -> TermId {
    exec.ctx
        .terms
        .mk_app(Symbol::named("seq.contains"), vec![s, t], Sort::Bool)
}

/// Helper: create `seq.extract(s, i, n)` and return the extract term.
fn mk_extract(exec: &mut Executor, s: TermId, i: TermId, n: TermId) -> TermId {
    let sort = exec.ctx.terms.sort(s).clone();
    exec.ctx
        .terms
        .mk_app(Symbol::named("seq.extract"), vec![s, i, n], sort)
}

/// Helper: create `seq.indexof(s, t, offset)` and return the term.
fn mk_indexof(exec: &mut Executor, s: TermId, t: TermId, offset: TermId) -> TermId {
    exec.ctx
        .terms
        .mk_app(Symbol::named("seq.indexof"), vec![s, t, offset], Sort::Int)
}

/// Helper: create `seq.replace(u, src, dst)` and return the term.
fn mk_replace(exec: &mut Executor, u: TermId, src: TermId, dst: TermId) -> TermId {
    let sort = exec.ctx.terms.sort(u).clone();
    exec.ctx
        .terms
        .mk_app(Symbol::named("seq.replace"), vec![u, src, dst], sort)
}

/// Helper: check if any axiom encodes `term >= 0`.
/// Note: mk_ge(a, b) normalizes to mk_le(b, a), so `a >= 0` is stored as `(<= 0 a)`.
fn has_ge_zero(exec: &Executor, axioms: &[TermId], term: TermId) -> bool {
    axioms.iter().any(|&ax| {
        if let TermData::App(Symbol::Named(name), args) = exec.ctx.terms.get(ax) {
            // Check (<= 0 term) — the canonical form of (>= term 0).
            if name == "<=" && args.len() == 2 && args[1] == term {
                matches!(exec.ctx.terms.get(args[0]),
                    TermData::Const(Constant::Int(n)) if n.is_zero())
            } else {
                false
            }
        } else {
            false
        }
    })
}

/// Helper: count axioms that encode implications from `condition`.
/// mk_implies(a, b) normalizes to (or (not a) b), and mk_or sorts args,
/// so (not condition) may be at any position.
fn count_implications_from(exec: &Executor, axioms: &[TermId], condition: TermId) -> usize {
    axioms
        .iter()
        .filter(|&&ax| {
            if let TermData::App(Symbol::Named(name), args) = exec.ctx.terms.get(ax) {
                if name == "or" {
                    // Check if any arg is (not condition).
                    args.iter().any(|&arg| {
                        matches!(exec.ctx.terms.get(arg),
                            TermData::Not(inner) if *inner == condition)
                    })
                } else {
                    false
                }
            } else {
                false
            }
        })
        .count()
}

// ── contains axiom generator ──

#[test]
fn test_contains_generates_decomposition_and_length_axioms() {
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let s = exec.ctx.terms.mk_var("s", seq_sort.clone());
    let t = exec.ctx.terms.mk_var("t", seq_sort);
    let c = mk_contains(&mut exec, s, t);

    // Add the contains term to assertions so scan can find it.
    exec.ctx.assertions.push(c);

    let scan = exec.scan_seq_terms();
    assert_eq!(
        scan.contains_terms.len(),
        1,
        "scan should find one contains term"
    );

    let axioms = exec.generate_seq_contains_axioms(&scan);

    // Should have at least 4 axioms:
    // 1. contains => s = sk_left ++ t ++ sk_right (decomposition)
    // 2. contains => len(sk_left) >= 0
    // 3. contains => len(sk_right) >= 0
    // 4. contains => len(s) >= len(t)
    assert!(
        axioms.len() >= 4,
        "contains should generate >=4 axioms, got {}",
        axioms.len()
    );

    // At least 3 should be implications from the contains term:
    // decomposition + two skolem non-negativity. The fourth (len(s) >= len(t))
    // may be simplified differently depending on term canonicalization.
    let impl_count = count_implications_from(&exec, &axioms, c);
    assert!(
        impl_count >= 3,
        "expected >=3 implications from contains term, got {impl_count}"
    );
}

#[test]
fn test_contains_ground_evaluation_forces_true() {
    // seq.contains([1,2,3], [2]) should force contains = true.
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let two = exec.ctx.terms.mk_int(BigInt::from(2));
    let three = exec.ctx.terms.mk_int(BigInt::from(3));
    let u1 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), vec![one], seq_sort.clone());
    let u2 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), vec![two], seq_sort.clone());
    let u3 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), vec![three], seq_sort.clone());
    let s = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.++"), vec![u1, u2, u3], seq_sort.clone());
    let t = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), vec![two], seq_sort);

    let c = mk_contains(&mut exec, s, t);
    exec.ctx.assertions.push(c);

    let scan = exec.scan_seq_terms();
    let axioms = exec.generate_seq_contains_axioms(&scan);

    // Should include a ground-eval axiom: the contains_term itself (forcing true).
    assert!(
        axioms.contains(&c),
        "ground contains([1,2,3], [2]) should generate axiom forcing contains = true"
    );
}

#[test]
fn test_contains_ground_evaluation_forces_false() {
    // seq.contains([1,2], [3]) should force not(contains).
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let two = exec.ctx.terms.mk_int(BigInt::from(2));
    let three = exec.ctx.terms.mk_int(BigInt::from(3));
    let u1 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), vec![one], seq_sort.clone());
    let u2 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), vec![two], seq_sort.clone());
    let s = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.++"), vec![u1, u2], seq_sort.clone());
    let t = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), vec![three], seq_sort);

    let c = mk_contains(&mut exec, s, t);
    exec.ctx.assertions.push(c);

    let scan = exec.scan_seq_terms();
    let axioms = exec.generate_seq_contains_axioms(&scan);

    // Should include not(c) forcing false.
    let not_c = exec.ctx.terms.mk_not(c);
    assert!(
        axioms.contains(&not_c),
        "ground contains([1,2], [3]) should generate axiom forcing contains = false"
    );
}

// ── extract axiom generator ──

#[test]
fn test_extract_generates_skolem_decomposition() {
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let s = exec.ctx.terms.mk_var("s", seq_sort);
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let n = exec.ctx.terms.mk_var("n", Sort::Int);
    let e = mk_extract(&mut exec, s, i, n);

    exec.ctx.assertions.push(e);

    let scan = exec.scan_seq_terms();
    assert_eq!(
        scan.extract_terms.len(),
        1,
        "scan should find one extract term"
    );

    let axioms = exec.generate_seq_extract_axioms(&scan);

    // Extract generates several axioms:
    // - Skolem decomposition: in-bounds => s = pre ++ e ++ post
    // - Length of pre = i
    // - Length of e (two cases: normal vs clamped)
    // - OOB guard: i < 0 OR ... => e = empty
    // - Non-negativity axioms
    assert!(
        axioms.len() >= 5,
        "extract should generate >=5 axioms, got {}",
        axioms.len()
    );
}

#[test]
fn test_extract_ground_forces_concrete_result() {
    // seq.extract([10,20,30], 1, 1) on a ground sequence should produce
    // concrete element equality axioms.
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let ten = exec.ctx.terms.mk_int(BigInt::from(10));
    let twenty = exec.ctx.terms.mk_int(BigInt::from(20));
    let thirty = exec.ctx.terms.mk_int(BigInt::from(30));
    let u10 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), vec![ten], seq_sort.clone());
    let u20 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), vec![twenty], seq_sort.clone());
    let u30 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), vec![thirty], seq_sort.clone());
    let s = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.++"), vec![u10, u20, u30], seq_sort);
    let idx = exec.ctx.terms.mk_int(BigInt::from(1));
    let len = exec.ctx.terms.mk_int(BigInt::from(1));
    let e = mk_extract(&mut exec, s, idx, len);

    exec.ctx.assertions.push(e);

    let scan = exec.scan_seq_terms();
    let axioms = exec.generate_seq_extract_axioms(&scan);

    // Ground path generates: len(e) = result_len, nth element equalities.
    // Check that axioms are non-empty (ground eval path produced something).
    assert!(!axioms.is_empty(), "ground extract should generate axioms");
}

// ── indexof axiom generator ──

#[test]
fn test_indexof_generates_contains_bridge_and_result_axioms() {
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let s = exec.ctx.terms.mk_var("s", seq_sort.clone());
    let t = exec.ctx.terms.mk_var("t", seq_sort);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let r = mk_indexof(&mut exec, s, t, zero);

    exec.ctx.assertions.push(r);

    let scan = exec.scan_seq_terms();
    assert_eq!(
        scan.indexof_terms.len(),
        1,
        "scan should find one indexof term"
    );

    let (axioms, synth_contains) = exec.generate_seq_indexof_axioms(&scan);

    // indexof should synthesize a contains(s, t) term.
    assert!(
        !synth_contains.is_empty(),
        "indexof should synthesize contains(s, t) term"
    );

    // Verify the synthesized contains triple has the right structure.
    let (_, cs, ct) = synth_contains[0];
    assert_eq!(cs, s, "synthesized contains should reference original s");
    assert_eq!(ct, t, "synthesized contains should reference original t");

    // indexof generates several axioms:
    // - Bridge: !contains(s,t) => r = -1
    // - Decomposition: contains & t != "" => s = left ++ t ++ right
    // - Result: r = len(left)
    // - Tightest prefix guarantee
    // - r >= -1
    assert!(
        axioms.len() >= 4,
        "indexof should generate >=4 axioms, got {}",
        axioms.len()
    );

    // Should include r >= -1, stored as (<= -1 r).
    let neg_one = exec.ctx.terms.mk_int(BigInt::from(-1));
    let r_ge_neg1 = axioms.iter().any(|&ax| {
        if let TermData::App(Symbol::Named(name), args) = exec.ctx.terms.get(ax) {
            name == "<=" && args.len() == 2 && args[0] == neg_one && args[1] == r
        } else {
            false
        }
    });
    assert!(r_ge_neg1, "indexof result should have r >= -1 axiom");
}

#[test]
fn test_indexof_nonzero_offset_generates_suffix_decomposition() {
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let s = exec.ctx.terms.mk_var("s", seq_sort.clone());
    let t = exec.ctx.terms.mk_var("t", seq_sort);
    let offset = exec.ctx.terms.mk_int(BigInt::from(2));
    let r = mk_indexof(&mut exec, s, t, offset);

    exec.ctx.assertions.push(r);

    let scan = exec.scan_seq_terms();
    let (axioms, synth_contains) = exec.generate_seq_indexof_axioms(&scan);

    // Non-zero offset still synthesizes contains.
    assert!(
        !synth_contains.is_empty(),
        "non-zero offset indexof should synthesize contains"
    );

    // Should generate more axioms than zero-offset (adds offset < 0 guard, etc).
    assert!(
        axioms.len() >= 5,
        "non-zero offset indexof should generate >=5 axioms, got {}",
        axioms.len()
    );
}

// ── replace axiom generator ──

#[test]
fn test_replace_generates_contains_bridge_and_decomposition() {
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let u = exec.ctx.terms.mk_var("u", seq_sort.clone());
    let src = exec.ctx.terms.mk_var("src", seq_sort.clone());
    let dst = exec.ctx.terms.mk_var("dst", seq_sort);
    let r = mk_replace(&mut exec, u, src, dst);

    exec.ctx.assertions.push(r);

    let scan = exec.scan_seq_terms();
    assert_eq!(
        scan.replace_terms.len(),
        1,
        "scan should find one replace term"
    );

    let (axioms, synth_contains) = exec.generate_seq_replace_axioms(&scan);

    // replace should synthesize a contains(u, src) term.
    assert!(
        !synth_contains.is_empty(),
        "replace should synthesize contains(u, src) term"
    );

    // Verify the synthesized contains triple references the right terms.
    let (_, cu, csrc) = synth_contains[0];
    assert_eq!(cu, u, "synthesized contains should reference u");
    assert_eq!(csrc, src, "synthesized contains should reference src");

    // replace generates several axioms:
    // - src = "" => r = dst ++ u
    // - u = "" => src = "" OR r = u
    // - !contains(u, src) => r = u
    // - Guard => u = sk_x ++ src ++ sk_y, r = sk_x ++ dst ++ sk_y
    // - Tightest prefix, length axioms, non-negativity
    assert!(
        axioms.len() >= 5,
        "replace should generate >=5 axioms, got {}",
        axioms.len()
    );
}

// ── len axiom generator ──

#[test]
fn test_len_generates_non_negativity() {
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let s = exec.ctx.terms.mk_var("s", seq_sort);
    let len_s = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);

    exec.ctx.assertions.push(len_s);

    let scan = exec.scan_seq_terms();
    assert_eq!(scan.len_terms.len(), 1, "scan should find one len term");

    let axioms = exec.generate_seq_len_axioms(&scan);

    // Axiom 1: seq.len(s) >= 0 (stored as (<= 0 seq.len(s))).
    assert!(
        has_ge_zero(&exec, &axioms, len_s),
        "len axiom should include seq.len(s) >= 0"
    );
}

#[test]
fn test_len_unit_equals_one() {
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let x = exec.ctx.terms.mk_int(BigInt::from(42));
    let unit = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), vec![x], seq_sort);

    exec.ctx.assertions.push(unit);

    let scan = exec.scan_seq_terms();
    assert_eq!(scan.unit_terms.len(), 1, "scan should find one unit term");

    let axioms = exec.generate_seq_len_axioms(&scan);

    // Axiom 2: seq.len(seq.unit(x)) = 1.
    // mk_eq canonicalizes argument order, so check both sides.
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let len_unit = exec.mk_seq_len(unit);
    let has_len_eq_1 = axioms.iter().any(|&ax| {
        if let TermData::App(Symbol::Named(name), args) = exec.ctx.terms.get(ax) {
            name == "="
                && args.len() == 2
                && ((args[0] == len_unit && args[1] == one)
                    || (args[0] == one && args[1] == len_unit))
        } else {
            false
        }
    });
    assert!(
        has_len_eq_1,
        "len axiom should include seq.len(seq.unit(42)) = 1"
    );
}

#[test]
fn test_len_concat_sum() {
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let a = exec.ctx.terms.mk_var("a", seq_sort.clone());
    let b = exec.ctx.terms.mk_var("b", seq_sort.clone());
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.++"), vec![a, b], seq_sort);
    let len_concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.len"), vec![concat], Sort::Int);

    exec.ctx.assertions.push(len_concat);

    let scan = exec.scan_seq_terms();
    assert_eq!(
        scan.concat_terms.len(),
        1,
        "scan should find one concat term"
    );

    let axioms = exec.generate_seq_len_axioms(&scan);

    // Axiom 4: seq.len(a ++ b) = seq.len(a) + seq.len(b)
    // Plus non-negativity for seq.len(a) and seq.len(b).
    // At least: 1 equality + 1 non-neg for len_concat + 2 non-neg for component lens.
    assert!(
        axioms.len() >= 3,
        "len(concat) should generate >=3 axioms (sum + non-neg), got {}",
        axioms.len()
    );

    // Check non-negativity for component lengths.
    let len_a = exec.mk_seq_len(a);
    let len_b = exec.mk_seq_len(b);
    assert!(
        has_ge_zero(&exec, &axioms, len_a),
        "should have seq.len(a) >= 0"
    );
    assert!(
        has_ge_zero(&exec, &axioms, len_b),
        "should have seq.len(b) >= 0"
    );
}

// ── two-pass scan ──

#[test]
fn test_two_pass_scan_discovers_synthesized_contains_from_indexof() {
    // indexof(s, t, 0) synthesizes a contains(s, t) term.
    // The two-pass scan should pick up this new contains term.
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let s = exec.ctx.terms.mk_var("s", seq_sort.clone());
    let t = exec.ctx.terms.mk_var("t", seq_sort);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let r = mk_indexof(&mut exec, s, t, zero);

    exec.ctx.assertions.push(r);

    // First pass: scan finds indexof but no contains.
    let mut scan = exec.scan_seq_terms();
    assert_eq!(scan.indexof_terms.len(), 1);
    assert_eq!(
        scan.contains_terms.len(),
        0,
        "first scan should find no contains"
    );

    // Generate axioms — indexof generator creates contains(s,t).
    let axioms = exec.generate_axioms_from_scan(&scan);

    // Second pass: scan the generated axioms for new seq operations.
    let prev_op_count = scan.axiom_op_count();
    scan.scan_roots(&exec.ctx.terms, &axioms);
    let new_op_count = scan.axiom_op_count();

    // The synthesized contains term should appear in the scan.
    assert!(
        !scan.contains_terms.is_empty(),
        "second pass should discover synthesized contains from indexof"
    );
    assert!(
        new_op_count > prev_op_count,
        "axiom_op_count should increase after second pass"
    );
}

#[test]
fn test_two_pass_scan_discovers_synthesized_contains_from_replace() {
    // replace(u, src, dst) synthesizes contains(u, src).
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let u = exec.ctx.terms.mk_var("u", seq_sort.clone());
    let src = exec.ctx.terms.mk_var("src", seq_sort.clone());
    let dst = exec.ctx.terms.mk_var("dst", seq_sort);
    let r = mk_replace(&mut exec, u, src, dst);

    exec.ctx.assertions.push(r);

    let mut scan = exec.scan_seq_terms();
    assert_eq!(scan.replace_terms.len(), 1);
    assert_eq!(scan.contains_terms.len(), 0);

    let axioms = exec.generate_axioms_from_scan(&scan);

    let prev_op_count = scan.axiom_op_count();
    scan.scan_roots(&exec.ctx.terms, &axioms);
    let new_op_count = scan.axiom_op_count();

    assert!(
        !scan.contains_terms.is_empty(),
        "second pass should discover synthesized contains from replace"
    );
    assert!(
        new_op_count > prev_op_count,
        "axiom_op_count should increase after second pass"
    );
}

// ── scan_seq_terms ──

#[test]
fn test_scan_finds_all_seq_operations() {
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let s = exec.ctx.terms.mk_var("s", seq_sort.clone());
    let t = exec.ctx.terms.mk_var("t", seq_sort);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let one = exec.ctx.terms.mk_int(BigInt::from(1));

    // Add one of each operation type.
    let c = mk_contains(&mut exec, s, t);
    let e = mk_extract(&mut exec, s, zero, one);
    let idx = mk_indexof(&mut exec, s, t, zero);
    let r = mk_replace(&mut exec, s, t, s);
    let pfx = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.prefixof"), vec![t, s], Sort::Bool);
    let sfx = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.suffixof"), vec![t, s], Sort::Bool);

    exec.ctx.assertions.extend([c, e, idx, r, pfx, sfx]);

    let scan = exec.scan_seq_terms();
    assert_eq!(scan.contains_terms.len(), 1);
    assert_eq!(scan.extract_terms.len(), 1);
    assert_eq!(scan.indexof_terms.len(), 1);
    assert_eq!(scan.replace_terms.len(), 1);
    assert_eq!(scan.prefixof_terms.len(), 1);
    assert_eq!(scan.suffixof_terms.len(), 1);
}

#[test]
fn test_scan_deduplicates_repeated_terms() {
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let s = exec.ctx.terms.mk_var("s", seq_sort.clone());
    let t = exec.ctx.terms.mk_var("t", seq_sort);
    let c = mk_contains(&mut exec, s, t);

    // Push the same contains term twice.
    exec.ctx.assertions.push(c);
    exec.ctx.assertions.push(c);

    let scan = exec.scan_seq_terms();
    assert_eq!(
        scan.contains_terms.len(),
        1,
        "scan should deduplicate repeated contains terms"
    );
}

// ── prefixof and suffixof ──

#[test]
fn test_prefixof_generates_decomposition_axioms() {
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let s = exec.ctx.terms.mk_var("s", seq_sort.clone());
    let t = exec.ctx.terms.mk_var("t", seq_sort);
    let p = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.prefixof"), vec![s, t], Sort::Bool);

    exec.ctx.assertions.push(p);

    let scan = exec.scan_seq_terms();
    let axioms = exec.generate_seq_prefixof_axioms(&scan);

    // prefixof generates:
    // - p => t = s ++ sk_suffix
    // - p => len(sk_suffix) >= 0
    // - p => len(s) <= len(t)
    // - len(s) >= 0, len(t) >= 0
    assert!(
        axioms.len() >= 4,
        "prefixof should generate >=4 axioms, got {}",
        axioms.len()
    );

    let impl_count = count_implications_from(&exec, &axioms, p);
    assert!(
        impl_count >= 3,
        "prefixof should generate >=3 implications from p, got {impl_count}"
    );
}

#[test]
fn test_suffixof_generates_decomposition_axioms() {
    let mut exec = make_executor();
    let seq_sort = Sort::seq(Sort::Int);
    let s = exec.ctx.terms.mk_var("s", seq_sort.clone());
    let t = exec.ctx.terms.mk_var("t", seq_sort);
    let p = exec
        .ctx
        .terms
        .mk_app(Symbol::named("seq.suffixof"), vec![s, t], Sort::Bool);

    exec.ctx.assertions.push(p);

    let scan = exec.scan_seq_terms();
    let axioms = exec.generate_seq_suffixof_axioms(&scan);

    assert!(
        axioms.len() >= 4,
        "suffixof should generate >=4 axioms, got {}",
        axioms.len()
    );

    let impl_count = count_implications_from(&exec, &axioms, p);
    assert!(
        impl_count >= 3,
        "suffixof should generate >=3 implications from p, got {impl_count}"
    );
}
