// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the `bit-blast` preprocessing pass (`bit_blast.rs`).
//!
//! Coverage:
//! - STRUCTURAL: a blasted supported QF_BV goal contains **no** bit-vector
//!   sub-terms (pure Boolean).
//! - HONESTY GATE: `apply` reports progress iff it actually blasted; an
//!   out-of-fragment op (e.g. `bvudiv`) and a BV-free goal are both left
//!   untouched with no progress (never a fabricated/partial blast).
//! - CORRECTNESS: exhaustive per-model equisatisfiability of the blasted goal
//!   against a direct semantic evaluation of the original BV goal, for every
//!   assignment over small widths.

use super::{BitBlast, PreprocessingPass};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use std::collections::HashSet;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Collect every sub-term reachable from `roots`.
fn reachable(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    let mut seen = HashSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    let mut out = Vec::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        out.push(id);
        match terms.get(id).clone() {
            TermData::App(_, args) => stack.extend(args),
            TermData::Not(t) => stack.push(t),
            TermData::Ite(c, t, e) => {
                stack.push(c);
                stack.push(t);
                stack.push(e);
            }
            TermData::Let(bs, body) => {
                for (_, v) in bs {
                    stack.push(v);
                }
                stack.push(body);
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(b),
            _ => {}
        }
    }
    out
}

/// Assert that no reachable sub-term is bit-vector-sorted (the goal is pure
/// Boolean, so a downstream SAT/Boolean engine sees no BV terms).
fn assert_no_bv(terms: &TermStore, roots: &[TermId]) {
    for id in reachable(terms, roots) {
        assert!(
            !matches!(terms.sort(id), Sort::BitVec(_)),
            "blasted goal still contains a BV-sorted term: {:?} :: {:?}",
            terms.get(id),
            terms.sort(id),
        );
    }
}

// ---------------------------------------------------------------------------
// STRUCTURAL: blasted supported goal is pure Boolean.
// ---------------------------------------------------------------------------

#[test]
fn blasted_qf_bv_goal_has_no_bv_terms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let y = terms.mk_var("y", Sort::bitvec(4));
    // (bvult (bvadd (bvand x y) (bvxor x y)) (bvor x (bvnot y)))
    let and = terms.mk_bvand(vec![x, y]);
    let xor = terms.mk_bvxor(vec![x, y]);
    let add = terms.mk_bvadd(vec![and, xor]);
    let noty = terms.mk_bvnot(y);
    let or = terms.mk_bvor(vec![x, noty]);
    let lt = terms.mk_bvult(add, or);

    let mut goal = vec![lt];
    let progressed = BitBlast::new().apply(&mut terms, &mut goal);
    assert!(progressed, "bit-blast must report progress on a QF_BV goal");
    assert_no_bv(&terms, &goal);
}

#[test]
fn blasted_concat_extract_goal_has_no_bv_terms() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    // (= ((_ extract 5 2) (concat a b)) (bvadd a #b0001))
    let cat = terms.mk_bvconcat(vec![a, b]);
    let ext = terms.mk_bvextract(5, 2, cat);
    let one = terms.mk_bitvec(BigInt::from(1), 4);
    let add = terms.mk_bvadd(vec![a, one]);
    let eq = terms.mk_eq(ext, add);

    let mut goal = vec![eq];
    let progressed = BitBlast::new().apply(&mut terms, &mut goal);
    assert!(progressed, "bit-blast must blast concat/extract");
    assert_no_bv(&terms, &goal);
}

// ---------------------------------------------------------------------------
// HONESTY GATE: no fabricated / partial blast.
// ---------------------------------------------------------------------------

#[test]
fn out_of_fragment_op_is_left_untouched() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let y = terms.mk_var("y", Sort::bitvec(4));
    // bvudiv is deliberately NOT in the supported fragment.
    let div = terms.mk_bvudiv(vec![x, y]);
    let z = terms.mk_bitvec(BigInt::from(3), 4);
    let eq = terms.mk_eq(div, z);

    let before = vec![eq];
    let mut goal = before.clone();
    let progressed = BitBlast::new().apply(&mut terms, &mut goal);
    assert!(
        !progressed,
        "an out-of-fragment op must yield an honest identity (no progress)"
    );
    assert_eq!(
        goal, before,
        "the goal must be left byte-for-byte unchanged"
    );
}

#[test]
fn bv_free_goal_is_a_genuine_no_op() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let or = terms.mk_or(vec![p, q]);

    let before = vec![or];
    let mut goal = before.clone();
    let progressed = BitBlast::new().apply(&mut terms, &mut goal);
    assert!(
        !progressed,
        "bit-blast on a BV-free goal must be a genuine no-op"
    );
    assert_eq!(goal, before);
}

// ---------------------------------------------------------------------------
// CORRECTNESS: exhaustive per-model equisatisfiability.
// ---------------------------------------------------------------------------

/// A tiny evaluator: evaluate a supported BV/Bool term under an assignment of
/// each BV *variable* to a concrete unsigned value, returning either a BV word
/// (as a `u64`, low `width` bits) or a Boolean.
enum Val {
    Bv(u64, u32),
    Bool(bool),
}

fn eval(terms: &TermStore, id: TermId, env: &std::collections::HashMap<String, u64>) -> Val {
    let mask = |w: u32| if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    match terms.get(id).clone() {
        TermData::Const(Constant::Bool(b)) => Val::Bool(b),
        TermData::Const(Constant::BitVec { value, width }) => {
            let v: u64 = value.iter_u64_digits().next().unwrap_or(0);
            Val::Bv(v & mask(width), width)
        }
        TermData::Var(name, _) => match terms.sort(id) {
            Sort::BitVec(bvs) => Val::Bv(env[&name] & mask(bvs.width), bvs.width),
            Sort::Bool => Val::Bool(env[&name] != 0),
            other => panic!("unexpected var sort {other:?}"),
        },
        TermData::Not(t) => Val::Bool(!eval_bool(terms, t, env)),
        TermData::Ite(c, t, e) => {
            if eval_bool(terms, c, env) {
                eval(terms, t, env)
            } else {
                eval(terms, e, env)
            }
        }
        TermData::App(sym, args) => eval_app(terms, &sym, &args, env, mask),
        other => panic!("evaluator reached unsupported term {other:?}"),
    }
}

fn eval_bool(terms: &TermStore, id: TermId, env: &std::collections::HashMap<String, u64>) -> bool {
    match eval(terms, id, env) {
        Val::Bool(b) => b,
        Val::Bv(..) => panic!("expected Bool"),
    }
}

fn eval_bv(
    terms: &TermStore,
    id: TermId,
    env: &std::collections::HashMap<String, u64>,
) -> (u64, u32) {
    match eval(terms, id, env) {
        Val::Bv(v, w) => (v, w),
        Val::Bool(_) => panic!("expected Bv"),
    }
}

fn eval_app(
    terms: &TermStore,
    sym: &Symbol,
    args: &[TermId],
    env: &std::collections::HashMap<String, u64>,
    mask: impl Fn(u32) -> u64,
) -> Val {
    // Indexed wire-ops (extract / *_extend / repeat) — constant shifts lower to
    // these in the core builder, so the evaluator must model them too.
    if let Symbol::Indexed(name, idx) = sym {
        let (v, w) = eval_bv(terms, args[0], env);
        return match name.as_str() {
            "extract" => {
                let high = idx[0];
                let low = idx[1];
                let nw = high - low + 1;
                Val::Bv((v >> low) & mask(nw), nw)
            }
            "zero_extend" => {
                let k = idx[0];
                Val::Bv(v, w + k)
            }
            "sign_extend" => {
                let k = idx[0];
                let sign = (v >> (w - 1)) & 1 == 1;
                let fill = if sign { mask(k) << w } else { 0 };
                Val::Bv((v | fill) & mask(w + k), w + k)
            }
            "repeat" => {
                let k = idx[0];
                let mut acc = 0u64;
                for j in 0..k {
                    acc |= v << (j * w);
                }
                Val::Bv(acc & mask(w * k), w * k)
            }
            "rotate_left" => {
                let kk = if w > 0 { idx[0] % w } else { 0 };
                let r = if kk == 0 {
                    v
                } else {
                    ((v << kk) | (v >> (w - kk))) & mask(w)
                };
                Val::Bv(r, w)
            }
            "rotate_right" => {
                let kk = if w > 0 { idx[0] % w } else { 0 };
                let r = if kk == 0 {
                    v
                } else {
                    ((v >> kk) | (v << (w - kk))) & mask(w)
                };
                Val::Bv(r, w)
            }
            other => panic!("evaluator reached unsupported indexed op {other}"),
        };
    }
    let name = sym.name();
    let bv = |i: usize| eval_bv(terms, args[i], env);
    match name {
        "bvand" => {
            let (a, w) = bv(0);
            let (b, _) = bv(1);
            Val::Bv(a & b, w)
        }
        "bvor" => {
            let (a, w) = bv(0);
            let (b, _) = bv(1);
            Val::Bv(a | b, w)
        }
        "bvxor" => {
            let (a, w) = bv(0);
            let (b, _) = bv(1);
            Val::Bv((a ^ b) & mask(w), w)
        }
        "bvnot" => {
            let (a, w) = bv(0);
            Val::Bv((!a) & mask(w), w)
        }
        "bvadd" => {
            let (a, w) = bv(0);
            let (b, _) = bv(1);
            Val::Bv(a.wrapping_add(b) & mask(w), w)
        }
        "bvsub" => {
            let (a, w) = bv(0);
            let (b, _) = bv(1);
            Val::Bv(a.wrapping_sub(b) & mask(w), w)
        }
        "bvmul" => {
            let (a, w) = bv(0);
            let (b, _) = bv(1);
            Val::Bv(a.wrapping_mul(b) & mask(w), w)
        }
        "bvneg" => {
            let (a, w) = bv(0);
            Val::Bv((0u64.wrapping_sub(a)) & mask(w), w)
        }
        "bvshl" => {
            let (a, w) = bv(0);
            let (s, _) = bv(1);
            let r = if s >= u64::from(w) { 0 } else { a << s };
            Val::Bv(r & mask(w), w)
        }
        "bvlshr" => {
            let (a, w) = bv(0);
            let (s, _) = bv(1);
            let r = if s >= u64::from(w) { 0 } else { a >> s };
            Val::Bv(r & mask(w), w)
        }
        "bvashr" => {
            let (a, w) = bv(0);
            let (s, _) = bv(1);
            let sign = (a >> (w - 1)) & 1 == 1;
            let sa = sign_extend_i128(a, w);
            let r_signed: i128 = if s >= u64::from(w) {
                if sign {
                    -1
                } else {
                    0
                }
            } else {
                sa >> (s as u32)
            };
            Val::Bv((r_signed as u64) & mask(w), w)
        }
        "concat" => {
            // args[0] high, args[1] low.
            let (hi, hw) = bv(0);
            let (lo, lw) = bv(1);
            let _ = hw;
            Val::Bv((hi << lw) | lo, hw + lw)
        }
        "bvcomp" => {
            // 1-bit result: 1 iff the operands are equal.
            let (a, _) = bv(0);
            let (b, _) = bv(1);
            Val::Bv(u64::from(a == b), 1)
        }
        "bvult" => Val::Bool(bv(0).0 < bv(1).0),
        "bvule" => Val::Bool(bv(0).0 <= bv(1).0),
        "bvugt" => Val::Bool(bv(0).0 > bv(1).0),
        "bvuge" => Val::Bool(bv(0).0 >= bv(1).0),
        "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
            let (a, w) = bv(0);
            let (b, _) = bv(1);
            let sa = sign_extend_i128(a, w);
            let sb = sign_extend_i128(b, w);
            Val::Bool(match name {
                "bvslt" => sa < sb,
                "bvsle" => sa <= sb,
                "bvsgt" => sa > sb,
                _ => sa >= sb,
            })
        }
        "=" => {
            if matches!(terms.sort(args[0]), Sort::BitVec(_)) {
                Val::Bool(bv(0).0 == bv(1).0)
            } else {
                Val::Bool(eval_bool(terms, args[0], env) == eval_bool(terms, args[1], env))
            }
        }
        "and" => Val::Bool(args.iter().all(|&a| eval_bool(terms, a, env))),
        "or" => Val::Bool(args.iter().any(|&a| eval_bool(terms, a, env))),
        "xor" => Val::Bool(
            args.iter()
                .fold(false, |acc, &a| acc ^ eval_bool(terms, a, env)),
        ),
        other => panic!("evaluator reached unsupported op {other}"),
    }
}

fn sign_extend_i128(v: u64, w: u32) -> i128 {
    let sign = (v >> (w - 1)) & 1 == 1;
    if sign {
        (v as i128) - (1i128 << w)
    } else {
        v as i128
    }
}

/// Read the Boolean value of a blasted formula under an assignment of the
/// blasted bit-variables (`bit_env`).
fn eval_blasted(
    terms: &TermStore,
    id: TermId,
    bit_env: &std::collections::HashMap<TermId, bool>,
) -> bool {
    match terms.get(id).clone() {
        TermData::Const(Constant::Bool(b)) => b,
        TermData::Var(_, _) => bit_env[&id],
        TermData::Not(t) => !eval_blasted(terms, t, bit_env),
        TermData::Ite(c, t, e) => {
            if eval_blasted(terms, c, bit_env) {
                eval_blasted(terms, t, bit_env)
            } else {
                eval_blasted(terms, e, bit_env)
            }
        }
        TermData::App(sym, args) => match sym.name() {
            "and" => args.iter().all(|&a| eval_blasted(terms, a, bit_env)),
            "or" => args.iter().any(|&a| eval_blasted(terms, a, bit_env)),
            "xor" => args
                .iter()
                .fold(false, |acc, &a| acc ^ eval_blasted(terms, a, bit_env)),
            "=>" => {
                let mut it = args.iter().rev();
                let last = *it.next().expect("=> needs args");
                let mut acc = eval_blasted(terms, last, bit_env);
                for &a in it {
                    acc = !eval_blasted(terms, a, bit_env) || acc;
                }
                acc
            }
            "=" => eval_blasted(terms, args[0], bit_env) == eval_blasted(terms, args[1], bit_env),
            other => panic!("blasted goal contains a non-Boolean op {other}"),
        },
        other => panic!("blasted goal contains an unexpected shape {other:?}"),
    }
}

/// EXHAUSTIVE equisat check: for a supported BV goal over the variables
/// `vars` (name, width), verify that the original goal is satisfiable under
/// SOME assignment iff the blasted goal is satisfiable under SOME assignment,
/// AND — stronger — that for every BV assignment the original goal's truth
/// value equals the blasted goal's value under the induced bit assignment.
fn check_exhaustive(build: impl Fn(&mut TermStore) -> (Vec<TermId>, Vec<(String, u32)>)) {
    let mut terms = TermStore::new();
    let (goal_orig, vars) = build(&mut terms);

    // Record the original variable terms so we can find their blasted bits.
    let mut var_terms: Vec<(String, u32, TermId)> = Vec::new();
    for (name, w) in &vars {
        let t = terms.mk_var(name.clone(), Sort::bitvec(*w));
        var_terms.push((name.clone(), *w, t));
    }

    // Blast a clone of the goal.
    let mut goal = goal_orig.clone();
    let mut pass = BitBlast::new();
    let progressed = pass.apply(&mut terms, &mut goal);
    assert!(progressed, "bit-blast must make progress on this goal");
    assert_no_bv(&terms, &goal);

    // The blasted bits of each variable are memoized in the pass; re-query them.
    let var_bits: Vec<(String, u32, Vec<TermId>)> = var_terms
        .iter()
        .map(|(name, w, t)| (name.clone(), *w, pass.bits_for_test(*t)))
        .collect();

    let total_bits: u32 = vars.iter().map(|(_, w)| *w).sum();
    assert!(total_bits <= 16, "keep the exhaustive space small");

    for assignment in 0u64..(1u64 << total_bits) {
        // Build the per-variable value environment and the induced bit env.
        let mut env = std::collections::HashMap::new();
        let mut bit_env = std::collections::HashMap::new();
        let mut offset = 0u32;
        for (name, w, bits) in &var_bits {
            let val = (assignment >> offset) & ((1u64 << w) - 1);
            env.insert(name.clone(), val);
            for (i, &bit) in bits.iter().enumerate() {
                bit_env.insert(bit, (val >> i) & 1 == 1);
            }
            offset += w;
        }

        let orig_true = goal_orig.iter().all(|&f| eval_bool(&terms, f, &env));
        let blasted_true = goal.iter().all(|&f| eval_blasted(&terms, f, &bit_env));
        assert_eq!(
            orig_true, blasted_true,
            "model mismatch at assignment {assignment:#b}: original={orig_true} blasted={blasted_true}"
        );
    }
}

#[test]
fn exhaustive_equisat_arith_and_compare() {
    check_exhaustive(|terms| {
        let x = terms.mk_var("x", Sort::bitvec(4));
        let y = terms.mk_var("y", Sort::bitvec(4));
        // (bvult (bvadd x y) (bvmul x y))  ∧  (bvsge x y)
        let add = terms.mk_bvadd(vec![x, y]);
        let mul = terms.mk_bvmul(vec![x, y]);
        let lt = terms.mk_bvult(add, mul);
        let sge = terms.mk_bvsge(x, y);
        (vec![lt, sge], vec![("x".into(), 4), ("y".into(), 4)])
    });
}

#[test]
fn exhaustive_equisat_bitwise_shift_concat() {
    check_exhaustive(|terms| {
        let x = terms.mk_var("x", Sort::bitvec(4));
        let y = terms.mk_var("y", Sort::bitvec(4));
        // (= (bvshl x y) (bvor (bvand x y) (bvxor x (bvnot y))))
        let shl = terms.mk_bvshl(vec![x, y]);
        let and = terms.mk_bvand(vec![x, y]);
        let noty = terms.mk_bvnot(y);
        let xor = terms.mk_bvxor(vec![x, noty]);
        let or = terms.mk_bvor(vec![and, xor]);
        let eq = terms.mk_eq(shl, or);
        (vec![eq], vec![("x".into(), 4), ("y".into(), 4)])
    });
}

#[test]
fn exhaustive_equisat_sub_neg_ashr_lshr() {
    check_exhaustive(|terms| {
        let x = terms.mk_var("x", Sort::bitvec(4));
        let y = terms.mk_var("y", Sort::bitvec(4));
        // (= (bvsub x y) (bvadd x (bvneg y)))  ∧  (= (bvashr x #b0001) ...)
        let sub = terms.mk_bvsub(vec![x, y]);
        let negy = terms.mk_bvneg(y);
        let addn = terms.mk_bvadd(vec![x, negy]);
        let eq1 = terms.mk_eq(sub, addn);
        let one = terms.mk_bitvec(BigInt::from(1), 4);
        let ashr = terms.mk_bvashr(vec![x, one]);
        let lshr = terms.mk_bvlshr(vec![x, one]);
        let ne = terms.mk_eq(ashr, lshr);
        let notne = terms.mk_not(ne);
        // x negative ⇒ ashr differs from lshr on the top bit.
        let dm = terms.mk_bvult(x, y);
        let g = terms.mk_or(vec![notne, dm]);
        (vec![eq1, g], vec![("x".into(), 4), ("y".into(), 4)])
    });
}

// ---------------------------------------------------------------------------
// NEWLY-SUPPORTED ops: rotate_left / rotate_right (constant amount) + bvcomp.
// ---------------------------------------------------------------------------

#[test]
fn exhaustive_equisat_rotate_and_bvcomp() {
    // Exercises the new wire-level circuits: a rotate_left / rotate_right of a
    // symbolic word (a constant bit permutation of the LSB-first bits) and
    // bvcomp (a 1-bit equality reducer). The per-model equisat check pins the
    // circuits to the independent value-level evaluator.
    check_exhaustive(|terms| {
        let x = terms.mk_var("x", Sort::bitvec(4));
        let y = terms.mk_var("y", Sort::bitvec(4));
        // For width 4, rotate_left(x,1) == rotate_right(x,3): a genuine identity
        // that would break if either permutation circuit were wrong.
        let rl = terms.mk_bvrotate_left(1, x);
        let rr = terms.mk_bvrotate_right(3, x);
        let same = terms.mk_eq(rl, rr);
        // (= (bvcomp x y) #b1)  ⟺  x = y.
        let comp = terms.mk_bvcomp(x, y);
        let one1 = terms.mk_bitvec(BigInt::from(1), 1);
        let comp_eq = terms.mk_eq(comp, one1);
        // A non-tautological use of a rotated word in a comparison.
        let rly = terms.mk_bvrotate_right(1, y);
        let lt = terms.mk_bvult(rl, rly);
        (
            vec![same, comp_eq, lt],
            vec![("x".into(), 4), ("y".into(), 4)],
        )
    });
}

#[test]
fn blasted_rotate_and_bvcomp_goal_has_no_bv_terms() {
    // Structural: the newly-supported ops must blast to a pure-Boolean goal too.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(8));
    // (bvult ((_ rotate_left 3) x) ((_ rotate_right 2) y))  ∧  (= (bvcomp x y) #b1)
    let rl = terms.mk_bvrotate_left(3, x);
    let rr = terms.mk_bvrotate_right(2, y);
    let lt = terms.mk_bvult(rl, rr);
    let comp = terms.mk_bvcomp(x, y);
    let one1 = terms.mk_bitvec(BigInt::from(1), 1);
    let comp_eq = terms.mk_eq(comp, one1);
    let g = terms.mk_and(vec![lt, comp_eq]);

    let mut goal = vec![g];
    let progressed = BitBlast::new().apply(&mut terms, &mut goal);
    assert!(progressed, "bit-blast must blast rotate/bvcomp");
    assert_no_bv(&terms, &goal);
}

// ---------------------------------------------------------------------------
// HONESTY CLASSIFICATION: classify_goal separates blast / no-op / honest-fail.
// This is the gate the tactic layer uses so `(apply bit-blast)` never returns a
// silent successful identity for a goal it did not actually blast.
// ---------------------------------------------------------------------------

#[test]
fn classify_goal_blasts_a_supported_bv_goal() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let y = terms.mk_var("y", Sort::bitvec(4));
    let add = terms.mk_bvadd(vec![x, y]);
    let lt = terms.mk_bvult(add, x);
    assert_eq!(
        BitBlast::new().classify_goal(&terms, &[lt]),
        Ok(true),
        "a fully-supported QF_BV goal must classify as blastable-with-BV"
    );
}

#[test]
fn classify_goal_is_identity_on_a_bv_free_goal() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let or = terms.mk_or(vec![p, q]);
    assert_eq!(
        BitBlast::new().classify_goal(&terms, &[or]),
        Ok(false),
        "a BV-free goal is z3's no-op identity (not a failure)"
    );
}

#[test]
fn classify_goal_honestly_fails_on_out_of_fragment_bvudiv() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let y = terms.mk_var("y", Sort::bitvec(4));
    let div = terms.mk_bvudiv(vec![x, y]);
    let z = terms.mk_bitvec(BigInt::from(3), 4);
    let eq = terms.mk_eq(div, z);
    match BitBlast::new().classify_goal(&terms, &[eq]) {
        Err(detail) => assert!(
            detail.contains("bvudiv"),
            "the honest-failure detail must name the offending operator; got {detail:?}"
        ),
        other => panic!("bvudiv goal must HONESTLY FAIL classification, got {other:?}"),
    }
}
