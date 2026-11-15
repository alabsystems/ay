// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The identity is true (exhaustively at `m = 4`), the recognizer accepts
//! exactly it, and the printer lane emits a hole-free certificate for it.

use super::bits;
use super::row::Row;
use super::term::{Op, Sort as GSort, Terms, T};
use super::*;
use ay_core::{Sort, Symbol, TermData};
use num_bigint::BigInt;

/// `t` as raw (unsimplified) AY terms over the limb variables `names`.
fn to_store(t: &Terms, root: T, store: &mut TermStore) -> TermId {
    let mut out: Vec<Option<TermId>> = vec![None; t.len()];
    let mut stack = vec![root];
    while let Some(&g) = stack.last() {
        let pending: Vec<T> = t
            .args(g)
            .iter()
            .copied()
            .filter(|&a| out[a as usize].is_none())
            .collect();
        if !pending.is_empty() {
            stack.extend(pending);
            continue;
        }
        stack.pop();
        let args: Vec<TermId> = t
            .args(g)
            .iter()
            .map(|&a| out[a as usize].unwrap())
            .collect();
        let sort = match t.sort(g) {
            GSort::Bool => Sort::Bool,
            GSort::Bv(w) => Sort::bitvec(w),
        };
        let named = |n: &str| Symbol::named(n);
        let id = match t.op(g) {
            Op::Var(name) => store.mk_var(&**name, sort),
            Op::Lit(bits) => {
                let value = bits
                    .iter()
                    .rev()
                    .fold(BigInt::from(0), |v, &b| v * 2 + u32::from(b));
                store.mk_bitvec(value, bits.len() as u32)
            }
            Op::Not => store.mk_not_raw(args[0]),
            Op::Ite => store.mk_ite_raw(args[0], args[1], args[2]),
            Op::And => store.mk_app(named("and"), args, sort),
            Op::Or => store.mk_app(named("or"), args, sort),
            Op::Neg => store.mk_app(named("bvneg"), args, sort),
            Op::Eq => store.mk_app(named("="), args, sort),
            Op::Add => store.mk_app(named("bvadd"), args, sort),
            Op::Mul => store.mk_app(named("bvmul"), args, sort),
            Op::Ult => store.mk_app(named("bvult"), args, sort),
            Op::Concat => store.mk_app(named("concat"), args, sort),
            Op::Udiv => store.mk_app(named("bvudiv"), args, sort),
            Op::Shl => store.mk_app(named("bvshl"), args, sort),
            Op::Extract(hi, lo) => {
                store.mk_app(Symbol::indexed("extract", vec![*hi, *lo]), args, sort)
            }
            Op::ZeroExt(k) => store.mk_app(Symbol::indexed("zero_extend", vec![*k]), args, sort),
            other => panic!("no AY spelling for {other:?}"),
        };
        out[g as usize] = Some(id);
    }
    out[root as usize].unwrap()
}

/// The value of `t` (a Boolean is 0/1) under the limb values `env`.
fn eval(t: &Terms, g: T, env: &[(T, u128)]) -> u128 {
    eval_memo(t, g, env, &mut vec![None; t.len()])
}

fn eval_memo(t: &Terms, g: T, env: &[(T, u128)], memo: &mut Vec<Option<u128>>) -> u128 {
    if let Some(v) = memo[g as usize] {
        return v;
    }
    let v = eval_node(t, g, env, memo);
    memo[g as usize] = Some(v);
    v
}

fn eval_node(t: &Terms, g: T, env: &[(T, u128)], memo: &mut Vec<Option<u128>>) -> u128 {
    let a: Vec<u128> = t
        .args(g)
        .iter()
        .map(|&x| eval_memo(t, x, env, memo))
        .collect();
    let w = t.width(g);
    let mask = |v: u128| if w >= 128 { v } else { v & ((1 << w) - 1) };
    match t.op(g) {
        Op::Var(_) => env.iter().find(|(v, _)| *v == g).unwrap().1,
        Op::Lit(bits) => bits.iter().rev().fold(0, |v, &b| v * 2 + u128::from(b)),
        Op::Not => 1 - a[0],
        Op::And => a.iter().product(),
        Op::Or => u128::from(a.iter().any(|&x| x == 1)),
        Op::Neg => mask(a[0].wrapping_neg()),
        Op::Eq => u128::from(a[0] == a[1]),
        Op::Ite => {
            if a[0] == 1 {
                a[1]
            } else {
                a[2]
            }
        }
        Op::Add => mask(a.iter().sum()),
        Op::Mul => mask(a[0] * a[1]),
        Op::Ult => u128::from(a[0] < a[1]),
        Op::Concat => (a[0] << t.width(t.args(g)[1])) | a[1],
        Op::Extract(hi, lo) => (a[0] >> lo) & ((1 << (hi - lo + 1)) - 1),
        Op::ZeroExt(_) => a[0],
        Op::Udiv => a[0].checked_div(a[1]).unwrap_or(mask(u128::MAX)),
        Op::Shl => mask(a[0].checked_shl(a[1] as u32).unwrap_or(0)),
        other => panic!("no evaluation for {other:?}"),
    }
}

fn row(m: u32) -> (Terms, Row) {
    let mut t = Terms::new();
    let leaves = Row::leaves(&mut t, m, ["a_lo", "a_hi", "b_lo", "b_hi"]);
    let row = Row::new(&mut t, m, leaves);
    (t, row)
}

/// Every one of the 2^16 limb assignments at `m = 4` satisfies the identity,
/// and the evaluator is not vacuous: dropping the `A != 0` guard is refuted.
#[test]
fn the_identity_holds_for_every_four_bit_limb_assignment() {
    let (mut t, row) = row(4);
    let unguarded = {
        let nqb = t.not(row.qb);
        let (one, zero) = (t.lit(vec![true]), t.lit(vec![false]));
        t.ite(nqb, one, zero)
    };
    let mut refuted = false;
    for x in 0_u128..1 << 16 {
        let env = [
            (row.a_lo, x & 15),
            (row.a_hi, (x >> 4) & 15),
            (row.b_lo, (x >> 8) & 15),
            (row.b_hi, x >> 12),
        ];
        let l = eval(&t, row.l, &env);
        assert_eq!(l, eval(&t, row.r, &env), "identity fails at {x:#06x}");
        refuted |= l != eval(&t, unguarded, &env);
    }
    assert!(refuted, "the unguarded variant must be refuted somewhere");
}

pub(super) fn clause_of(m: u32) -> (TermStore, TermId) {
    let (mut t, row) = row(m);
    let eq = t.eq(row.l, row.r);
    let mut store = TermStore::new();
    let id = to_store(&t, eq, &mut store);
    (store, id)
}

fn signed_row(m: u32) -> (Terms, signed::Signed) {
    let (t, sg, _) = signed_row_and_core(m);
    (t, sg)
}

fn signed_row_and_core(m: u32) -> (Terms, signed::Signed, Row) {
    let mut t = Terms::new();
    let leaves = Row::leaves(&mut t, m, ["a_lo", "a_hi", "b_lo", "b_hi"]);
    let (sg, core) = signed::Signed::new(&mut t, m, leaves);
    (t, sg, core)
}

fn signed_clause_of(m: u32) -> (TermStore, TermId) {
    let (mut t, sg) = signed_row(m);
    let eq = t.eq(sg.l, sg.r);
    let mut store = TermStore::new();
    let id = to_store(&t, eq, &mut store);
    (store, id)
}

/// The signed identity holds for every limb assignment at `m = 4` (every
/// pair of 8-bit operands, `MIN * -1` and division by zero included), and
/// the evaluator is not vacuous: dropping the `MIN * -1` disjunct is refuted.
#[test]
fn the_signed_identity_holds_for_every_four_bit_limb_assignment() {
    let (mut t, sg) = signed_row(4);
    let without_spec = {
        let (one, zero) = (t.lit(vec![true]), t.lit(vec![false]));
        t.ite(sg.first, one, zero)
    };
    let leaves = |t: &Terms| -> Vec<T> {
        ["a_lo", "a_hi", "b_lo", "b_hi"]
            .iter()
            .map(|name| {
                (0..t.len() as T)
                    .find(|&x| matches!(t.op(x), Op::Var(v) if &**v == *name))
                    .unwrap()
            })
            .collect()
    };
    let vars = leaves(&t);
    let mut refuted = false;
    for x in 0_u128..1 << 16 {
        let env: Vec<(T, u128)> = (0..4).map(|k| (vars[k], (x >> (4 * k)) & 15)).collect();
        let l = eval(&t, sg.l, &env);
        assert_eq!(l, eval(&t, sg.r, &env), "signed identity fails at {x:#06x}");
        refuted |= l != eval(&t, without_spec, &env);
    }
    assert!(refuted, "dropping MIN * -1 must be refuted somewhere");
}

#[test]
fn the_recognizer_accepts_the_identity_at_every_supported_width() {
    for m in [4, 6, 8, 64] {
        let (store, eq) = clause_of(m);
        assert!(recognize_mul_overflow_division(&store, &[eq]), "m = {m}");
        let (store, eq) = signed_clause_of(m);
        assert!(
            recognize_mul_overflow_division(&store, &[eq]),
            "signed m = {m}"
        );
    }
}

/// A signed identity whose limit ignores the signs (always `MAX`) is not
/// the identity, and the recognizer refuses it.
#[test]
fn the_recognizer_refuses_a_signed_row_with_the_wrong_limit() {
    let (mut t, sg, core) = signed_row_and_core(4);
    let lim = sg.maxw;
    let lo = sg.lo;
    let ovl = t.ult(lim, lo);
    let nhz = t.not(core.hz);
    let ov = t.or(&[nhz, ovl]);
    let (one, zero) = (t.lit(vec![true]), t.lit(vec![false]));
    let l = t.ite(ov, one, zero);
    let eq = t.eq(l, sg.r);
    let mut store = TermStore::new();
    let id = to_store(&t, eq, &mut store);
    assert!(!recognize_mul_overflow_division(&store, &[id]));
}

/// Negative controls: a mutated shape, an unsupported width, a repeated limb
/// and a wrong clause arity are all refused.
#[test]
fn the_recognizer_refuses_every_other_shape() {
    let (mut store, eq) = clause_of(4);
    assert!(!recognize_mul_overflow_division(&store, &[eq, eq]));
    assert!(!recognize_mul_overflow_division(&store, &[]));
    let not_eq = store.mk_not_raw(eq);
    assert!(!recognize_mul_overflow_division(&store, &[not_eq]));
    // The swapped equality is a different clause.
    let TermData::App(_, sides) = store.get(eq).clone() else {
        panic!("equality expected");
    };
    let swapped = store.mk_app(Symbol::named("="), [sides[1], sides[0]], Sort::Bool);
    assert!(!recognize_mul_overflow_division(&store, &[swapped]));
    // Odd and over-wide limbs.
    for m in [5, 66] {
        let (store, eq) = clause_of(m);
        assert!(!recognize_mul_overflow_division(&store, &[eq]), "m = {m}");
    }
    // A shifted carry by the wrong amount: rebuild with `m - 1` in the shift.
    let (mut t, row) = row(4);
    let wrong_shift = {
        let three = t.lit(bits::from_u64(3, 4));
        let shamt = t.zext(4, three);
        let cbx = t.zext(7, row.cb);
        let sh = t.mk(Op::Shl, &[cbx, shamt]);
        let xhe = t.extract(7, 4, row.mid);
        let xh = t.zext(4, xhe);
        let h1 = t.add(&[xh, row.phh]);
        let h = t.add(&[h1, sh]);
        let hz = t.eq(h, row.z);
        let nhz = t.not(hz);
        let (one, zero) = (t.lit(vec![true]), t.lit(vec![false]));
        let l = t.ite(nhz, one, zero);
        t.eq(l, row.r)
    };
    let mut store = TermStore::new();
    let id = to_store(&t, wrong_shift, &mut store);
    assert!(!recognize_mul_overflow_division(&store, &[id]));
    // One limb used twice.
    let mut t = Terms::new();
    let leaves = Row::leaves(&mut t, 4, ["a_lo", "a_hi", "a_lo", "b_hi"]);
    let row = Row::new(&mut t, 4, leaves);
    let eq = t.eq(row.l, row.r);
    let mut store = TermStore::new();
    let id = to_store(&t, eq, &mut store);
    assert!(!recognize_mul_overflow_division(&store, &[id]));
}

/// The printer lane emits the whole certificate ending in the lemma's own
/// step, with no hole and no trust anywhere in it.
#[test]
fn the_printer_lane_emits_a_complete_certificate() {
    let (store, eq) = clause_of(4);
    let printer = AlethePrinter::new(&store);
    let text = printer
        .format_mul_overflow_division(ProofId(7), &[eq])
        .expect("certificate");
    let last = text.lines().rev().find(|l| !l.is_empty()).unwrap();
    let spelled = printer.format_clause(&[eq]);
    assert!(
        last.starts_with(&format!("(step t7 {spelled} :rule ")),
        "{last}"
    );
    for rule in ["bitblast_udiv", "forall_inst", "poly_simp"] {
        assert!(text.contains(&format!(":rule {rule}")), "{rule}");
    }
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    assert!(text.contains("@ay_mo_t7_0_"));
    // Anything else keeps the hole.
    let not_eq = {
        let mut store = store.clone();
        let id = store.mk_not_raw(eq);
        (store, id)
    };
    let printer = AlethePrinter::new(&not_eq.0);
    assert!(printer
        .format_mul_overflow_division(ProofId(7), &[not_eq.1])
        .is_none());
}

/// A certificate is a function of its arguments, so the last one built is
/// served again for exactly those (the strict document scan and the export
/// each render the lemma), and built afresh for any other.
#[test]
fn the_last_certificate_is_served_again_for_exactly_its_arguments() {
    let key = |final_id: &str| CertificateKey {
        m: 4,
        names: ["a", "b", "c", "d"].map(str::to_string),
        prefix: "@ay_mo_t1_0_".to_string(),
        final_id: final_id.to_string(),
        clause: "(cl (= l r))".to_string(),
        signed: false,
    };
    let builds = std::cell::Cell::new(0);
    let build = |key: &CertificateKey| {
        builds.set(builds.get() + 1);
        Some(format!("text {}", key.final_id))
    };
    for _ in 0..2 {
        assert_eq!(
            remembered_certificate(key("t1"), build).as_deref(),
            Some("text t1")
        );
    }
    assert_eq!(builds.get(), 1);
    assert_eq!(
        remembered_certificate(key("t2"), build).as_deref(),
        Some("text t2")
    );
    assert_eq!(builds.get(), 2);
    // A build that declines is never remembered, and evicts nothing.
    assert_eq!(remembered_certificate(key("t3"), |_| None), None);
    assert_eq!(
        remembered_certificate(key("t2"), build).as_deref(),
        Some("text t2")
    );
    assert_eq!(builds.get(), 2);
}

/// The whole export, through every surface judge the printer runs over the
/// bytes it ships (`poly_simp`, `or`, resolution): the refutation of the
/// negated identity prints with no hole. A judge that cannot read a step
/// downgrades the whole lemma to `hole`, which no unit check of the
/// certificate text alone would notice.
#[test]
fn the_exported_refutation_survives_every_printed_surface_judge() {
    // `m = 8` also takes the byte-power shift lemmas of `m = 64`.
    for m in [4, 8] {
        exported_refutation_has_no_hole(clause_of(m), m);
    }
}

#[test]
fn the_exported_signed_refutation_survives_every_printed_surface_judge() {
    for m in [4, 8] {
        exported_refutation_has_no_hole(signed_clause_of(m), m);
    }
}

fn exported_refutation_has_no_hole((mut store, eq): (TermStore, TermId), m: u32) {
    let root = store.mk_not_raw(eq);
    let mut proof = ay_core::Proof::new();
    let premise = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "bv",
        vec![eq],
        ay_core::TheoryLemmaKind::BvMulOverflowDivision,
    );
    proof.add_resolution(Vec::new(), eq, premise, lemma);
    let text =
        crate::try_export_alethe_with_problem_scope_and_overrides(&proof, &store, &[root], None)
            .expect("export");
    assert!(
        !text.contains(":rule hole") && !text.contains(":rule trust"),
        "m = {m}"
    );
    assert!(text.contains(":rule bitblast_udiv"));
    assert!(text.contains(":rule poly_simp)"));
}

/// Negative control of the divider induction: the chain of stage-lemma
/// instances carries the invariant only along the checker's own divider.
/// Along the true stages it reaches `x` itself; with one remainder bit of one
/// stage flipped, no invariant follows and the chain is refused.
#[test]
fn the_divider_chain_refuses_a_wrong_stage() {
    let n = 4;
    let chain = |flip: bool| {
        let mut p = proof::Proof::new("t1.mo".into(), "@w".into());
        let ds = div::DivStage::new(&mut p, n, "@v").expect("stage lemma");
        let xb: Vec<T> = (0..n)
            .map(|i| p.t.var(&format!("x{i}"), GSort::Bool))
            .collect();
        let yb: Vec<T> = (0..n)
            .map(|i| p.t.var(&format!("y{i}"), GSort::Bool))
            .collect();
        let ff = p.t.ff;
        let zero_bits: Vec<T> = yb.iter().map(|&b| p.t.eq(b, ff)).collect();
        let yz = p.t.and(&zero_bits);
        let nyz = p.t.not(yz);
        let nz = p.assume(nyz);
        let mut stages = clean::udiv_stages(&mut p.t, &xb, &yb);
        if flip {
            let bit = stages[2].1[0];
            stages[2].1[0] = p.t.not(bit);
        }
        div_spec::division_spec_over(&mut p, &ds, &xb, &yb, nz, &stages).is_some()
    };
    assert!(chain(false), "the true stages carry the invariant");
    assert!(!chain(true), "a flipped stage must be refused");
}

/// The quantified division lemma is proved once over its own two words and
/// every use is an instance of it; it is proved only along the divider of its
/// own width: a stage lemma of another width carries no invariant, and the
/// lemma is refused.
#[test]
fn the_division_lemma_is_proved_only_along_its_own_divider() {
    let lemma = |stage_width: u32| {
        let mut p = proof::Proof::new("t1.mo".into(), "@w".into());
        let ds = div::DivStage::new(&mut p, stage_width, "@v").expect("stage lemma");
        div_lemma::DivLemma::new(&mut p, 4, &ds, "@u").map(|dl| (p, dl))
    };
    let (mut p, dl) = lemma(8).expect("the lemma over 8-bit words");
    let fact = p.clause(dl.fact).to_vec();
    assert!(matches!(fact[..], [f] if matches!(p.t.op(f), Op::Forall)));
    let x = p.t.var("x", GSort::Bv(8));
    let y = p.t.var("y", GSort::Bv(8));
    let split = dl.split_instance(&mut p, x, y).expect("instance");
    assert_eq!(p.clause(split).len(), 2, "(cl (not (not YZ)) (and ..))");
    assert!(
        lemma(6).is_none(),
        "a stage lemma of another width must be refused"
    );
}

#[path = "tests/cache_owner_tests.rs"]
mod cache_owner_tests;
