// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic clause-validity oracle for Theorem 1 (precondition P2).
//!
//! For small queries, every assignment of the declared constants and of the
//! wrong-constructor values `tl(nil)`, `hd(nil)` over a finite universe
//! (lists of length <= 3 over a 2-letter alphabet) is enumerated. For each
//! assignment `M` that satisfies the query, the CNF plus the CONTENT bits of
//! `M` (every constant's and shared value's cells fixed to what `M` says)
//! must be satisfiable — exactly the statement "every model of φ extends to
//! a model of `E_D(φ)`" that Theorem 1's proof constructs. An over-strong
//! clause in any schema (including the shared equality and mux helpers)
//! makes some such check UNSAT. `D` ranges over 1 and 2, below the length
//! of the longest enumerated list, so deep values are exercised.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::TermId;
use ay_frontend::parse;
use ay_sat::{Literal, SatResult, Solver as SatSolver, Variable};
use ntest::timeout;

use super::super::cnf::Lit;
use super::super::decode::{Decoder, VNode};
use super::super::encode::Encoder;
use super::super::guards::{alias_map, guarded_selectors};
use super::super::scan::{FieldSort, Node, Scan, SortShape};
use super::super::values::Val;
use crate::Executor;

const HEADER: &str = "(set-logic QF_DT)\n(declare-datatypes ((E 0) (L 0)) (((A) (B)) \
                      ((cons (hd E) (tl L)) (nil))))\n\
                      (declare-datatypes ((R 0)) (((mk (lf L) (fl Bool)))))\n";

/// All lists of length <= 3 over {A, B}, as interned values.
fn lists(dec: &mut Decoder<'_, '_>, sort: u32, e: u32) -> Vec<u32> {
    let mut out = vec![dec.nil_of(sort).unwrap_or(0)];
    let mut frontier = out.clone();
    for _ in 0..3 {
        let mut next = Vec::new();
        for &tail in &frontier {
            for c in 0..2 {
                let head = dec.enum_value(e, c);
                next.push(dec.values.intern(VNode::Ctor {
                    sort,
                    ctor: 0,
                    args: vec![head, tail],
                }));
            }
        }
        out.extend(&next);
        frontier = next;
    }
    out
}

/// Content units of `value` under the encoded value `v` (cells beyond `D`
/// are simply not described).
fn units(dec: &Decoder<'_, '_>, v: &Val, value: u32, out: &mut Vec<Lit>) {
    let node = dec.values.get(value).cloned();
    match (v, node) {
        (Val::Bool(l), Some(VNode::Bool(b))) => out.push(if b { *l } else { -*l }),
        (Val::Enum(row), Some(VNode::Ctor { ctor, .. })) => {
            for (i, &l) in row.iter().enumerate() {
                out.push(if i as u32 == ctor { l } else { -l });
            }
        }
        (Val::Record(fields), Some(VNode::Ctor { args, .. })) => {
            for (f, a) in fields.iter().zip(args) {
                units(dec, f, a, out);
            }
        }
        (Val::List(cells), Some(_)) => {
            let mut cur = value;
            for cell in cells.iter() {
                match dec.values.get(cur).cloned() {
                    Some(VNode::Ctor { ctor: 0, args, .. }) => {
                        out.push(cell.s);
                        let Some(VNode::Ctor { ctor: c, .. }) = dec.values.get(args[0]).cloned()
                        else {
                            return;
                        };
                        for (i, &l) in cell.rows[0].iter().enumerate() {
                            out.push(if i as u32 == c { l } else { -l });
                        }
                        cur = args[1];
                    }
                    _ => {
                        out.push(-cell.s);
                        out.extend(cell.rows[0].iter().map(|&l| -l));
                    }
                }
            }
        }
        _ => {}
    }
}

fn cnf_sat_with(enc: &Encoder<'_>, extra: &[Lit]) -> bool {
    let to = |l: i32| {
        let v = Variable::new(l.unsigned_abs() - 1);
        if l > 0 {
            Literal::positive(v)
        } else {
            Literal::negative(v)
        }
    };
    let mut solver = SatSolver::new(enc.cnf.num_vars() as usize);
    let mut buf = Vec::new();
    for &l in enc.cnf.flat_literals() {
        if l == 0 {
            solver.add_clause(std::mem::take(&mut buf));
        } else {
            buf.push(to(l));
        }
    }
    for &l in extra {
        if l.abs() != 1 {
            solver.add_clause(vec![to(l)]);
        } else if l == -1 {
            return false;
        }
    }
    matches!(
        solver.solve_interruptible(|| false).into_inner(),
        SatResult::Sat(_)
    )
}

fn list_sort(scan: &Scan) -> Option<(u32, u32)> {
    scan.sorts
        .iter()
        .enumerate()
        .find_map(|(i, s)| match &s.shape {
            SortShape::List { cell_fields, .. } => Some((i as u32, cell_fields[0])),
            _ => None,
        })
}

/// Check every model of `body` (over the enumerated universe) at cell count `d`.
fn check(body: &str, d: usize) -> usize {
    let commands = parse(&format!("{HEADER}{body}\n")).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();
    let scan = exec.dt_fd_scan().expect("query must be in the fragment");
    let (alias, (guarded, _)) = (alias_map(&scan), guarded_selectors(&scan));
    let mut enc = Encoder::new(&scan, d, 1 << 22, &alias, &guarded);
    enc.encode().expect("encodes");
    let consts: Vec<(TermId, FieldSort)> = scan
        .order
        .iter()
        .filter_map(|&t| match scan.nodes.get(&t) {
            Some((Node::Const, s)) => Some((t, *s)),
            _ => None,
        })
        .collect();
    let empty: Vec<bool> = Vec::new();
    let mut dec = Decoder::new(&enc, &empty);
    let (ls, es) = list_sort(&scan).expect("a list sort");
    let list_vals = lists(&mut dec, ls, es);
    let domain = |s: FieldSort, dec: &mut Decoder<'_, '_>| -> Vec<u32> {
        match s {
            FieldSort::Bool => vec![
                dec.values.intern(VNode::Bool(false)),
                dec.values.intern(VNode::Bool(true)),
            ],
            FieldSort::Dt(i) if i == ls => list_vals.clone(),
            FieldSort::Dt(i) => match scan.sorts[i as usize].shape {
                SortShape::Record { .. } => {
                    let mut out = Vec::new();
                    for &l in &list_vals {
                        for b in [false, true] {
                            let b = dec.values.intern(VNode::Bool(b));
                            out.push(dec.values.intern(VNode::Ctor {
                                sort: i,
                                ctor: 0,
                                args: vec![l, b],
                            }));
                        }
                    }
                    out
                }
                _ => (0..2).map(|c| dec.enum_value(i, c)).collect(),
            },
        }
    };
    let mut axes: Vec<Vec<u32>> = consts.iter().map(|&(_, s)| domain(s, &mut dec)).collect();
    axes.push(list_vals[..7].to_vec()); // tl(nil)
    axes.push((0..2).map(|c| dec.enum_value(es, c)).collect()); // hd(nil)
    let total: usize = axes.iter().map(Vec::len).product();
    let mut models = 0;
    for mut k in 0..total {
        let pick: Vec<u32> = axes
            .iter()
            .map(|a| {
                let v = a[k % a.len()];
                k /= a.len();
                v
            })
            .collect();
        dec.fixed_consts = consts
            .iter()
            .zip(&pick)
            .map(|(&(t, _), &v)| (t, v))
            .collect();
        dec.fixed_rest = HashMap::from_iter([(ls, pick[consts.len()])]);
        dec.fixed_field = HashMap::from_iter([((ls, 0), pick[consts.len() + 1])]);
        if dec.evaluate().is_none() {
            continue;
        }
        models += 1;
        let mut extra = Vec::new();
        for (&(t, _), &v) in consts.iter().zip(&pick) {
            units(&dec, &enc.vals[&t], v, &mut extra);
        }
        if let Some(rn) = enc.shared_rest.get(&ls) {
            units(&dec, rn, pick[consts.len()], &mut extra);
        }
        if let Some(fnil) = enc.shared_field.get(&(ls, 0)) {
            units(&dec, fnil, pick[consts.len() + 1], &mut extra);
        }
        assert!(
            cnf_sat_with(&enc, &extra),
            "a model of the query does not extend to the CNF (D = {d}):\n{body}"
        );
    }
    models
}

const QUERIES: &[&str] = &[
    // Wrong-constructor selectors and deep self-reference through tl(nil).
    "(declare-const x L) (declare-const y L)\n\
     (assert (or ((_ is nil) x) (= (tl x) (cons A y))))\n\
     (assert (= (tl (tl x)) y)) (assert (not (= (hd y) (hd (tl y)))))",
    // Guarded selectors (Lemma 4) under ite and and, with deep equalities.
    "(declare-const x L) (declare-const y L)\n\
     (assert (ite (and ((_ is cons) x) (= (hd x) A)) (= y (tl x)) (= y (cons B x))))\n\
     (assert (or (and ((_ is cons) y) (= (hd y) B)) (distinct x y)))",
    // DT-sorted ite, distinct, xor and implication.
    "(declare-const x L) (declare-const y L) (declare-const b Bool)\n\
     (assert (= x (ite b (cons A y) (tl y))))\n\
     (assert (xor b (distinct x y (cons B nil))))\n\
     (assert (=> ((_ is cons) x) (= (hd x) (hd y))))",
    // Records with a Bool field and record equality.
    "(declare-const r R) (declare-const x L)\n\
     (assert (= r (mk (tl x) (= x (cons A nil)))))\n\
     (assert (or (fl r) (= (lf r) x)))",
    // A domain-closure root (left unasserted) next to guarded selectors.
    "(declare-const x L) (declare-const y L)\n\
     (assert (or (= (hd x) A) (= B (hd x))))\n\
     (assert (ite (and ((_ is cons) x) (= (hd x) A)) (= y (tl x)) (= y (cons B x))))",
    // Unguarded field selector on a possibly-nil argument.
    "(declare-const x L) (declare-const y L)\n\
     (assert (= (hd x) (hd (tl y)))) (assert (distinct (tl x) y))",
];

#[test]
#[timeout(300000)]
fn every_model_extends_to_a_cnf_model_at_tiny_cell_counts() {
    for q in QUERIES {
        for d in [1, 2] {
            let n = check(q, d);
            assert!(n > 0, "the oracle saw no model of:\n{q}");
        }
    }
}
