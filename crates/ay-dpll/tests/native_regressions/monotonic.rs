// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preserve the actual mono#2 core lowering, not a parsed equivalent.

use super::common::{self, Binding};
use ay_dpll::api::{FuncDecl, Solver, Sort, Term};

// This is a public Solver builder, not an SMT parser. The small tree keeps
// DeductiveChecks's left-to-right, right-associated && lowering and negation interning.
#[derive(Clone)]
enum E {
    V(usize),
    N(i64),
    Sub(Box<E>, Box<E>),
    Eq(Box<E>, Box<E>),
    Le(Box<E>, Box<E>),
    Lt(Box<E>, Box<E>),
    And(Vec<E>),
    Not(Box<E>),
    Implies(Box<E>, Box<E>),
    Ite(Box<E>, Box<E>, Box<E>),
    Call(usize, Box<E>),
}
fn v(i: usize) -> E {
    E::V(i)
}
fn n(i: i64) -> E {
    E::N(i)
}
fn sub(a: E, b: E) -> E {
    E::Sub(Box::new(a), Box::new(b))
}
fn eq(a: E, b: E) -> E {
    E::Eq(Box::new(a), Box::new(b))
}
fn le(a: E, b: E) -> E {
    E::Le(Box::new(a), Box::new(b))
}
fn lt(a: E, b: E) -> E {
    E::Lt(Box::new(a), Box::new(b))
}
fn not(a: E) -> E {
    E::Not(Box::new(a))
}
fn implies(a: E, b: E) -> E {
    E::Implies(Box::new(a), Box::new(b))
}
fn ite(a: E, b: E, c: E) -> E {
    E::Ite(Box::new(a), Box::new(b), Box::new(c))
}
fn call(f: usize, a: E) -> E {
    E::Call(f, Box::new(a))
}
fn small() -> E {
    E::And(vec![lt(v(0), n(2)), lt(v(1), n(2))])
}
fn previous() -> E {
    sub(v(1), n(1))
}
fn guard(last: E) -> E {
    E::And(vec![not(small()), not(eq(v(0), v(1))), last])
}
fn clipped() -> E {
    ite(le(n(0), previous()), previous(), call(0, previous()))
}

fn encode_and(xs: &[E], s: &mut Solver, vs: &[Term], fs: &[FuncDecl]) -> Term {
    let Some((first, rest)) = xs.split_first() else {
        return s.bool_const(true);
    };
    let left = encode(first, s, vs, fs);
    if rest.is_empty() {
        return left;
    }
    let _not_left = s.try_not(left).unwrap();
    let right = encode_and(rest, s, vs, fs);
    let no = s.bool_const(false);
    s.try_ite(left, right, no).unwrap()
}

fn encode(e: &E, s: &mut Solver, vs: &[Term], fs: &[FuncDecl]) -> Term {
    match e {
        E::V(i) => vs[*i],
        E::N(i) => s.int_const(*i),
        E::Sub(a, b) | E::Eq(a, b) | E::Le(a, b) | E::Lt(a, b) => {
            let a = encode(a, s, vs, fs);
            let b = encode(b, s, vs, fs);
            match e {
                E::Sub(..) => s.try_sub(a, b).unwrap(),
                E::Eq(..) => s.try_eq(a, b).unwrap(),
                E::Le(..) => s.try_le(a, b).unwrap(),
                E::Lt(..) => s.try_lt(a, b).unwrap(),
                _ => unreachable!(),
            }
        }
        E::And(xs) => encode_and(xs, s, vs, fs),
        E::Not(a) => {
            let a = encode(a, s, vs, fs);
            s.try_not(a).unwrap()
        }
        E::Implies(a, b) => {
            let a = encode(a, s, vs, fs);
            let _not_a = s.try_not(a).unwrap();
            let b = encode(b, s, vs, fs);
            s.try_implies(a, b).unwrap()
        }
        E::Ite(c, a, b) => {
            let c = encode(c, s, vs, fs);
            let _not_c = s.try_not(c).unwrap();
            let a = encode(a, s, vs, fs);
            let b = encode(b, s, vs, fs);
            s.try_ite(c, a, b).unwrap()
        }
        E::Call(f, a) => {
            let a = encode(a, s, vs, fs);
            s.try_apply(&fs[*f], &[a]).unwrap()
        }
    }
}

fn query(binding: Binding) -> Solver {
    let mut s = common::solver();
    let vs: Vec<Term> = (0..5)
        .map(|i| s.try_declare_const(&format!("v{i}"), Sort::Int).unwrap())
        .collect();
    for name in ["nl_mul", "nl_div", "nl_mod"] {
        s.try_declare_fun(name, &[Sort::Int, Sort::Int], Sort::Int)
            .unwrap();
    }
    let mut clip_nat = None;
    for name in [
        "clip_u8_oob",
        "clip_u16_oob",
        "clip_u32_oob",
        "clip_u64_oob",
        "clip_i8_oob",
        "clip_i16_oob",
        "clip_i32_oob",
        "clip_i64_oob",
        "clip_nat_oob",
    ] {
        let f = s.try_declare_fun(name, &[Sort::Int], Sort::Int).unwrap();
        if name == "clip_nat_oob" {
            clip_nat = Some(f);
        }
    }
    let sf0 = s.try_declare_fun("sf0", &[Sort::Int], Sort::Int).unwrap();
    s.try_declare_fun("rf0", &[Sort::Int], Sort::Int).unwrap();
    s.try_declare_fun("sf1", &[], Sort::Int).unwrap();
    let fs = [clip_nat.unwrap(), sf0];
    let hypotheses = vec![
        le(n(0), v(0)),
        le(n(0), v(1)),
        le(v(0), v(1)),
        eq(v(2), sub(v(1), v(0))),
        le(n(0), v(3)),
        implies(guard(eq(v(0), previous())), eq(v(3), clipped())),
        implies(
            guard(eq(v(0), previous())),
            le(call(1, v(0)), call(1, v(3))),
        ),
        le(n(0), v(4)),
        implies(guard(not(eq(v(0), previous()))), eq(v(4), clipped())),
        not(small()),
        not(eq(v(0), v(1))),
        not(eq(v(0), previous())),
        le(n(0), call(0, previous())),
        le(n(0), call(1, v(0))),
        le(n(0), call(1, v(3))),
    ];
    for (i, h) in hypotheses.iter().enumerate() {
        let term = encode(h, &mut s, &vs, &fs);
        // The SAT twin removes just the authored v2 = v1 - v0 binding.
        if !(matches!(binding, Binding::Omitted) && i == 3) {
            s.try_assert_named(term, &format!("qh{i}")).unwrap();
        }
    }
    // Refuting And(Le(0,v4-v0), Lt(v4-v0,v2)) inverts comparisons first
    // and uses direct try_or, as encode_refutation_expr does.
    let zero = s.int_const(0);
    let diff = encode(&sub(v(4), v(0)), &mut s, &vs, &fs);
    let a = s.try_gt(zero, diff).unwrap();
    let diff = encode(&sub(v(4), v(0)), &mut s, &vs, &fs);
    let b = s.try_ge(diff, vs[2]).unwrap();
    let counterexample = s.try_or(a, b).unwrap();
    s.try_assert_term(counterexample).unwrap();
    s
}

#[test]
fn native_arithmetic_ite_decrease_unsat() {
    common::on_solver_stack(|| common::assert_unsat(query(Binding::Original)));
}

#[test]
fn native_arithmetic_ite_decrease_omitted_binding_sat() {
    common::on_solver_stack(|| common::assert_sat(query(Binding::Omitted)));
}
