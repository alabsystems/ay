// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A hash-consed term DAG with exactly the term shapes the pinned checker
//! builds, so a printed term and the checker's own construction coincide.

use ay_core::kani_compat::DetHashMap as HashMap;

pub(crate) type T = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Sort {
    Bool,
    Bv(u32),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Op {
    Var(Box<str>),
    True,
    False,
    /// A bit-vector literal, least significant bit first.
    Lit(Box<[bool]>),
    Not,
    And,
    Or,
    Xor,
    Eq,
    Ite,
    BbTerm,
    BitOf(u32),
    Add,
    Mul,
    Sub,
    Neg,
    Ult,
    Concat,
    Extract(u32, u32),
    ZeroExt(u32),
    Udiv,
    Urem,
    Shl,
    /// `(forall (vars..) body)`: the arguments are the bound variables then the body.
    Forall,
}

pub(crate) struct Terms {
    ops: Vec<Op>,
    args: Vec<Box<[T]>>,
    sorts: Vec<Sort>,
    index: HashMap<(Op, Box<[T]>), T>,
    pub(crate) tt: T,
    pub(crate) ff: T,
}

impl Terms {
    pub(crate) fn new() -> Self {
        let mut terms = Terms {
            ops: Vec::new(),
            args: Vec::new(),
            sorts: Vec::new(),
            index: HashMap::default(),
            tt: 0,
            ff: 0,
        };
        terms.tt = terms.mk_sorted(Op::True, &[], Sort::Bool);
        terms.ff = terms.mk_sorted(Op::False, &[], Sort::Bool);
        terms
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.ops.len()
    }

    pub(crate) fn op(&self, t: T) -> &Op {
        &self.ops[t as usize]
    }

    pub(crate) fn args(&self, t: T) -> &[T] {
        &self.args[t as usize]
    }

    pub(crate) fn sort(&self, t: T) -> Sort {
        self.sorts[t as usize]
    }

    /// Width of a bit-vector term (0 for a Boolean one).
    pub(crate) fn width(&self, t: T) -> u32 {
        match self.sort(t) {
            Sort::Bv(w) => w,
            Sort::Bool => 0,
        }
    }

    pub(crate) fn mk_sorted(&mut self, op: Op, args: &[T], sort: Sort) -> T {
        let key = (op, args.to_vec().into_boxed_slice());
        if let Some(&t) = self.index.get(&key) {
            return t;
        }
        let t = self.ops.len() as T;
        self.ops.push(key.0.clone());
        self.args.push(key.1.clone());
        self.sorts.push(sort);
        self.index.insert(key, t);
        t
    }

    fn infer(&self, op: &Op, args: &[T]) -> Sort {
        match op {
            Op::Lit(bits) => Sort::Bv(bits.len() as u32),
            Op::BbTerm => Sort::Bv(args.len() as u32),
            Op::Ite => args.get(1).map_or(Sort::Bool, |&a| self.sort(a)),
            Op::Add | Op::Mul | Op::Sub | Op::Neg | Op::Udiv | Op::Urem | Op::Shl => {
                args.first().map_or(Sort::Bool, |&a| self.sort(a))
            }
            Op::Concat => Sort::Bv(args.iter().map(|&a| self.width(a)).sum()),
            Op::Extract(hi, lo) => Sort::Bv(hi - lo + 1),
            Op::ZeroExt(k) => Sort::Bv(args.first().map_or(0, |&a| self.width(a)) + k),
            _ => Sort::Bool,
        }
    }

    pub(crate) fn mk(&mut self, op: Op, args: &[T]) -> T {
        let sort = self.infer(&op, args);
        self.mk_sorted(op, args, sort)
    }

    pub(crate) fn var(&mut self, name: &str, sort: Sort) -> T {
        self.mk_sorted(Op::Var(name.into()), &[], sort)
    }
    pub(crate) fn not(&mut self, a: T) -> T {
        self.mk(Op::Not, &[a])
    }
    pub(crate) fn and(&mut self, a: &[T]) -> T {
        self.mk(Op::And, a)
    }
    pub(crate) fn or(&mut self, a: &[T]) -> T {
        self.mk(Op::Or, a)
    }
    pub(crate) fn xor(&mut self, a: T, b: T) -> T {
        self.mk(Op::Xor, &[a, b])
    }
    pub(crate) fn eq(&mut self, a: T, b: T) -> T {
        self.mk(Op::Eq, &[a, b])
    }
    pub(crate) fn ite(&mut self, c: T, a: T, b: T) -> T {
        self.mk(Op::Ite, &[c, a, b])
    }
    pub(crate) fn bb(&mut self, bits: &[T]) -> T {
        self.mk(Op::BbTerm, bits)
    }
    pub(crate) fn bit_of(&mut self, i: u32, w: T) -> T {
        self.mk(Op::BitOf(i), &[w])
    }
    pub(crate) fn add(&mut self, a: &[T]) -> T {
        self.mk(Op::Add, a)
    }
    pub(crate) fn mul(&mut self, a: T, b: T) -> T {
        self.mk(Op::Mul, &[a, b])
    }
    pub(crate) fn sub(&mut self, a: T, b: T) -> T {
        self.mk(Op::Sub, &[a, b])
    }
    pub(crate) fn neg(&mut self, a: T) -> T {
        self.mk(Op::Neg, &[a])
    }
    pub(crate) fn ult(&mut self, a: T, b: T) -> T {
        self.mk(Op::Ult, &[a, b])
    }
    pub(crate) fn concat(&mut self, a: &[T]) -> T {
        self.mk(Op::Concat, a)
    }
    pub(crate) fn extract(&mut self, hi: u32, lo: u32, a: T) -> T {
        self.mk(Op::Extract(hi, lo), &[a])
    }
    pub(crate) fn zext(&mut self, k: u32, a: T) -> T {
        self.mk(Op::ZeroExt(k), &[a])
    }
    pub(crate) fn lit(&mut self, bits: Vec<bool>) -> T {
        self.mk(Op::Lit(bits.into_boxed_slice()), &[])
    }
    pub(crate) fn forall(&mut self, vars: &[T], body: T) -> T {
        let mut a = vars.to_vec();
        a.push(body);
        self.mk(Op::Forall, &a)
    }

    /// The checker's `get_term_bits`: an `@bbterm`'s own arguments, otherwise
    /// one `@bit_of` projection per bit.
    pub(crate) fn bits(&mut self, t: T) -> Vec<T> {
        if matches!(self.op(t), Op::BbTerm) {
            return self.args(t).to_vec();
        }
        (0..self.width(t)).map(|i| self.bit_of(i, t)).collect()
    }

    /// Strip negations: the atom and its polarity.
    pub(crate) fn lit_of(&self, mut t: T) -> (T, bool) {
        let mut pol = true;
        while matches!(self.op(t), Op::Not) {
            t = self.args(t)[0];
            pol = !pol;
        }
        (t, pol)
    }

    pub(crate) fn is_gate(&self, t: T) -> bool {
        matches!(self.op(t), Op::And | Op::Or | Op::Xor | Op::Ite)
            || (matches!(self.op(t), Op::Eq) && self.sort(self.args(t)[0]) == Sort::Bool)
    }
}
