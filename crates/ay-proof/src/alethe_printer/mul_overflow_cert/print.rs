// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Alethe spelling of terms, with every compound term named once by a
//! proof-local `define-fun` (the checker inlines definitions at parse time).

use super::bits;
use super::term::{Op, Sort, Terms, T};
use ay_core::kani_compat::DetHashMap as HashMap;
use std::fmt::Write;

pub(crate) fn sort_str(s: Sort) -> String {
    match s {
        Sort::Bool => "Bool".into(),
        Sort::Bv(w) => format!("(_ BitVec {w})"),
    }
}

const B36: &[u8] = b"0123456789abcdefghijklmnopqrstuvwxyz";

pub(crate) fn b36(mut k: u64) -> String {
    let mut out = Vec::new();
    loop {
        out.push(B36[(k % 36) as usize]);
        k /= 36;
        if k == 0 {
            break;
        }
    }
    out.reverse();
    String::from_utf8(out).unwrap_or_default()
}

pub(crate) struct Printer {
    names: HashMap<T, Box<str>>,
    prefix: String,
    next: u64,
}

impl Printer {
    pub(crate) fn new(prefix: String) -> Self {
        Printer {
            names: HashMap::default(),
            prefix,
            next: 0,
        }
    }

    fn head(op: &Op) -> String {
        match op {
            Op::Not => "not".into(),
            Op::And => "and".into(),
            Op::Or => "or".into(),
            Op::Xor => "xor".into(),
            Op::Eq => "=".into(),
            Op::Ite => "ite".into(),
            Op::BbTerm => "@bbterm".into(),
            Op::BitOf(i) => format!("(_ @bit_of {i})"),
            Op::Add => "bvadd".into(),
            Op::Mul => "bvmul".into(),
            Op::Sub => "bvsub".into(),
            Op::Neg => "bvneg".into(),
            Op::Ult => "bvult".into(),
            Op::Concat => "concat".into(),
            Op::Extract(h, l) => format!("(_ extract {h} {l})"),
            Op::ZeroExt(k) => format!("(_ zero_extend {k})"),
            Op::Udiv => "bvudiv".into(),
            Op::Urem => "bvurem".into(),
            Op::Shl => "bvshl".into(),
            _ => String::new(),
        }
    }

    /// Spelling of `t` given the names already defined.
    pub(crate) fn render(&self, terms: &Terms, t: T) -> String {
        if let Some(n) = self.names.get(&t) {
            return n.to_string();
        }
        match terms.op(t) {
            Op::Var(name) => name.to_string(),
            Op::True => "true".into(),
            Op::False => "false".into(),
            Op::Lit(b) => bits::render(b),
            Op::Forall => {
                let args = terms.args(t);
                let (vars, body) = args.split_at(args.len().saturating_sub(1));
                let mut s = String::from("(forall (");
                for (k, &v) in vars.iter().enumerate() {
                    let sep = if k == 0 { "" } else { " " };
                    let _ = write!(
                        s,
                        "{sep}({} {})",
                        self.render(terms, v),
                        sort_str(terms.sort(v))
                    );
                }
                let b = body
                    .first()
                    .map_or(String::new(), |&b| self.render(terms, b));
                let _ = write!(s, ") {b})");
                s
            }
            op => {
                let mut s = format!("({}", Self::head(op));
                for &a in terms.args(t) {
                    s.push(' ');
                    s.push_str(&self.render(terms, a));
                }
                s.push(')');
                s
            }
        }
    }

    fn want_name(terms: &Terms, t: T) -> bool {
        !matches!(
            terms.op(t),
            Op::Var(_) | Op::True | Op::False | Op::Lit(_) | Op::Not
        )
    }

    /// Emit `define-fun`s (post-order) so that `t` prints compactly.
    pub(crate) fn ensure(&mut self, terms: &Terms, t: T, out: &mut String) {
        let mut stack = vec![(t, false)];
        while let Some((u, done)) = stack.pop() {
            if self.names.contains_key(&u) {
                continue;
            }
            if !done {
                stack.push((u, true));
                for &a in terms.args(u) {
                    if !self.names.contains_key(&a) {
                        stack.push((a, false));
                    }
                }
                continue;
            }
            if !Self::want_name(terms, u) {
                continue;
            }
            let body = self.render(terms, u);
            if body.len() > 12 {
                let name = format!("{}{}", self.prefix, b36(self.next));
                self.next += 1;
                let _ = writeln!(
                    out,
                    "(define-fun {name} () {} {body})",
                    sort_str(terms.sort(u))
                );
                self.names.insert(u, name.into());
            }
        }
    }
}
