// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constant and string-length bound computation.

use super::ArithEntail;
use ay_core::term::{Constant, TermData, TermId};

impl ArithEntail<'_> {
    pub(super) fn compute_constant_bound(&self, term: TermId, is_lower: bool) -> Option<i64> {
        if let Some(n) = self.state.resolve_int_constant(self.terms, term) {
            return Some(n);
        }

        let rep = self.state.find(term);
        if rep != term {
            if let Some(rep_bound) = self.get_constant_bound(rep, is_lower) {
                return Some(rep_bound);
            }
        }

        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => n.try_into().ok(),
            TermData::App(sym, args) if sym.name() == "str.len" && args.len() == 1 => {
                self.get_length_bound(args[0], is_lower)
            }
            TermData::App(sym, args) if sym.name() == "+" => {
                let mut total: i64 = 0;
                for &arg in args {
                    let bound = self.get_constant_bound(arg, is_lower)?;
                    total = total.checked_add(bound)?;
                }
                Some(total)
            }
            TermData::App(sym, args) if sym.name() == "-" => self.subtraction_bound(args, is_lower),
            TermData::App(sym, args) if sym.name() == "*" => {
                self.multiplication_bound(args, is_lower)
            }
            _ => None,
        }
    }

    fn subtraction_bound(&self, args: &[TermId], is_lower: bool) -> Option<i64> {
        match args.len() {
            0 => None,
            1 => self.get_constant_bound(args[0], !is_lower)?.checked_neg(),
            _ => {
                let mut total = self.get_constant_bound(args[0], is_lower)?;
                for &arg in &args[1..] {
                    let bound = self.get_constant_bound(arg, !is_lower)?;
                    total = total.checked_sub(bound)?;
                }
                Some(total)
            }
        }
    }

    fn multiplication_bound(&self, args: &[TermId], is_lower: bool) -> Option<i64> {
        if args.is_empty() {
            return Some(1);
        }

        // Exact product when all factors have exact bounds.
        let mut exact: i64 = 1;
        let mut all_exact = true;
        for &arg in args {
            match (
                self.get_constant_bound(arg, true),
                self.get_constant_bound(arg, false),
            ) {
                (Some(lb), Some(ub)) if lb == ub => {
                    exact = exact.checked_mul(lb)?;
                }
                _ => {
                    all_exact = false;
                    break;
                }
            }
        }
        if all_exact {
            return Some(exact);
        }

        // Conservative lower bound for products of non-negative factors.
        if !is_lower {
            return None;
        }
        let mut product: i64 = 1;
        for &arg in args {
            let lb = self.get_constant_bound(arg, true)?;
            if lb < 0 {
                return None;
            }
            product = product.checked_mul(lb)?;
        }
        Some(product)
    }

    pub(super) fn compute_length_bound(&self, s: TermId, is_lower: bool) -> Option<i64> {
        let rep = self.state.find(s);

        if let Some(known) = self.state.known_length(self.terms, rep) {
            return i64::try_from(known).ok();
        }
        if let Some(len_term) = self.state.get_length_term(&rep) {
            if let Some(n) = self.state.resolve_int_constant(self.terms, len_term) {
                if n >= 0 {
                    return Some(n);
                }
            }
        }
        if rep != s {
            if let Some(rep_bound) = self.get_length_bound(rep, is_lower) {
                return Some(rep_bound);
            }
        }

        let bound = match self.terms.get(s) {
            TermData::Const(Constant::String(text)) => i64::try_from(text.chars().count()).ok(),
            TermData::App(sym, args)
                if (sym.name() == "str.unit" || sym.name() == "seq.unit") && args.len() == 1 =>
            {
                Some(1)
            }
            TermData::App(sym, args) if sym.name() == "str.++" => {
                let mut sum = 0i64;
                for &child in args {
                    match self.get_length_bound(child, is_lower) {
                        Some(child_bound) => {
                            sum = sum.checked_add(child_bound)?;
                        }
                        None if is_lower => {}
                        None => return None,
                    }
                }
                Some(sum)
            }
            _ => None,
        };

        if is_lower {
            Some(bound.unwrap_or(0))
        } else {
            bound
        }
    }
}
