// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Validate affine index syntax without building unused address-bit circuits.
//! Normal forms choose a derivation; polynomial and subproof steps must still
//! be checked independently before a read-over-write equality is authoritative.

use super::*;
use ay_core::Constant;
use num_traits::ToPrimitive;

#[derive(Clone, Copy)]
struct Affine {
    base: Option<TermId>,
    offset: u128,
}

#[derive(Clone)]
pub(super) struct Address {
    pub(super) text: String,
    pub(super) width: usize,
    normal: Option<Affine>,
}

impl Address {
    pub(super) fn relation(&self, other: &Self) -> Option<bool> {
        let (a, b) = (self.normal?, other.normal?);
        (self.width == other.width && a.base == b.base).then_some(a.offset == b.offset)
    }
}

fn mask(width: usize) -> u128 {
    if width == 128 {
        u128::MAX
    } else {
        (1_u128 << width) - 1
    }
}

impl Circuit<'_, '_, '_> {
    pub(super) fn address(&mut self, term: TermId, depth: usize) -> Option<Address> {
        self.proof.printer.terms.entry_stamp(term)?;
        if let Some(address) = self.addresses.get(&term) {
            return Some(address.clone());
        }
        self.proof.enter(depth)?;
        let Sort::BitVec(sort) = self.proof.printer.terms.sort(term) else {
            return None;
        };
        let width = sort.width as usize;
        if width == 0 || width > MAX_WIDTH {
            return None;
        }
        let data = self.proof.printer.terms.get(term).clone();
        let normal = match &data {
            TermData::Var(..) => Some(Affine {
                base: Some(term),
                offset: 0,
            }),
            TermData::Const(Constant::BitVec {
                value,
                width: actual,
            }) => {
                let offset = value.to_u128()?;
                if *actual as usize != width || offset > mask(width) {
                    return None;
                }
                Some(Affine { base: None, offset })
            }
            TermData::App(Symbol::Named(op), args)
                if matches!(op.as_str(), "bvadd" | "bvsub") && args.len() == 2 =>
            {
                let a = self.address(args[0], depth + 1)?;
                let b = self.address(args[1], depth + 1)?;
                if a.width != width || b.width != width {
                    return None;
                }
                match (a.normal, b.normal) {
                    (Some(a), Some(b))
                        if op == "bvadd" && (a.base.is_none() || b.base.is_none()) =>
                    {
                        Some(Affine {
                            base: a.base.or(b.base),
                            offset: a.offset.wrapping_add(b.offset) & mask(width),
                        })
                    }
                    (Some(a), Some(b))
                        if op == "bvsub" && (b.base.is_none() || a.base == b.base) =>
                    {
                        Some(Affine {
                            base: if a.base == b.base { None } else { a.base },
                            offset: a.offset.wrapping_sub(b.offset) & mask(width),
                        })
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        // Validate every child before this check. An ancestor override cannot
        // conceal a changed constant or variable used by normalization.
        let text = self.proof.printer.format_term(term);
        if text != self.proof.printer.format_term_data(&data)
            || self.proof.printer.work_budget_exhausted()
        {
            return None;
        }
        if normal.is_none() {
            let word = self.word(term, depth)?;
            if word.equality.left != text || word.bits.len() != width {
                return None;
            }
        }
        let address = Address {
            text,
            width,
            normal,
        };
        self.addresses.insert(term, address.clone());
        Some(address)
    }

    pub(super) fn different_addresses(&mut self, a: &Address, b: &Address) -> Option<String> {
        if a.relation(b) != Some(false) {
            return None;
        }
        let delta = a.normal?.offset.wrapping_sub(b.normal?.offset) & mask(a.width);
        let constant = format!("(_ bv{delta} {})", a.width);
        let zero = format!("(_ bv0 {})", a.width);
        let difference = format!("(bvsub {} {})", a.text, b.text);
        let known = self
            .proof
            .equality(&difference, &constant, "poly_simp", &[])?;
        let not_false = self.proof.step("(not false)", "false", &[])?;
        let end = self.proof.fresh();
        let assumption = self.proof.fresh();
        let equal = format!("(= {} {})", a.text, b.text);
        self.proof.append(&format!(
            "(anchor :step {end})\n(assume {assumption} {equal})\n"
        ))?;
        let replace = Equality {
            left: a.text.clone(),
            right: b.text.clone(),
            step: assumption.clone(),
        };
        let keep = self.proof.equality(&b.text, &b.text, "refl", &[])?;
        let changed = self.proof.congruence("bvsub", &[replace, keep])?;
        let cancel = self
            .proof
            .equality(&changed.right, &zero, "poly_simp", &[])?;
        let vanished = self.proof.chain(changed, cancel)?;
        let reverse = self
            .proof
            .equality(&constant, &difference, "symm", &[&known.step])?;
        let impossible = self.proof.chain(reverse, vanished)?;
        let proposition = format!("(= {} {})", impossible.left, impossible.right);
        let evaluate = self
            .proof
            .equality(&proposition, "false", "evaluate", &[])?;
        let false_unit = self.proof.transport_unit(&evaluate, &impossible.step)?;
        self.proof
            .step("", "resolution", &[&false_unit, &not_false])?;
        self.proof.named_step(
            &end,
            &format!("(not {equal}) false"),
            "subproof",
            &[],
            &format!(" :discharge ({assumption})"),
        )?;
        self.proof
            .step(&format!("(not {equal})"), "resolution", &[&end, &not_false])
    }
}
