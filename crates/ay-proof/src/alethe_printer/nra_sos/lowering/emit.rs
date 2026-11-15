// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The step writer of the SOS lowering. Every `la_generic` and `poly_simp` it
//! writes is first replayed by the printer's own pinned-checker judgements
//! (`la_generic_surface`) over the exact text it ships, and every
//! `la_generic` must also refute its hypotheses over the reals WITHOUT the
//! pinned checker's sort-blind strengthening; a step that fails either
//! refuses the whole lowering, which leaves the honest `hole`.

use crate::alethe_printer::la_generic_surface::readings::{
    printed_la_generic_atom_residual, printed_la_generic_is_real_contradiction, printed_polynomial,
};
use crate::alethe_printer::la_generic_surface::{
    printed_la_generic_holds, printed_poly_simp_holds,
};
use crate::alethe_printer::AlethePrinter;
use ay_core::{Constant, RationalWrapper};
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;
use std::fmt::Write as _;

#[cfg(test)]
mod tests;

/// Past this many bytes the lowering refuses and the step stays a `hole`.
const MAX_LOWERED_BYTES: usize = 16 * 1024 * 1024;

/// Which pinned multiplication rule scales a comparison.
#[derive(Clone, Copy)]
pub(super) enum Multiplier {
    /// `la_mult_pos`: `m > 0` keeps the relation.
    Positive,
    /// `la_mult_neg`: `m < 0` flips it.
    Negative,
}

/// One written `la_generic` step: its id and the `poly_simp` ids it cites.
pub(super) struct LaGeneric {
    pub(super) name: String,
    pub(super) equalities: Vec<String>,
}

pub(super) struct Emitter {
    prefix: String,
    real: bool,
    next: usize,
    out: String,
    /// One `poly_simp` normal form per opaque atom, shared by every step.
    equalities: BTreeMap<String, String>,
}

/// `(not X)`.
pub(super) fn negated(literal: &str) -> String {
    format!("(not {literal})")
}

/// A pinned `la_generic` coefficient: `n`, `(- n)`, `(/ n.0 d.0)` or
/// `(- (/ n.0 d.0))`.
fn format_arg(value: &BigRational) -> String {
    let magnitude = value.abs();
    let text = if magnitude.is_integer() {
        magnitude.numer().to_string()
    } else {
        format!("(/ {}.0 {}.0)", magnitude.numer(), magnitude.denom())
    };
    if value.is_negative() {
        format!("(- {text})")
    } else {
        text
    }
}

impl Emitter {
    pub(super) fn new(prefix: String, real: bool) -> Self {
        Self {
            prefix,
            real,
            next: 0,
            out: String::new(),
            equalities: BTreeMap::new(),
        }
    }

    pub(super) fn finish(self) -> String {
        self.out
    }

    fn name(&mut self, tag: &str) -> String {
        let name = format!("{}.{tag}{}", self.prefix, self.next);
        self.next += 1;
        name
    }

    pub(super) fn push(&mut self, line: &str) -> Option<()> {
        if self.out.len().saturating_add(line.len()) >= MAX_LOWERED_BYTES {
            return None;
        }
        self.out.push_str(line);
        self.out.push('\n');
        Some(())
    }

    /// A constant in the lowering's one arithmetic sort, spelled exactly as
    /// the printer spells that sort's constants.
    pub(super) fn numeral(&self, value: &BigRational) -> Option<String> {
        if self.real {
            Some(AlethePrinter::format_constant(&Constant::Rational(
                RationalWrapper(value.clone()),
            )))
        } else {
            value
                .is_integer()
                .then(|| AlethePrinter::format_constant(&Constant::Int(value.to_integer())))
        }
    }

    pub(super) fn zero(&self) -> String {
        if self.real { "0.0" } else { "0" }.to_string()
    }

    pub(super) fn one(&self) -> String {
        if self.real { "1.0" } else { "1" }.to_string()
    }

    /// The pinned `poly_simp` normal form of `atom`, spelled over the atoms
    /// `la_generic` reads: a monomial of degree one is its atom, a higher one
    /// is one flat `(* a b ..)`. Normal forms are fixed points, so atoms of
    /// two different spellings of one monomial meet in one `la_generic` atom.
    fn normal_form(&self, atom: &str) -> Option<String> {
        let (monomials, constant) = printed_polynomial(atom)?;
        let mut parts = Vec::with_capacity(monomials.len() + 1);
        if !constant.is_zero() {
            parts.push(self.numeral(&constant)?);
        }
        for (monomial, coefficient) in &monomials {
            let product = match monomial.as_slice() {
                [single] => single.clone(),
                _ => format!("(* {})", monomial.join(" ")),
            };
            parts.push(if coefficient.is_one() {
                product
            } else if (-coefficient).is_one() {
                format!("(- {product})")
            } else {
                format!("(* {} {product})", self.numeral(coefficient)?)
            });
        }
        match parts.len() {
            0 => Some(self.zero()),
            1 => parts.pop(),
            _ => Some(format!("(+ {})", parts.join(" "))),
        }
    }

    /// The `poly_simp` step proving `(= atom normal)`, written once.
    fn equality(&mut self, atom: &str, normal: &str) -> Option<String> {
        if let Some(name) = self.equalities.get(atom) {
            return Some(name.clone());
        }
        if printed_poly_simp_holds(atom, normal) != Some(true) {
            return None;
        }
        let name = self.name("e");
        self.push(&format!(
            "(step {name} (cl (= {atom} {normal})) :rule poly_simp)"
        ))?;
        self.equalities.insert(atom.to_string(), name.clone());
        Some(name)
    }

    /// Write `la_generic` over `(literal, coefficient)` rows. Every opaque
    /// atom the rows leave uncancelled that is not already in normal form is
    /// rewritten by one `poly_simp` equality row; the step is written only if
    /// the pinned replay accepts the exact text.
    pub(super) fn la_generic(&mut self, rows: Vec<(String, BigRational)>) -> Option<LaGeneric> {
        let mut merged: Vec<(String, BigRational)> = Vec::with_capacity(rows.len());
        for (literal, coefficient) in rows {
            match merged.iter_mut().find(|(seen, _)| *seen == literal) {
                Some((_, existing)) => *existing += coefficient,
                None => merged.push((literal, coefficient)),
            }
        }
        let literals: Vec<&str> = merged.iter().map(|(literal, _)| literal.as_str()).collect();
        let coefficients: Vec<BigRational> = merged.iter().map(|(_, c)| c.clone()).collect();
        let residual = printed_la_generic_atom_residual(&literals, &coefficients)?;
        let mut equalities = Vec::new();
        for (atom, coefficient) in residual {
            let normal = self.normal_form(&atom)?;
            if normal == atom {
                continue;
            }
            equalities.push(self.equality(&atom, &normal)?);
            merged.push((negated(&format!("(= {atom} {normal})")), -coefficient));
        }
        let literals: Vec<&str> = merged.iter().map(|(literal, _)| literal.as_str()).collect();
        let coefficients: Vec<BigRational> = merged.iter().map(|(_, c)| c.clone()).collect();
        let args: Vec<String> = coefficients.iter().map(format_arg).collect();
        let arg_refs: Vec<&str> = args.iter().map(String::as_str).collect();
        // Both: the pinned checker must accept the exact text, and the step
        // must be a theorem over the reals on its own, not only through the
        // checker's integer strengthening (which it applies to `Real` rows).
        if !printed_la_generic_holds(&literals, &arg_refs)
            || !printed_la_generic_is_real_contradiction(&literals, &coefficients)
        {
            return None;
        }
        let name = self.name("g");
        self.push(&format!(
            "(step {name} (cl {}) :rule la_generic :args ({}))",
            literals.join(" "),
            args.join(" ")
        ))?;
        Some(LaGeneric { name, equalities })
    }

    /// `(cl (not cond) (not orig) scaled)` from the pinned multiplication
    /// axiom `(=> (and cond orig) scaled)`, `implies_pos`, `and_neg` and one
    /// resolution. The caller spells `scaled` as the rule's exact image of
    /// `orig`; the rule itself is purely syntactic.
    pub(super) fn multiply(
        &mut self,
        multiplier: Multiplier,
        cond: &str,
        orig: &str,
        scaled: &str,
    ) -> Option<String> {
        let implication = format!("(=> (and {cond} {orig}) {scaled})");
        let axiom = self.name("m");
        match multiplier {
            Multiplier::Positive => self.push(&format!(
                "(step {axiom} (cl {implication}) :rule la_mult_pos)"
            ))?,
            Multiplier::Negative => self.push(&format!(
                "(step {axiom} (cl {implication}) :rule la_mult_neg)"
            ))?,
        }
        let unfolded = self.name("i");
        self.push(&format!(
            "(step {unfolded} (cl {} (not (and {cond} {orig})) {scaled}) :rule implies_pos)",
            negated(&implication)
        ))?;
        let conjunction = self.name("a");
        self.push(&format!(
            "(step {conjunction} (cl (and {cond} {orig}) (not {cond}) (not {orig})) :rule and_neg)"
        ))?;
        self.resolution(
            &[negated(cond), negated(orig), scaled.to_string()],
            &[axiom, unfolded, conjunction],
        )
    }

    /// One `resolution` step over `premises`, concluding `clause` with
    /// repeated literals written once.
    pub(super) fn resolution(&mut self, clause: &[String], premises: &[String]) -> Option<String> {
        let name = self.name("r");
        let mut line = format!("(step {name} (cl");
        let mut written: Vec<&str> = Vec::with_capacity(clause.len());
        for literal in clause {
            if !written.contains(&literal.as_str()) {
                written.push(literal);
                let _ = write!(line, " {literal}");
            }
        }
        let _ = write!(
            line,
            ") :rule resolution :premises ({}))",
            premises.join(" ")
        );
        self.push(&line)?;
        Some(name)
    }
}
