// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compare a rendered assertion with the authored one MODULO the spelling of
//! bit-vector literals.
//!
//! The Alethe printer spells every bit-vector constant as a full-width binary
//! string, so an authored `#xff` prints back as `#b11111111`. The consumer
//! reads both as ONE term — measured 2026-09-29 against Clean `5390f432b8`'s
//! `cert verify-external`: a problem asserting `(= x #xff)` accepts the
//! premise `(assume h (= x #b11111111))` and rejects `(= x #b11111110)` with
//! "assumption not present in the problem". Only the spelling is forgiven:
//! both literals are rewritten to the binary digits of their own value at
//! their own width, so a different value or width still compares unequal.

use super::*;

impl Executor {
    /// [`Self::rebuilt_root_prints_as_authored`] up to the spelling of
    /// bit-vector literals. Only a replacement whose printed steps all come
    /// from the internal DAG — a bit-blast lemma and its resolutions
    /// (`authored_bv_bitblast_refutation`) — may use it: there a literal's
    /// spelling reaches nothing but the `assume`, which the consumer reads as
    /// the same term. A replacement that keeps authored spellings in its
    /// steps (a `cong` over an authored operand) needs them exact, or the
    /// exporter refuses the step.
    pub(super) fn rebuilt_root_prints_as_authored_up_to_literals(
        &self,
        root: TermId,
        assertion: &FrontendTerm,
    ) -> bool {
        let authored = crate::executor::proof_surface_syntax::strip_frontend_annotations(assertion);
        let overrides = self.proof_export_term_overrides().unwrap_or_default();
        let rendered =
            ay_proof::format_term_alethe_with_overrides(&self.ctx.terms, root, &overrides);
        parse_rendered_assertion(&rendered).is_some_and(|reparsed| {
            same_modulo_bv_literal_spelling(
                crate::executor::proof_surface_syntax::strip_frontend_annotations(&reparsed),
                authored,
            )
        })
    }
}

/// `rendered` and `authored` are the same surface term once every binary or
/// hexadecimal literal is spelled in binary.
pub(in crate::executor::proof) fn same_modulo_bv_literal_spelling(
    rendered: &FrontendTerm,
    authored: &FrontendTerm,
) -> bool {
    if rendered == authored {
        return true;
    }
    let (mut rendered, mut authored) = (rendered.clone(), authored.clone());
    spell_bv_literals_in_binary(&mut rendered);
    spell_bv_literals_in_binary(&mut authored);
    rendered == authored
}

/// Rewrite `#x…` literals and indexed `(_ bvN W)` constants to `#b…` in
/// place. Only application arguments and annotations are descended: a literal
/// under any other node keeps its spelling, which can only make the comparison
/// stricter. (external-codegen writes every constant as `(_ bvN W)`; Clean read
/// `(= x (_ bv7 8))` and `(= x #b00000111)` as one premise and rejected
/// `#b00000110`, measured 2026-09-29.)
fn spell_bv_literals_in_binary(root: &mut FrontendTerm) {
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        match term {
            FrontendTerm::Const(FrontendConstant::Hexadecimal(text)) => {
                let digits = text.strip_prefix("#x").unwrap_or(text.as_str());
                let mut binary = String::with_capacity(2 + 4 * digits.len());
                binary.push_str("#b");
                for digit in digits.chars() {
                    let Some(nibble) = digit.to_digit(16) else {
                        // Not a hexadecimal literal after all: leave it be.
                        binary.clear();
                        break;
                    };
                    binary.push_str(&format!("{nibble:04b}"));
                }
                if !binary.is_empty() {
                    *term = FrontendTerm::Const(FrontendConstant::Binary(binary));
                }
            }
            FrontendTerm::IndexedApp(name, indices, args) if args.is_empty() => {
                if let Some(binary) = indexed_constant_in_binary(name, indices) {
                    *term = FrontendTerm::Const(FrontendConstant::Binary(binary));
                }
            }
            FrontendTerm::App(_, args)
            | FrontendTerm::IndexedApp(_, _, args)
            | FrontendTerm::QualifiedApp(_, _, args) => stack.extend(args.iter_mut()),
            FrontendTerm::Annotated(inner, _) => stack.push(inner),
            _ => (),
        }
    }
}

/// `(_ bvN W)` as `#b` digits: `None` unless `N` is a decimal numeral below
/// `2^W` and `1 <= W <= 4096`.
fn indexed_constant_in_binary(name: &str, indices: &[FrontendIndex]) -> Option<String> {
    let [FrontendIndex::Numeral(width)] = indices else {
        return None;
    };
    let width: usize = width.parse().ok().filter(|w| (1..=4096).contains(w))?;
    let digits = name.strip_prefix("bv")?;
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    // Leading zeroes carry no arithmetic work. Reject oversized significant
    // numerals before BigUint allocation; no 4096-bit value needs more digits.
    let digits = digits.trim_start_matches('0');
    if digits.len() > 4096 {
        return None;
    }
    let digits = if digits.is_empty() { "0" } else { digits };
    let value = num_bigint::BigUint::parse_bytes(digits.as_bytes(), 10)?;
    let bits = value.to_str_radix(2);
    if value.bits() > width as u64 {
        return None;
    }
    let bits = if value.bits() == 0 {
        String::new()
    } else {
        bits
    };
    Some(format!("#b{}{bits}", "0".repeat(width - bits.len())))
}

#[cfg(test)]
#[path = "bv_literal_spelling_tests.rs"]
mod tests;

/// Extra normalization allocation/work beyond the already charged parsed AST.
/// This mirrors only the literal forms the comparator rewrites. Callers must
/// have admitted the surface tree before entering this walk.
pub(in crate::executor::proof) fn literal_normalization_work(root: &FrontendTerm) -> Option<usize> {
    let mut pending = vec![root];
    let mut work = 0usize;
    while let Some(term) = pending.pop() {
        work = work.checked_add(std::mem::size_of::<FrontendTerm>())?;
        match term {
            FrontendTerm::Const(FrontendConstant::Hexadecimal(text)) => {
                work = work.checked_add(text.len().checked_mul(32)?)?;
            }
            FrontendTerm::IndexedApp(name, indices, args) if args.is_empty() => {
                if let [FrontendIndex::Numeral(width)] = indices.as_slice() {
                    if let Ok(width) = width.parse::<usize>() {
                        if (1..=4096).contains(&width) && name.starts_with("bv") {
                            work = work
                                .checked_add(width.checked_mul(32)?)?
                                .checked_add(name.len().checked_mul(32)?)?;
                        }
                    }
                }
            }
            FrontendTerm::App(_, args)
            | FrontendTerm::IndexedApp(_, _, args)
            | FrontendTerm::QualifiedApp(_, _, args) => pending.extend(args),
            FrontendTerm::Annotated(inner, _) => pending.push(inner),
            _ => (),
        }
    }
    Some(work)
}
