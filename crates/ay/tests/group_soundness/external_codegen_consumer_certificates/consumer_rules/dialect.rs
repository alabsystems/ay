// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The steps pinned Carcara 9a352ee refuses although the consumer accepts
//! them, read from the document as printed: a certificate carrying one must
//! disclose `carcara_surface=clean-dialect`.

use super::document::Document;
use super::reader::{Command, Sexp, Step};

/// The two sides of a unit equality clause.
pub(super) fn equality(clause: &[Sexp]) -> Option<(&Sexp, &Sexp)> {
    let [literal] = clause else { return None };
    match (literal.head(), literal.args()) {
        (Some("="), [left, right]) => Some((left, right)),
        _ => None,
    }
}

/// The document's steps, in order.
pub(super) fn steps(document: &mut Document) -> Vec<Step> {
    std::mem::take(&mut document.commands)
        .into_iter()
        .filter_map(|command| match command {
            Command::Step(step) => Some(step),
            Command::Assume(..) | Command::Anchor(..) => None,
        })
        .collect()
}

/// Whether every bit of the printed `bvashr` result is `(ite _ _ sign)`, the
/// overshift layer filled with the shifted word's sign bit (the consumer's
/// spelling), and that sign bit is not literally `false`.
fn fills_with_a_sign_bit(document: &mut Document, clause: &[Sexp]) -> bool {
    let Some((source, result)) = equality(clause) else {
        return false;
    };
    let Some(word) = source
        .args()
        .first()
        .filter(|_| source.head() == Some("bvashr"))
    else {
        return false;
    };
    let word = document.expand(word);
    let Some(&sign) = document
        .args(word)
        .last()
        .filter(|_| document.head(word) == Some("@bbterm"))
    else {
        return false;
    };
    let result = document.expand(result);
    let bits = document.args(result);
    document.head(result) == Some("@bbterm")
        && bits.len() == document.args(word).len()
        && bits.iter().all(|&bit| {
            let guarded = document.args(bit);
            document.head(bit) == Some("ite") && guarded.len() == 3 && guarded[2] == sign
        })
        && document.show(sign) != "false"
}

/// The `bitblast_ashr` steps whose final layer fills with a sign bit that is
/// not literally `false`: the consumer's spelling, which pinned Carcara 9a352ee
/// (it fills with `false`) refuses.
pub(crate) fn pinned_refused_ashr_steps(proof: &str) -> Vec<String> {
    let mut document = Document::read(proof);
    steps(&mut document)
        .into_iter()
        .filter(|step| {
            step.rule == "bitblast_ashr" && fills_with_a_sign_bit(&mut document, &step.clause)
        })
        .map(|step| step.id)
        .collect()
}

/// The steps that cross `zero_extend` (`zero_extend_identity`): a side that
/// is a `zero_extend` application equated with one that is not, outside a
/// transport step or a closed `evaluate`. The consumer reads the operator as
/// its definition (`dialect:expand_zero_extend`, from Clean `ba5e28ff5`),
/// while pinned Carcara 9a352ee keeps it and refuses the step.
pub(crate) fn pinned_refused_zero_extend_steps(proof: &str) -> Vec<String> {
    super::zero_extend_identity::zero_extend_crossings(proof)
        .into_iter()
        .map(|crossing| crossing.id)
        .collect()
}

/// The `bitblast_udiv`/`bitblast_urem` steps spelled with the consumer's
/// divider, which pinned Carcara 9a352ee refuses: every divider step of a
/// default-dialect document (Clean `5390f432b8`'s long division, whose adder
/// returns the carry OUT of the top bit) whose dividend is not literally zero.
/// On a literally zero dividend both circuits stop at once and build the same
/// terms.
pub(crate) fn pinned_refused_divider_steps(proof: &str) -> Vec<String> {
    let mut document = Document::read(proof);
    steps(&mut document)
        .into_iter()
        .filter(|step| {
            matches!(step.rule.as_str(), "bitblast_udiv" | "bitblast_urem")
                && equality(&step.clause).is_none_or(|(source, _)| {
                    let dividend = source.args().first().map(|word| document.expand(word));
                    dividend.is_none_or(|word| {
                        let bits = document.args(word);
                        bits.is_empty() || bits.iter().any(|bit| document.show(*bit) != "false")
                    })
                })
        })
        .map(|step| step.id)
        .collect()
}
