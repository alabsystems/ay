// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's checker, mirrored step by step over a printed Alethe
//! document: Clean 7330fa6c's `clean cert verify-external`, which external-codegen
//! promotes an AY `unsat` on (its vendored Carcara with Clean's fixes, under
//! the default checker configuration, behind `carcara_verify`'s parsing
//! boundary and `bitblast_ashr` guard).
//!
//! Each mirrored rule answers three ways. `Accepted` is claimed only where the
//! consumer's own code accepts the step; `Refused` only where it refuses it;
//! anything the mirror does not decide (a rule outside [`MIRRORED`], a width
//! or sort the reader does not infer, a subproof's context, a resolution
//! without pivots that only the consumer's greedy search might accept, an
//! assumption matching a premise only up to n-ary flattening) is
//! `Undetermined`, and a certificate with such a step is NOT reported as
//! checked here: [`Coverage::checked`] holds only when every step and
//! assumption was accepted AND the walk itself re-derived the empty clause
//! from the problem's own assertions ([`Coverage::refutation`]: a `(cl)`
//! outside every subproof resting on no undischarged local assumption, and
//! only on accepted commands). The structural checks the consumer makes
//! around a rule are transcribed too: `:discharge` only on `subproof`, an end
//! step discharging every assumption made directly in its subproof, and only
//! a context-closing rule (or a hole) ending an anchor with `:args`; Clean's
//! premise scoping across such an anchor is not, so an accepted step whose
//! premise crosses one is `Undetermined`. The covered-rule set is
//! [`MIRRORED`] itself, the table the steps are dispatched through. The
//! problem is read by AY's own SMT-LIB front end (`ay_frontend::parse` and
//! the elaborator AY solves with): its assertions as live at its query
//! (`push`/`pop`, `reset-assertions` and `reset` applied, nothing after the
//! first `check-sat`), never through the proof's macros, and every sort the
//! mirror infers a width from is the elaborated sort of a live symbol, never
//! read off a name. A problem that declares a name the front end's operator
//! tables hold (`ay_frontend::is_builtin_operator_name`: `ite`, `=`, `and`,
//! …, which AY accepts as overloads) is not read as a query, and no problem
//! symbol is ever an application's operator to a rule (`Document::head`).
//! The proof is lexed by the same front end and its
//! nullary `define-fun`s applied in document order; a macro with parameters,
//! or defined after a command that uses its name, is refused, and, stricter
//! than the consumer, so is a proof `define-fun` of a symbol the problem
//! uses. Not mirrored: the consumer's own sort checking of the proof, which
//! the mirror assumes succeeds.

use std::collections::BTreeMap;

#[path = "consumer_rules/bitblast.rs"]
mod bitblast;
#[path = "consumer_rules/clauses.rs"]
mod clauses;
#[path = "consumer_rules/dialect.rs"]
mod dialect;
#[path = "consumer_rules/divider.rs"]
mod divider;
#[path = "consumer_rules/document.rs"]
mod document;
#[path = "consumer_rules/equality.rs"]
mod equality;
#[path = "consumer_rules/evaluate.rs"]
mod evaluate;
#[path = "consumer_rules/linear.rs"]
mod linear;
#[path = "consumer_rules/polynomial.rs"]
mod polynomial;
#[path = "consumer_rules/pseudo_boolean.rs"]
mod pseudo_boolean;
#[path = "consumer_rules/query.rs"]
mod query;
#[path = "consumer_rules/reader.rs"]
mod reader;
#[path = "consumer_rules/resolution.rs"]
mod resolution;
#[path = "consumer_rules/shift.rs"]
mod shift;
#[path = "consumer_rules/simplify.rs"]
mod simplify;
#[path = "consumer_rules/walk.rs"]
mod walk;
#[path = "consumer_rules/zero_extend_identity.rs"]
mod zero_extend_identity;

pub(crate) use dialect::{
    pinned_refused_ashr_steps, pinned_refused_divider_steps, pinned_refused_zero_extend_steps,
};
use document::Document;
pub(super) use walk::{mirror_certificate, mirror_certificate_with_control, step_verdict};
pub(crate) use zero_extend_identity::zero_extend_identity_defects;

/// Why the mirror does not accept a step.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Verdict {
    /// The consumer's code refuses the step.
    Refused(String),
    /// The mirror does not decide the step.
    Undetermined(String),
}

/// `Ok` is the consumer accepting the step.
type Checked = Result<(), Verdict>;

fn refuse<T>(why: impl Into<String>) -> Result<T, Verdict> {
    Err(Verdict::Refused(why.into()))
}

fn undecided<T>(why: impl Into<String>) -> Result<T, Verdict> {
    Err(Verdict::Undetermined(why.into()))
}

/// `Ok` when `holds`, else the consumer's refusal.
fn require(holds: bool, why: impl FnOnce() -> String) -> Checked {
    if holds {
        Ok(())
    } else {
        refuse(why())
    }
}

/// `match_term_err!((head a1 … an) = id)`: the operands of an application
/// of `head` with exactly `arity` of them.
fn shape(document: &Document, id: u32, head: &str, arity: usize) -> Result<Vec<u32>, Verdict> {
    match document.op(id, head) {
        Some(operands) if operands.len() == arity => Ok(operands),
        _ => refuse(format!(
            "{} is not ({head} …) of {arity}",
            document.show(id)
        )),
    }
}

/// `match_term_err!((head ...) = id)`: the operands, however many.
fn nary(document: &Document, id: u32, head: &str) -> Result<Vec<u32>, Verdict> {
    document.op(id, head).map_or_else(
        || refuse(format!("{} is not ({head} …)", document.show(id))),
        Ok,
    )
}

/// `remove_negation_err`.
fn negation(document: &Document, id: u32) -> Result<u32, Verdict> {
    shape(document, id, "not", 1).map(|operands| operands[0])
}

/// `assert_eq`: the consumer's terms are hash-consed, so equal is identical.
fn same(document: &Document, expected: u32, got: u32) -> Checked {
    require(expected == got, || {
        format!(
            "expected {}, got {}",
            document.show(expected),
            document.show(got)
        )
    })
}

/// One step as the consumer's rule sees it: every term expanded.
struct StepInput {
    conclusion: Vec<u32>,
    premises: Vec<Vec<u32>>,
    args: Vec<u32>,
    /// Inside an `anchor` with `:args`: `refl` may use its context.
    in_context: bool,
    /// The step that closes a subproof: the clause of the command before it.
    previous: Option<Vec<u32>>,
    /// The `:discharge` commands: an assumption's term, `None` otherwise.
    discharge: Vec<Option<u32>>,
}

impl StepInput {
    /// `assert_clause_len(conclusion, 1)`: the one literal.
    fn unit(&self) -> Result<u32, Verdict> {
        match self.conclusion[..] {
            [literal] => Ok(literal),
            _ => refuse(format!("{} literals, not one", self.conclusion.len())),
        }
    }

    /// `assert_num_args(args, 1)` and `as_usize_err`.
    fn index(&self, document: &Document) -> Result<usize, Verdict> {
        match self.args[..] {
            [index] => document
                .atom_text(index)
                .and_then(|text| text.parse().ok())
                .map_or_else(|| refuse("the argument is not an index"), Ok),
            _ => refuse(format!("{} arguments, not one", self.args.len())),
        }
    }

    /// `get_premise_term` of the only premise.
    fn premise_term(&self) -> Result<u32, Verdict> {
        match &self.premises[..] {
            [premise] => match premise[..] {
                [term] => Ok(term),
                _ => refuse("the premise is not a unit clause"),
            },
            _ => refuse(format!("{} premises, not one", self.premises.len())),
        }
    }
}

type Rule = fn(&mut Document, &StepInput) -> Checked;

/// The names of the rules in [`MIRRORED`].
pub(super) fn mirrored_rules() -> impl Iterator<Item = &'static str> {
    MIRRORED.iter().map(|&(name, _)| name)
}

/// The rules this mirror checks, by the name the consumer dispatches on: the
/// covered-rule set. A step whose rule is not here is `Undetermined`.
const MIRRORED: &[(&str, Rule)] = &[
    ("true", clauses::r#true),
    ("false", clauses::r#false),
    ("not_not", clauses::not_not),
    ("and_pos", clauses::and_pos),
    ("and_neg", clauses::and_neg),
    ("or_pos", clauses::or_pos),
    ("or_neg", clauses::or_neg),
    ("xor_pos1", clauses::xor_pos1),
    ("xor_pos2", clauses::xor_pos2),
    ("xor_neg1", clauses::xor_neg1),
    ("xor_neg2", clauses::xor_neg2),
    ("implies_pos", clauses::implies_pos),
    ("implies_neg1", clauses::implies_neg1),
    ("implies_neg2", clauses::implies_neg2),
    ("equiv_pos1", clauses::equiv_pos1),
    ("equiv_pos2", clauses::equiv_pos2),
    ("equiv_neg1", clauses::equiv_neg1),
    ("equiv_neg2", clauses::equiv_neg2),
    ("ite_pos1", clauses::ite_pos1),
    ("ite_pos2", clauses::ite_pos2),
    ("ite_neg1", clauses::ite_neg1),
    ("ite_neg2", clauses::ite_neg2),
    ("equiv1", clauses::equiv1),
    ("equiv2", clauses::equiv2),
    ("not_equiv1", clauses::not_equiv1),
    ("not_equiv2", clauses::not_equiv2),
    ("ite1", clauses::ite1),
    ("ite2", clauses::ite2),
    ("not_ite1", clauses::not_ite1),
    ("not_ite2", clauses::not_ite2),
    ("xor1", clauses::xor1),
    ("xor2", clauses::xor2),
    ("not_xor1", clauses::not_xor1),
    ("not_xor2", clauses::not_xor2),
    ("implies", clauses::implies),
    ("not_implies1", clauses::not_implies1),
    ("not_implies2", clauses::not_implies2),
    ("and", clauses::and),
    ("not_or", clauses::not_or),
    ("or", clauses::or),
    ("not_and", clauses::not_and),
    ("contraction", clauses::contraction),
    ("reordering", clauses::reordering),
    ("resolution", resolution::resolution),
    ("th_resolution", resolution::resolution),
    ("drup", resolution::drup),
    ("eq_reflexive", equality::eq_reflexive),
    ("eq_transitive", equality::eq_transitive),
    ("eq_congruent", equality::eq_congruent),
    ("eq_congruent_pred", equality::eq_congruent_pred),
    ("refl", equality::refl),
    ("trans", equality::trans),
    ("cong", equality::cong),
    ("arrays_idx", equality::arrays_idx),
    ("arrays_row", equality::arrays_row),
    ("arrays_row_contra", equality::arrays_row_contra),
    ("symm", equality::symm),
    ("not_symm", equality::not_symm),
    ("subproof", equality::subproof),
    ("and_simplify", simplify::and_simplify),
    ("or_simplify", simplify::or_simplify),
    ("ite_simplify", simplify::ite_simplify),
    ("equiv_simplify", simplify::equiv_simplify),
    ("ite_intro", simplify::ite_intro),
    ("evaluate", evaluate::evaluate_rule),
    ("poly_simp", polynomial::poly_simp),
    ("la_generic", linear::la_generic),
    ("pbblast_bveq", pseudo_boolean::bveq),
    ("pbblast_bvult", pseudo_boolean::bvult),
    ("pbblast_bvugt", pseudo_boolean::bvugt),
    ("pbblast_bvuge", pseudo_boolean::bvuge),
    ("pbblast_bvule", pseudo_boolean::bvule),
    ("pbblast_bvslt", pseudo_boolean::bvslt),
    ("pbblast_bvsgt", pseudo_boolean::bvsgt),
    ("pbblast_bvsge", pseudo_boolean::bvsge),
    ("pbblast_bvsle", pseudo_boolean::bvsle),
    ("bitblast_const", bitblast::constant),
    ("bitblast_var", bitblast::variable),
    ("bitblast_and", bitblast::and),
    ("bitblast_or", bitblast::or),
    ("bitblast_xor", bitblast::xor),
    ("bitblast_xnor", bitblast::xnor),
    ("bitblast_not", bitblast::not),
    ("bitblast_neg", bitblast::neg),
    ("bitblast_equal", bitblast::equal),
    ("bitblast_comp", bitblast::comp),
    ("bitblast_ult", bitblast::ult),
    ("bitblast_slt", bitblast::slt),
    ("bitblast_add", bitblast::add),
    ("bitblast_mult", bitblast::mult),
    ("bitblast_extract", bitblast::extract),
    ("bitblast_concat", bitblast::concat),
    ("bitblast_sign_extend", bitblast::sign_extend),
    ("bitblast_shl", shift::shl),
    ("bitblast_lshr", shift::lshr),
    ("bitblast_ashr", shift::ashr),
    ("bitblast_udiv", divider::udiv),
    ("bitblast_urem", divider::urem),
];

fn mirrored(rule: &str) -> Option<Rule> {
    MIRRORED
        .iter()
        .find_map(|&(name, check)| (name == rule).then_some(check))
}

/// Whether the mirror checks steps of `rule` (`assume` is always checked).
pub(super) fn is_mirrored(rule: &str) -> bool {
    rule == "assume" || mirrored(rule).is_some()
}

/// What the mirror established about one certificate.
#[derive(Debug, Default)]
pub(super) struct Coverage {
    /// Every command's rule (`assume` for assumptions), with its count.
    pub(super) rules: BTreeMap<String, usize>,
    /// The consumer refuses these: `step <id> (<rule>): <why>`, or a
    /// document-level refusal.
    pub(super) refused: Vec<String>,
    /// Rules with steps the mirror did not decide: count and the first reason.
    pub(super) undetermined: BTreeMap<String, (usize, String)>,
    /// The step whose empty clause the walk re-derived from the problem's
    /// assertions through accepted commands only; `None` unless it did.
    pub(super) refutation: Option<String>,
}

impl Coverage {
    /// Every step was checked against the consumer's rules and accepted, and
    /// the walk re-derived the empty clause from the problem's assertions.
    pub(super) fn checked(&self) -> bool {
        self.refused.is_empty()
            && self.undetermined.is_empty()
            && !self.rules.is_empty()
            && self.refutation.is_some()
    }

    fn record(&mut self, id: &str, rule: &str, verdict: Checked) {
        *self.rules.entry(rule.to_string()).or_default() += 1;
        match verdict {
            Ok(()) => {}
            Err(Verdict::Refused(why)) => self.refused.push(format!("step {id} ({rule}): {why}")),
            Err(Verdict::Undetermined(why)) => {
                let entry = self
                    .undetermined
                    .entry(rule.to_string())
                    .or_insert((0, format!("step {id}: {why}")));
                entry.0 += 1;
            }
        }
    }
}

/// Every step of the document that the consumer's rules refuse, as mirrored
/// here (the assumptions, which need the problem, and the empty clause are
/// not asked).
pub(super) fn consumer_rule_defects(proof: &str) -> Vec<String> {
    mirror_certificate("", proof)
        .refused
        .into_iter()
        .filter(|refusal| refusal.starts_with("step "))
        .collect()
}
