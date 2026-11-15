// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface admissibility for Alethe `eq_congruent` steps.
//!
//! `eq_congruent` is a premise-free tautology whose validity is a RELATION
//! among its printed operands: hypothesis `i` must equate argument pair `i`
//! of two applications of one head. The surface override channel re-spells
//! operands independently of the term DAG, and the lazy-EUF lane states the
//! whole lemma as ONE or-literal, `(cl (or ¬e_1 .. ¬e_k e))`, which the
//! internal validator flattens and pinned carcara 1.1.0 refuses outright
//! (`expected at least 2 terms in clause, got 1`). Before 2026-09-20 the
//! one-literal unit reached the wire UNDER ITS RULE NAME: the only
//! `eq_congruent` bridge returned `Ok(None)` below two literals and the step
//! fell through unjudged — not even a hole. QF_UF `iso_brn925` `t1892` made
//! its document `invalid`.
//!
//! Every `eq_congruent` is now rendered once, judged by
//! [`printed_eq_congruent_holds`] — the replay of carcara's own
//! `generic_congruent_rule` over the shipped strings — and shipped as the
//! certified packing where the judgement holds and as the honest hole where
//! it does not.

use ay_core::{ProofId, TermId, UNPROVED_STEP_RULE};

use super::surface_literal::same_printed_term;
use super::surface_tokens::split_smt_term_slices_bounded;
use super::{split_alethe_application_bounded, AlethePrinter};

/// Literal count above which the replay declines rather than scanning.
const MAX_CONGRUENCE_LITERALS: usize = 1_024;

/// Byte cap on one rendered literal handed to the balanced tokenizer.
const MAX_CONGRUENCE_TERM_BYTES: usize = 1024 * 1024;

/// How pinned carcara's `eq_congruent` reads a printed clause, and what it
/// takes to make the clause an instance of the rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum PrintedCongruence {
    /// Exactly one `(not (= t u))` hypothesis per argument position, each
    /// equating its pair in either orientation: the clause IS the rule.
    Exact,
    /// AY's omitted-identical-position shape. The internal validator lets an
    /// argument position whose two terms are the SAME term go without a
    /// hypothesis (`t = t` holds by reflexivity, so dropping `¬(t = t)`
    /// preserves validity); carcara demands `n == f_args.len()` and answers
    /// `MissingPremise`. The clause becomes an exact instance once
    /// `(not (= a a))` is inserted at each listed position (0-based,
    /// ascending), `a` being that position's printed argument text — and
    /// each inserted hypothesis is discharged by an `eq_reflexive` axiom.
    Padded(Vec<(usize, String)>),
}

impl AlethePrinter<'_> {
    /// Judge an `eq_congruent` step over the text it ships and spell it, or
    /// decline it to `hole`.
    ///
    /// `None` only for a clause outside what the replay reads (empty, or
    /// wider than [`MAX_CONGRUENCE_LITERALS`]); every other clause gets a
    /// rendering here, and the caller's default rendering never sees an
    /// `eq_congruent` this judgement has not read. Every literal is rendered
    /// ONCE, by the same literal renderer `format_clause` uses, and the
    /// spelling, the exact default and the decline all ship that text.
    ///
    /// The OR-packed unit `(cl (or ¬e_1 .. ¬e_k e))` — the lazy-EUF lane's
    /// statement of the lemma, which carcara's two-literal floor refuses as
    /// one literal — spells as
    ///
    /// ```text
    /// (step t.ec (cl ¬e_1 .. ¬e_k e) :rule eq_congruent)
    /// (step t.o0 (cl (or ¬e_1 .. e) (not ¬e_1)) :rule or_neg :args (0))
    /// ...
    /// (step t.o{k} (cl (or ¬e_1 .. e) (not e)) :rule or_neg :args (k))
    /// (step t (cl (or ¬e_1 .. e)) :rule resolution :premises (t.ec t.o0 .. t.o{k}))
    /// ```
    ///
    /// with the disjuncts read off the rendered or-term by the balanced
    /// tokenizer and `t.ec` judged by [`printed_eq_congruent_holds`]. For the
    /// omitted-identical-position shape, `t.ec` carries the padded
    /// hypothesis `(not (= a a))` at each omitted position and one
    /// `(step t.r{i} (cl (= a a)) :rule eq_reflexive)` per padding joins the
    /// resolution's premises. The closing `resolution` ships the unit's
    /// exact text under the original id — the RUP carcara replays
    /// (`¬(or ..)` reduces every `or_neg` to the negation of one disjunct,
    /// the reflexive axioms cancel the paddings, and those empty `t.ec`) — so
    /// the unit's `or` consumer reads the same conclusion it always did.
    ///
    /// A FLAT clause (two or more literals) that is an exact instance renders
    /// as the byte-identical default `(step t (cl ..) :rule eq_congruent)`;
    /// the omitted-identical-position shape ships as the padded `t.ec`, its
    /// `eq_reflexive` axioms and a `resolution` back to the clause's exact
    /// text under the original id.
    ///
    /// A clause whose printed literals are no congruence — a re-spelled
    /// hypothesis, a differing position with no hypothesis, an indexed or
    /// differing head, a unit that is not an `or` over the text or has fewer
    /// than two operands — ships as the honest hole over the same text, never
    /// under a rule name the printed step does not instantiate.
    pub(super) fn format_eq_congruent_or_hole(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        if let [unit] = clause {
            let mut printed = String::new();
            self.write_derived_literal_into(&mut printed, *unit);
            return Some(self.packed_eq_congruent_or_hole(id, &printed));
        }
        if !(2..=MAX_CONGRUENCE_LITERALS).contains(&clause.len()) {
            return None;
        }
        let printed: Vec<String> = clause
            .iter()
            .map(|&literal| {
                let mut out = String::new();
                self.write_derived_literal_into(&mut out, literal);
                out
            })
            .collect();
        let borrowed: Vec<&str> = printed.iter().map(String::as_str).collect();
        let clause_text = borrowed.join(" ");
        Some(match printed_eq_congruent_holds(&borrowed) {
            Ok(PrintedCongruence::Exact) => {
                format!("(step {id} (cl {clause_text}) :rule eq_congruent)")
            }
            Ok(judgement @ PrintedCongruence::Padded(_)) => {
                let mut out = String::new();
                let mut premises = format!("{id}.ec");
                write_congruence_prefix(&mut out, &mut premises, id, &borrowed, &judgement);
                let _ = std::fmt::Write::write_fmt(
                    &mut out,
                    format_args!(
                        "(step {id} (cl {clause_text}) :rule resolution :premises ({premises}))"
                    ),
                );
                out
            }
            Err(reason) => {
                disclose_hole(id, reason);
                format!("(step {id} (cl {clause_text}) :rule {UNPROVED_STEP_RULE})")
            }
        })
    }

    fn packed_eq_congruent_or_hole(&self, id: ProofId, printed: &str) -> String {
        let hole = |reason: &str| {
            disclose_hole(id, reason);
            format!("(step {id} (cl {printed}) :rule {UNPROVED_STEP_RULE})")
        };
        let Ok(disjuncts) = split_alethe_application_bounded(
            printed,
            "or",
            MAX_CONGRUENCE_LITERALS,
            MAX_CONGRUENCE_TERM_BYTES,
        ) else {
            return hole("the unit does not print as an or-term");
        };
        let judgement = match printed_eq_congruent_holds(&disjuncts) {
            Ok(judgement) => judgement,
            Err(reason) => return hole(reason),
        };
        let mut out = String::with_capacity(printed.len() * (disjuncts.len() + 3));
        let mut premises = format!("{id}.ec");
        write_congruence_prefix(&mut out, &mut premises, id, &disjuncts, &judgement);
        for (index, disjunct) in disjuncts.iter().enumerate() {
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {id}.o{index} (cl {printed} (not {disjunct})) :rule or_neg :args ({index}))\n"
                ),
            );
            let _ = std::fmt::Write::write_fmt(&mut premises, format_args!(" {id}.o{index}"));
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!("(step {id} (cl {printed}) :rule resolution :premises ({premises}))"),
        );
        out
    }
}

/// WHICH replay arm declined is the one fact a holey-certificate triage
/// needs, and the document does not carry it. Same typed-carrier disclosure
/// as the theory-lemma path's wire downgrade.
fn disclose_hole(id: ProofId, reason: &str) {
    if ay_core::misc_cli_flags().debug_cert {
        ay_core::safe_eprintln!("c !! eq_congruent judgement at {id}: hole ({reason})");
    }
}

/// The `eq_congruent` step over `literals` (padded where the judgement says
/// so) and one `eq_reflexive` per padding, appended to `out`; every step id
/// is appended to `premises`.
fn write_congruence_prefix(
    out: &mut String,
    premises: &mut String,
    id: ProofId,
    literals: &[&str],
    judgement: &PrintedCongruence,
) {
    let paddings: &[(usize, String)] = match judgement {
        PrintedCongruence::Exact => &[],
        PrintedCongruence::Padded(paddings) => paddings,
    };
    let (conclusion, hypotheses) = literals.split_last().expect("judged clause is non-empty");
    // The judged arity: every position carries either a printed hypothesis
    // or a padding, in argument order.
    let arity = hypotheses.len() + paddings.len();
    let mut padded: Vec<String> = Vec::with_capacity(arity + 1);
    let mut hypotheses = hypotheses.iter();
    let mut paddings_by_position = paddings.iter().peekable();
    for position in 0..arity {
        match paddings_by_position.peek() {
            Some((padded_position, argument)) if *padded_position == position => {
                padded.push(format!("(not (= {argument} {argument}))"));
                paddings_by_position.next();
            }
            _ => padded.push(
                (*hypotheses
                    .next()
                    .expect("one hypothesis per unpadded position"))
                .to_string(),
            ),
        }
    }
    padded.push((*conclusion).to_string());
    let _ = std::fmt::Write::write_fmt(
        out,
        format_args!(
            "(step {id}.ec (cl {}) :rule eq_congruent)\n",
            padded.join(" ")
        ),
    );
    for (position, argument) in paddings {
        let _ = std::fmt::Write::write_fmt(
            out,
            format_args!(
                "(step {id}.r{position} (cl (= {argument} {argument})) :rule eq_reflexive)\n"
            ),
        );
        let _ = std::fmt::Write::write_fmt(premises, format_args!(" {id}.r{position}"));
    }
}

/// Replay pinned carcara 1.1.0's `eq_congruent` decision procedure over the
/// exact literal text a step is about to ship, extended by the one repair
/// AY's own validator makes necessary.
///
/// Mirrors `carcara/src/checker/rules/congruence.rs::eq_congruent` and its
/// `generic_congruent_rule`:
///
/// * at least two literals (`assert_clause_len(conclusion, 2..)`);
/// * the LAST literal is a binary `(= f g)` whose two sides are applications
///   (`Term::App` / `Term::Op`) of the SAME head with the SAME arity; an
///   indexed head (`(_ extract ..)`, `(_ is C)`) is neither and is refused
///   (`term is not an application or operation`), as is a bare symbol;
/// * every earlier literal is a `(not (= t u))` hypothesis;
/// * there is EXACTLY one hypothesis per argument position (`TooManyPremises`
///   / `MissingPremise` otherwise), and hypothesis `i` equates pair `i` in
///   either orientation (`PremiseDoesntJustifyArgs` otherwise).
///
/// The one extension: a position whose two printed arguments are one term
/// and which the next hypothesis does not equate is recorded as a PADDING
/// rather than refused — that is the shape AY's `validate_euf_congruent`
/// admits without a hypothesis, and [`PrintedCongruence::Padded`] says how
/// the clause becomes an exact instance. Every hypothesis must still be
/// consumed in argument order.
///
/// Heads and operands are compared with [`same_printed_term`]: byte
/// identity first, then
/// [`super::surface_literal::equal_modulo_bitvec_literal_spelling`], carcara's
/// term identity on the two ways the printed surface can spell one term
/// differently. A head the tokenizer cannot read as one symbol field, or two
/// heads that differ as text, decline — carcara compares its parsed
/// function/operator terms, and a distinct spelling this replay cannot prove
/// equal is refused rather than guessed.
pub(super) fn printed_eq_congruent_holds(
    literals: &[&str],
) -> Result<PrintedCongruence, &'static str> {
    if literals.len() < 2 {
        return Err("fewer than two literals (carcara's eq_congruent floor)");
    }
    if literals.len() > MAX_CONGRUENCE_LITERALS {
        return Err("more literals than the replay scans");
    }
    let (conclusion, hypotheses) = literals
        .split_last()
        .ok_or("fewer than two literals (carcara's eq_congruent floor)")?;
    let (left, right) =
        split_printed_equality(conclusion).ok_or("the conclusion is not a binary equality")?;
    let (left_head, left_args) = split_printed_application(left)
        .ok_or("the conclusion's left side is not a plain application")?;
    let (right_head, right_args) = split_printed_application(right)
        .ok_or("the conclusion's right side is not a plain application")?;
    if !same_printed_term(left_head, right_head) {
        return Err("the two applications have different heads");
    }
    if left_args.len() != right_args.len() {
        return Err("the two applications have different arities");
    }
    if hypotheses.len() > left_args.len() {
        return Err("more hypotheses than argument positions");
    }
    let mut pairs: Vec<(&str, &str)> = Vec::with_capacity(hypotheses.len());
    for hypothesis in hypotheses {
        let negated =
            split_printed_negation(hypothesis).ok_or("a hypothesis is not a printed negation")?;
        pairs.push(
            split_printed_equality(negated)
                .ok_or("a hypothesis does not negate a binary equality")?,
        );
    }
    let mut paddings: Vec<(usize, String)> = Vec::new();
    let mut next_pair = 0usize;
    for (position, (&left_arg, &right_arg)) in left_args.iter().zip(right_args.iter()).enumerate() {
        if let Some(&(t, u)) = pairs.get(next_pair) {
            let justifies = (same_printed_term(t, left_arg) && same_printed_term(u, right_arg))
                || (same_printed_term(u, left_arg) && same_printed_term(t, right_arg));
            if justifies {
                next_pair += 1;
                continue;
            }
        }
        if same_printed_term(left_arg, right_arg) {
            paddings.push((position, left_arg.to_string()));
            continue;
        }
        return Err("an argument pair differs and the next hypothesis does not equate it");
    }
    if next_pair != pairs.len() {
        return Err("a hypothesis is left over after every argument position is justified");
    }
    Ok(if paddings.is_empty() {
        PrintedCongruence::Exact
    } else {
        PrintedCongruence::Padded(paddings)
    })
}

/// One rendered application `(head a_1 .. a_n)` split into its head symbol
/// and its operand renderings. A bare symbol has no arguments to pair, and a
/// head that is itself parenthesised (an indexed identifier) is not
/// `Term::App`/`Term::Op` to carcara's rule; both decline.
fn split_printed_application(term: &str) -> Option<(&str, Vec<&str>)> {
    let inner = term.strip_prefix('(')?.strip_suffix(')')?;
    let fields = split_smt_term_slices_bounded(
        inner,
        MAX_CONGRUENCE_LITERALS.saturating_add(1),
        MAX_CONGRUENCE_TERM_BYTES,
    )
    .ok()?;
    let (head, args) = fields.split_first()?;
    if args.is_empty() || head.starts_with('(') {
        return None;
    }
    Some((head, args.to_vec()))
}

/// One rendered binary `(= a b)` split into its two operand renderings.
fn split_printed_equality(term: &str) -> Option<(&str, &str)> {
    let operands =
        split_alethe_application_bounded(term, "=", 2, MAX_CONGRUENCE_TERM_BYTES).ok()?;
    match operands.as_slice() {
        [left, right] => Some((left, right)),
        _ => None,
    }
}

/// One rendered `(not X)` split into `X`.
fn split_printed_negation(term: &str) -> Option<&str> {
    let operands =
        split_alethe_application_bounded(term, "not", 1, MAX_CONGRUENCE_TERM_BYTES).ok()?;
    match operands.as_slice() {
        [only] => Some(only),
        _ => None,
    }
}

#[cfg(test)]
#[path = "alethe_printer_eq_congruent_tests.rs"]
mod tests;
