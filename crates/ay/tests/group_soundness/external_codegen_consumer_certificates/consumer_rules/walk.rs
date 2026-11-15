// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's walk over the commands (Clean's Carcara parser and
//! `ProofChecker::check`): an `assume` outside a subproof must be a problem
//! assertion; a premise must name a command in scope (an `anchor` opens a
//! scope, and its end step is the one id that survives it); a closing step
//! sees the command before it; and the proof must derive the empty clause
//! outside every subproof.
//!
//! On top of the consumer's checks, the walk re-derives the refutation
//! itself: every command carries the local assumptions it rests on (an
//! assumption made inside a subproof rests on itself; a step, on what its
//! premises and, at a subproof's end, the command before it rest on, less
//! what an accepted `subproof` discharges) and whether every command it rests
//! on was accepted. [`Coverage::refutation`] names an empty clause outside
//! every subproof that rests on no assumption but the problem's own
//! assertions and on accepted steps only; without one, nothing is checked.
//!
//! REGRESSION (measured 2026-10-01 on aca0123d5, introduced by 049bfc24e):
//! the walk counted a certificate as checked when every step was accepted and
//! some step outside every subproof concluded `(cl)`, so a `subproof` that
//! discharged nothing smuggled its local assumption `q` out, and a refutation
//! of the satisfiable `(assert (not q))` was reported checked step by step.
//! The consumer's structural checks around a rule (`check_step_core`) were not
//! transcribed either: `:discharge` on another rule, an end step leaving a
//! local assumption undischarged, a non-closing rule ending an anchor with
//! `:args`, and Clean's premise scoping across such an anchor.

use std::collections::{BTreeSet, HashMap};

use super::document::Document;
use super::equality::assumption;
use super::reader::{Command, Step};
use super::{mirrored, refuse, undecided, Coverage, StepInput, Verdict};

/// What a command derived, as the mirror re-derives it.
#[derive(Clone)]
struct Fact<'a> {
    clause: Vec<u32>,
    /// The assumptions local to a subproof that the clause still rests on.
    rests_on: BTreeSet<&'a str>,
    /// Every command the clause rests on was accepted.
    accepted: bool,
}

/// An open subproof.
struct Frame<'a> {
    end: &'a str,
    context: bool,
    declared: Vec<&'a str>,
    /// The latest command at this level.
    last: Option<Fact<'a>>,
    /// The assumptions made directly in this subproof: the consumer's
    /// `check_discharge_shared` requires its end step to discharge each one.
    local_assumes: Vec<&'a str>,
}

#[derive(Default)]
struct Scope<'a> {
    facts: HashMap<&'a str, Fact<'a>>,
    assumptions: HashMap<&'a str, u32>,
    /// The subproof depth each id in scope was declared at.
    depths: HashMap<&'a str, usize>,
    frames: Vec<Frame<'a>>,
}

impl<'a> Scope<'a> {
    /// Declare `id` at the current level; `false` when it is already in scope.
    fn declare(&mut self, id: &'a str, fact: Fact<'a>) -> bool {
        if self.facts.contains_key(id) {
            return false;
        }
        self.depths.insert(id, self.frames.len());
        if let Some(frame) = self.frames.last_mut() {
            frame.declared.push(id);
            frame.last = Some(fact.clone());
        }
        self.facts.insert(id, fact);
        true
    }

    /// Close the innermost subproof: its commands leave scope.
    fn close(&mut self) {
        if let Some(frame) = self.frames.pop() {
            for id in frame.declared {
                self.facts.remove(id);
                self.assumptions.remove(id);
                self.depths.remove(id);
            }
        }
    }
}

/// The consumer's verdict on every command of `proof` against `problem`, as
/// far as this mirror decides it.
pub(in super::super) fn mirror_certificate(problem: &str, proof: &str) -> Coverage {
    walk(problem, proof, None, true).0
}

/// The mirror's coverage of `proof` with its negative control: the same proof
/// against `problem` with every assertion dropped (its declarations and
/// definitions kept; `define-fun-rec` is not, so it is satisfiable) must not
/// be counted as checked. If it is, the walk accepted a refutation that does
/// not rest on the problem, and that is recorded as a refusal.
pub(in super::super) fn mirror_certificate_with_control(problem: &str, proof: &str) -> Coverage {
    let mut coverage = walk(problem, proof, None, true).0;
    assert!(
        !problem.contains("define-fun-rec"),
        "the control drops assertions only from a problem without recursive definitions"
    );
    if walk(problem, proof, None, false).0.checked() {
        coverage.refused.push(
            "document: counted as checked against the problem with every assertion dropped"
                .to_string(),
        );
    }
    coverage
}

/// The mirror's verdict on the one step `id`: `accepted`, `refused: …` or
/// `undetermined: …` (`None` when no step has that id).
pub(in super::super) fn step_verdict(problem: &str, proof: &str, id: &str) -> Option<String> {
    walk(problem, proof, Some(id), true).1
}

fn walk(
    problem: &str,
    proof: &str,
    focus: Option<&str>,
    asserted: bool,
) -> (Coverage, Option<String>) {
    let mut focused = None;
    let mut document = Document::read_as_consumer(problem, proof);
    if !asserted {
        document.assertions.clear();
    }
    let commands = std::mem::take(&mut document.commands);
    let mut scope = Scope::default();
    let mut coverage = Coverage::default();
    document_refusals(&document, &mut coverage);
    // A top-level `(cl)` resting on no local assumption, and whether every
    // command it rests on was accepted.
    let mut empty_clauses: Vec<(&str, bool)> = Vec::new();
    for command in &commands {
        match command {
            Command::Anchor(end, context) => scope.frames.push(Frame {
                end,
                context: *context,
                declared: Vec::new(),
                last: None,
                local_assumes: Vec::new(),
            }),
            Command::Assume(id, term) => {
                let term = document.expand(term);
                // The consumer ignores an assumption local to a subproof: the
                // mirror lets everything derived from it rest on it.
                let fact = if scope.frames.is_empty() {
                    let verdict = assumption(&mut document, term);
                    let accepted = verdict.is_ok();
                    coverage.record(id, "assume", verdict);
                    Fact {
                        clause: vec![term],
                        rests_on: BTreeSet::new(),
                        accepted,
                    }
                } else {
                    Fact {
                        clause: vec![term],
                        rests_on: BTreeSet::from([id.as_str()]),
                        accepted: true,
                    }
                };
                if !scope.declare(id, fact) {
                    coverage
                        .refused
                        .push(format!("assume {id}: a repeated command id"));
                }
                scope.assumptions.insert(id, term);
                if let Some(frame) = scope.frames.last_mut() {
                    frame.local_assumes.push(id);
                }
            }
            Command::Step(step) => {
                let fact = check_step(
                    &mut document,
                    &mut scope,
                    &mut coverage,
                    step,
                    focus,
                    &mut focused,
                );
                if fact.clause.is_empty() && scope.frames.is_empty() {
                    if fact.rests_on.is_empty() {
                        empty_clauses.push((&step.id, fact.accepted));
                    } else {
                        coverage.refused.push(format!(
                            "document: the empty clause {} rests on the undischarged local \
                             assumptions {:?}",
                            step.id, fact.rests_on
                        ));
                    }
                }
            }
        }
    }
    close_walk(&scope, &mut coverage, empty_clauses);
    (coverage, focused)
}

/// The document-level refusals that precede the walk: a problem that is not
/// one query, a proof definition the mirror does not read as the consumer
/// does, and a proof that redefines a symbol the problem uses.
fn document_refusals(document: &Document, coverage: &mut Coverage) {
    for defect in &document.problem_defects {
        coverage
            .refused
            .push(format!("document: the problem is not one query: {defect}"));
    }
    // A stricter rule than the consumer's (whose parser lets a proof macro
    // shadow a problem symbol in the proof's own terms): a proof may not
    // (re)define a name the problem uses, so a premise and a proof term
    // spelled alike are one term.
    for defect in &document.proof_defects {
        coverage.refused.push(format!(
            "document: the proof is not read as the consumer reads it: {defect}"
        ));
    }
    for name in &document.redefined {
        coverage.refused.push(format!(
            "document: the proof defines {name}, a symbol the problem uses"
        ));
    }
}

/// The document-level refusals after the walk (an unclosed subproof, no
/// empty clause), and the first accepted top-level empty clause as the
/// refutation.
fn close_walk(scope: &Scope<'_>, coverage: &mut Coverage, empty_clauses: Vec<(&str, bool)>) {
    if !scope.frames.is_empty() {
        coverage
            .refused
            .push("document: a subproof is not closed".to_string());
    }
    if empty_clauses.is_empty() {
        coverage.refused.push(
            "document: the proof does not reach the empty clause from the problem's assertions"
                .to_string(),
        );
    }
    coverage.refutation = empty_clauses
        .into_iter()
        .find(|&(_, accepted)| accepted)
        .map(|(id, _)| id.to_string());
}

/// One step: its rule's verdict recorded, its fact declared in scope (the
/// subproof it closes, closed) and returned.
fn check_step<'a>(
    document: &mut Document,
    scope: &mut Scope<'a>,
    coverage: &mut Coverage,
    step: &'a Step,
    focus: Option<&str>,
    focused: &mut Option<String>,
) -> Fact<'a> {
    let conclusion: Vec<u32> = step.clause.iter().map(|t| document.expand(t)).collect();
    let args = step.args.iter().map(|arg| document.expand(arg)).collect();
    let premise_facts: Option<Vec<Fact<'a>>> = step
        .premises
        .iter()
        .map(|premise| scope.facts.get(premise.as_str()).cloned())
        .collect();
    let premises = premise_facts
        .as_ref()
        .map(|facts| facts.iter().map(|fact| fact.clause.clone()).collect());
    // Each discharged command, by the id it is in scope under.
    let discharged = discharged_ids(scope, step);
    let discharge: Option<Vec<Option<u32>>> = discharged.as_ref().map(|ids| {
        ids.iter()
            .map(|id| scope.assumptions.get(id).copied())
            .collect()
    });
    let closing = scope
        .frames
        .last()
        .is_some_and(|frame| frame.end == step.id);
    let previous_fact = closing
        .then(|| scope.frames.last().and_then(|f| f.last.clone()))
        .flatten();
    let previous = previous_fact.as_ref().map(|fact| fact.clause.clone());
    let in_context = scope.frames.iter().any(|frame| frame.context);
    let verdict = match (premises, discharge, mirrored(&step.rule)) {
        (None, _, _) | (_, None, _) => refuse("a premise or discharged id is not in scope"),
        _ if closing && previous.is_none() => refuse("a subproof without a command before its end"),
        (_, _, None) if matches!(step.rule.as_str(), "hole" | "lia_generic") => {
            refuse("a hole: the consumer reports the certificate holey")
        }
        (_, _, None) => undecided("the rule is not mirrored"),
        (Some(premises), Some(discharge), Some(check)) => {
            let input = StepInput {
                conclusion: conclusion.clone(),
                premises,
                args,
                in_context,
                previous,
                discharge,
            };
            check(document, &input)
        }
    };
    // A context's substitution may justify what the mirror refuses.
    let verdict = match verdict {
        Err(Verdict::Refused(why)) if in_context => undecided(format!("in a context: {why}")),
        verdict => verdict,
    };
    let verdict = structure(scope, step, closing, discharged.as_deref(), verdict);
    if focus == Some(step.id.as_str()) {
        *focused = Some(match &verdict {
            Ok(()) => "accepted".to_string(),
            Err(Verdict::Refused(why)) => format!("refused: {why}"),
            Err(Verdict::Undetermined(why)) => format!("undetermined: {why}"),
        });
    }
    // What the step's clause rests on: its premises and, at a subproof's
    // end, the command before it; an accepted `subproof` discharges its
    // assumptions (and nothing else does).
    let mut fact = Fact {
        clause: conclusion,
        rests_on: BTreeSet::new(),
        accepted: verdict.is_ok(),
    };
    for source in premise_facts.iter().flatten().chain(previous_fact.as_ref()) {
        fact.rests_on.extend(source.rests_on.iter().copied());
        fact.accepted &= source.accepted;
    }
    if closing && step.rule == "subproof" && verdict.is_ok() {
        for id in discharged.iter().flatten() {
            fact.rests_on.remove(id);
        }
    }
    coverage.record(&step.id, &step.rule, verdict);
    if closing {
        scope.close();
    }
    if !scope.declare(&step.id, fact.clone()) {
        coverage
            .refused
            .push(format!("step {}: a repeated command id", step.id));
    }
    fact
}

fn discharged_ids<'a>(scope: &Scope<'a>, step: &Step) -> Option<Vec<&'a str>> {
    step.discharge
        .iter()
        .map(|id| {
            let absolute = format!("{}.{id}", step.id);
            scope
                .facts
                .get_key_value(absolute.as_str())
                .or_else(|| scope.facts.get_key_value(id.as_str()))
                .map(|(&key, _)| key)
        })
        .collect()
}

/// The consumer's structural checks around the rule (`check_step_core`):
/// `:discharge` only on `subproof`; an end step discharges every assumption
/// made directly in its subproof; an end step of an anchor with `:args` is a
/// context-closing rule; and a premise crossing an anchor with `:args` is
/// subject to Clean's premise scoping, which is not mirrored.
fn structure(
    scope: &Scope<'_>,
    step: &Step,
    closing: bool,
    discharged: Option<&[&str]>,
    verdict: super::Checked,
) -> super::Checked {
    let hole = matches!(step.rule.as_str(), "hole" | "lia_generic");
    if !step.discharge.is_empty() && step.rule != "subproof" {
        return refuse("`:discharge` on a rule other than `subproof`");
    }
    if closing {
        let frame = scope.frames.last().expect("a closing step has a frame");
        // Each `:discharge` id as the consumer's parser resolves it (the
        // absolute `<end>.<id>` first); an unresolved one is refused above.
        let discharged = discharged.unwrap_or_default();
        if let Some(missing) = frame
            .local_assumes
            .iter()
            .find(|id| !discharged.contains(id))
        {
            return refuse(format!("the local assumption {missing} is not discharged"));
        }
        const CLOSING: &[&str] = &[
            "bind",
            "let",
            "onepoint",
            "sko_ex",
            "sko_forall",
            "bind_let",
        ];
        if frame.context && !hole && !CLOSING.contains(&step.rule.as_str()) {
            return refuse("a rule that cannot end a subproof whose anchor has arguments");
        }
    }
    if verdict.is_ok() {
        let depth = scope.frames.len();
        let level = if closing {
            depth.saturating_sub(1)
        } else {
            depth
        };
        for premise in &step.premises {
            let Some(&at) = scope.depths.get(premise.as_str()) else {
                continue;
            };
            let (low, high) = if at <= level {
                (at, level)
            } else {
                (level, at)
            };
            if scope.frames[low..high].iter().any(|frame| frame.context) {
                return undecided("a premise crosses an anchor with arguments: Clean's premise scoping is not mirrored");
            }
        }
    }
    verdict
}
