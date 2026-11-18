// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The unvalidated candidate model that `(get-model)` may print after an
//! `unknown` answer.
//!
//! z3 answers `unknown` on a query it cannot decide (for instance quantifiers
//! with MBQI off) and still answers `(get-model)` with the assignment its
//! search stopped at. Tools written against z3 read that assignment: Verus's
//! AIR reads its `%%location_label%%` constants to name the assertion that
//! failed. ay withholds every model one of its checks rejects, so after the
//! same `unknown` it has nothing to print.
//!
//! [`CandidateModelPolicy::PublishAfterUnknown`] keeps the models that checks
//! reject during the outermost `check-sat` / `check-sat-assuming` command, and
//! the ground model the quantifier loop declines to publish, and lets
//! `(get-model)` print one of them when that command answered `unknown` and
//! z3 would have kept a model (see [`Z3SolverPath`]). The default,
//! [`CandidateModelPolicy::Withhold`], keeps nothing and `(get-model)` after
//! `unknown` stays an error. Only the CLI's `--z3-mode` selects the publishing
//! policy.
//!
//! The candidate is printed as the search left it, including the values that
//! made a check reject it (an enumeration sort given more distinct values than
//! it has constructors, say), except that Boolean constants no assertion needs
//! true are printed false and symbols the printer cannot render are left out.
//!
//! A published candidate is never a validated model, and a consumer can tell:
//!
//! * it is printed only when the preceding check answered `unknown`; a model
//!   printed after `sat` is always the validated one;
//! * its text begins with [`UNVALIDATED_CANDIDATE_HEADER`];
//! * it is stored apart from `last_model`, so `get-value`, `eval`, the library
//!   API's model accessors and every internal reader of `last_model` never see
//!   it.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::TermId;
use ay_frontend::Command;

use crate::executor::Executor;
use crate::executor_format::format_sort_surface;
use crate::executor_types::SolveResult;

use super::Model;

mod booleans;
use booleans::AtomReading;

/// Comment line that opens a candidate model printed after `unknown`.
const UNVALIDATED_CANDIDATE_HEADER: &str =
    ";; candidate model after unknown: not validated, may violate the assertions";

/// Rejected models kept per decision command, newest last.
const CANDIDATE_CAPACITY: usize = 4;

/// Whether `(get-model)` after an `unknown` answer prints the rejected
/// candidate model.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CandidateModelPolicy {
    /// `(get-model)` after `unknown` answers `model is not available`.
    #[default]
    Withhold,
    /// `(get-model)` after `unknown` prints a candidate model a check rejected
    /// during that command, marked as unvalidated.
    PublishAfterUnknown,
}

/// The z3 solver a decision command reaches, which decides whether z3 keeps a
/// model after `unknown`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::executor) enum Z3SolverPath {
    /// The incremental solver: after a `push` (until `reset`), or for
    /// `check-sat-assuming`. It keeps the model its search stopped at.
    Incremental,
    /// The tactic z3 runs for a plain `check-sat` in a session that never
    /// pushed. It keeps no model after `unknown`.
    Tactic,
}

/// Whether rejected models are being recorded right now.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum CaptureWindow {
    #[default]
    Closed,
    /// Inside the outermost decision command of a publishing executor.
    Open,
}

/// The candidates an [`UnknownCandidate`] held at one point of a command.
#[derive(Debug)]
pub(in crate::executor) struct RecordedCandidates(Vec<Model>);

/// Per-executor state behind [`CandidateModelPolicy`].
#[derive(Debug, Default)]
pub(in crate::executor) struct UnknownCandidate {
    policy: CandidateModelPolicy,
    window: CaptureWindow,
    /// Rejected models of the current or last decision command, newest last.
    models: Vec<Model>,
}

impl UnknownCandidate {
    pub(in crate::executor) fn policy(&self) -> CandidateModelPolicy {
        self.policy
    }

    pub(in crate::executor) fn set_policy(&mut self, policy: CandidateModelPolicy) {
        self.policy = policy;
        if policy == CandidateModelPolicy::Withhold {
            self.window = CaptureWindow::Closed;
            self.models.clear();
        }
    }

    /// Start of an outermost `check-sat` / `check-sat-assuming` that z3 would
    /// run on `path`: forget the previous candidates and, where z3 would keep
    /// one, record rejections until [`Self::finish_check`].
    pub(in crate::executor) fn begin_check(&mut self, path: Z3SolverPath) {
        self.models.clear();
        self.window = match (self.policy, path) {
            (CandidateModelPolicy::PublishAfterUnknown, Z3SolverPath::Incremental) => {
                CaptureWindow::Open
            }
            _ => CaptureWindow::Closed,
        };
    }

    /// End of that command: stop recording, and keep the candidates only when
    /// the command's answer was `unknown`.
    pub(in crate::executor) fn finish_check(&mut self, answer: Option<&SolveResult>) {
        self.window = CaptureWindow::Closed;
        if !matches!(answer, Some(SolveResult::Unknown)) {
            self.models.clear();
        }
    }

    pub(in crate::executor) fn is_capturing(&self) -> bool {
        self.window == CaptureWindow::Open
    }

    /// Record `model` as the newest rejected candidate (no-op outside a window).
    pub(in crate::executor) fn record(&mut self, model: Model) {
        if !self.is_capturing() {
            return;
        }
        if self.models.len() == CANDIDATE_CAPACITY {
            self.models.remove(0);
        }
        self.models.push(model);
    }

    /// The assertion stack changed: the candidates no longer describe it.
    /// Invalidations inside the window are the solve's own bookkeeping and keep
    /// what was recorded so far.
    pub(in crate::executor) fn invalidate(&mut self) {
        if !self.is_capturing() {
            self.models.clear();
        }
    }

    /// A copy of the candidates recorded so far, for a later
    /// [`Self::restore_recorded`].
    pub(in crate::executor) fn recorded(&self) -> RecordedCandidates {
        RecordedCandidates(self.models.clone())
    }

    /// Put back the candidates [`Self::recorded`] copied, dropping the ones
    /// recorded since: for a solve attempt the command abandons, whose
    /// rejected models are not what the command's answer describes.
    pub(in crate::executor) fn restore_recorded(&mut self, recorded: RecordedCandidates) {
        self.models = recorded.0;
    }

    /// The candidates that may be printed after an answer of `answer`, newest
    /// first.
    pub(in crate::executor) fn for_answer(
        &self,
        answer: Option<&SolveResult>,
    ) -> impl Iterator<Item = &Model> {
        let publish = self.policy == CandidateModelPolicy::PublishAfterUnknown
            && matches!(answer, Some(SolveResult::Unknown));
        self.models.iter().rev().filter(move |_| publish)
    }
}

impl Executor {
    /// Select whether `(get-model)` after `unknown` prints the candidate model
    /// a check rejected. See [`CandidateModelPolicy`]; the default withholds it.
    pub fn set_candidate_model_policy(&mut self, policy: CandidateModelPolicy) {
        self.unknown_candidate.set_policy(policy);
    }

    /// The policy set by [`Self::set_candidate_model_policy`].
    #[must_use]
    pub fn candidate_model_policy(&self) -> CandidateModelPolicy {
        self.unknown_candidate.policy()
    }

    /// Open the candidate window for the outermost decision command `cmd`.
    ///
    /// z3 4.12.5 answers `(get-model)` after `unknown` only from its incremental
    /// solver; clients depend on the difference (AIR reports a Verus bit-vector
    /// query, which never pushes, differently when there is no model).
    pub(in crate::executor) fn begin_candidate_window(&mut self, cmd: &Command) {
        let path = if self.incremental_mode || matches!(cmd, Command::CheckSatAssuming(_)) {
            Z3SolverPath::Incremental
        } else {
            Z3SolverPath::Tactic
        };
        self.unknown_candidate.begin_check(path);
    }

    /// Clear `last_model` after a check rejected it, keeping it as a candidate
    /// when the policy publishes candidates.
    pub(in crate::executor) fn withdraw_rejected_model(&mut self) {
        if let Some(model) = self.last_model.take() {
            self.unknown_candidate.record(model);
        }
    }

    /// Keep `model`, which a check took out of `last_model` and rejected, as a
    /// candidate when the policy publishes candidates.
    pub(in crate::executor) fn keep_rejected_model(&mut self, model: Model) {
        self.unknown_candidate.record(model);
    }

    /// Keep a copy of `last_model` as a candidate after a check rejected it but
    /// left it in place.
    pub(in crate::executor) fn record_rejected_model(&mut self) {
        if let Some(model) = self.snapshot_candidate_model() {
            self.unknown_candidate.record(model);
        }
    }

    /// A copy of `last_model` for a later [`Self::keep_rejected_model`], taken
    /// only while candidates are being recorded.
    pub(in crate::executor) fn snapshot_candidate_model(&self) -> Option<Model> {
        if !self.unknown_candidate.is_capturing() {
            return None;
        }
        self.last_model.clone()
    }

    /// The candidate `(get-model)` prints after the current answer, or `None`.
    ///
    /// Candidates are tried newest first. One is published only when its
    /// Boolean constants falsify no assertion and no check-sat assumption with
    /// every other atom read as unknown. z3's candidate satisfies at least that
    /// skeleton; one that does not came from a search that never reached the
    /// query's goal (a probe that solved a different formula, say). Other
    /// values are not checked: the candidate failed a check, and may violate
    /// any assertion through them.
    pub(in crate::executor) fn publishable_candidate(&self) -> Option<Model> {
        let mut candidates = self
            .unknown_candidate
            .for_answer(self.last_result.as_ref())
            .peekable();
        candidates.peek()?;
        let mut roots: Vec<TermId> = self.ctx.assertions.clone();
        if let Some(assumptions) = self.last_assumptions.as_ref() {
            roots.extend(assumptions.iter().copied());
        }
        let mut withheld = false;
        for candidate in candidates {
            if self.poll_evaluation_stop().is_err() {
                return None;
            }
            let mut memo = HashMap::default();
            if roots.iter().any(|&root| {
                self.ground_truth(candidate, root, AtomReading::Skeleton, &mut memo) == Some(false)
            }) {
                withheld = true;
                continue;
            }
            return Some(self.prefer_false_booleans(candidate, &roots));
        }
        if withheld {
            eprintln!("c ay.model.candidate withheld: its Boolean constants falsify an assertion");
        }
        None
    }

    /// Finish the printed definitions of a candidate: open them with
    /// [`UNVALIDATED_CANDIDATE_HEADER`], and leave out (recording the symbol in
    /// `omitted`) each one that mentions a quoted symbol the problem does not
    /// declare. Such a symbol is a value the search left on a term of another
    /// kind (an arithmetic value on an uninterpreted constant, say): it names
    /// no element, and z3 clients' readers, AIR's among them, reject the
    /// quoted spelling.
    pub(in crate::executor) fn finish_candidate_definitions(
        &self,
        definitions: &mut Vec<String>,
        omitted: &mut Vec<String>,
    ) {
        let mut declared: HashSet<String> = HashSet::default();
        for (name, info) in self.ctx.symbol_iter() {
            declared.insert(name.clone());
            for sort in info.arg_sorts.iter().chain(std::iter::once(&info.sort)) {
                declared.extend(quoted_tokens(&format_sort_surface(&self.ctx, sort)));
            }
        }
        for (datatype, constructors) in self.ctx.datatype_iter() {
            declared.insert(datatype.to_string());
            declared.extend(constructors.iter().cloned());
        }
        definitions.retain(|definition| {
            let printable = quoted_tokens(definition)
                .iter()
                .all(|token| declared.contains(token));
            if !printable {
                let name = definition.trim_start().trim_start_matches("(define-fun ");
                let end = name.find(char::is_whitespace).unwrap_or(name.len());
                omitted.push(name[..end].to_string());
            }
            printable
        });
        definitions.insert(0, format!("  {UNVALIDATED_CANDIDATE_HEADER}"));
    }
}

/// The contents of the `|quoted|` symbols in `text`, skipping string literals.
/// Inside a quoted symbol a `\` takes the next character, so the escapes
/// `ay_core::quote_symbol` writes read back as the name: `|a\|b|` gives
/// `a|b`.
fn quoted_tokens(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut chars = text.chars().peekable();
    while let Some(chr) = chars.next() {
        match chr {
            '"' => {
                // Skip a string literal; `""` inside it is an escaped quote.
                while let Some(inner) = chars.next() {
                    if inner == '"' {
                        if chars.peek() == Some(&'"') {
                            chars.next();
                        } else {
                            break;
                        }
                    }
                }
            }
            '|' => {
                let mut token = String::new();
                while let Some(inner) = chars.next() {
                    match inner {
                        '|' => break,
                        '\\' => token.extend(chars.next()),
                        other => token.push(other),
                    }
                }
                tokens.push(token);
            }
            _ => {}
        }
    }
    tokens
}

#[cfg(test)]
mod tests;
