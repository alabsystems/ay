// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ONE reader for every judgement that consumes a rendered step.
//!
//! A rendered step is a sequence of Alethe COMMANDS — `(assume ..)`,
//! `(step ..)`, `(anchor ..)` — and a judgement that reads it has to read
//! those commands as objects. Three judgements read rendered text: the
//! arithmetic chokepoint (`la_generic` / `poly_simp`), the printed `or`
//! judgement, and the ledger `judge_printed_resolution` consults. Until
//! 2026-09-16 the first two read commands and the third read LINES:
//! `printed_conclusion_of` scanned `rendered.lines()` for the line that began
//! with `(step tN `, so a command spanning lines — a quoted symbol carrying a
//! newline, legal SMT-LIB 2.6 (`|g\nh|`), or a multi-line string literal —
//! yielded no balanced clause, nothing entered the ledger, and BOTH ledger
//! consumers took their "premise not recorded → unchanged" path.
//!
//! MEASURED on build 9706 (`d2eb507ab9`): greenflag14's shape with the
//! function symbol `|g\nh|` shipped `unproved_steps=0 ay_self_checkable=yes`
//! in the default, `--strict-proofs` and `--proof FILE` postures, and pinned
//! carcara 1.1.0 refused it at the `or` over the printed implication — the
//! tenth false green, reopened by a newline. The controls pin the
//! discriminator: a TAB or a CR inside the symbol is holed, a newline in a
//! symbol OUTSIDE the `or` premise's clause is holed, and a newline with no
//! violation is valid on both arms. Reachable: 12 of 3,000 sampled corpus
//! files carry a quoted symbol spanning a newline outside
//! `set-info`/`set-option` (BV/2017-Preiner-*), 16 carry a multi-line string
//! literal.
//!
//! Every reader now goes through [`printed_commands`], whose scanner is the
//! SMT-LIB-aware [`split_alethe_commands_bounded`]: quoted symbols, string
//! literals and `;` comments are opaque, and a command is a command whatever
//! lines it spans. No `.lines()` scan remains on any judging path.

use super::surface_tokens::{
    scan_quoted_symbol, scan_string_term, split_alethe_commands_bounded,
    split_smt_term_slices_bounded, AletheSurfaceParseError,
};

/// Byte cap on one rendered step handed to a printed-text judgement.
///
/// This may not sit BELOW what this printer itself emits for ONE step. The
/// packed BV circuit lane bounds its document at `bv_packed`'s 64 MiB and
/// `complete_blast`'s at its `MAX_COUNTED_TEXT_BYTES` (128 MiB since
/// 2026-09-30, when a document past 76 MiB became one sized by the
/// consumer's own work); the margin covers what a step adds around the
/// document (`clause.rs` opens a conjunction). A reader capped under those does not judge
/// such a step, it refuses it UNREAD: `printed_commands` gets
/// `Err(BudgetExceeded)` from `split_alethe_commands_bounded`,
/// `judge_printed_la_generic` falls through to its token backstop, and a
/// derivation AY fully derived and `check_proof_strict` accepted is published
/// as `:rule hole`. Measured 2026-09-19: the cell32, cell64 and output-memory
/// calling-frame lemmas render a ~31.8 MB step whose six `la_generic`
/// commands are valid instances, and every one of them shipped as a hole.
///
/// Raising this only widens what is actually READ and judged; nothing is
/// admitted unjudged. A command that fails its replay still collapses the
/// step to the honest hole. The scan cost is already paid today by the token
/// backstop, which walks the whole rendered text anyway.
/// Measured 2026-09-30: external-codegen's 64-bit `SDIV` definitional lemma renders
/// an 84.6 MB complete blast the consumer verifies, and this reader, capped
/// at 80 MiB, refused its `ite1`/`ite2` commands unread, publishing a hole.
pub(super) const MAX_STEP_BYTES: usize =
    super::complete_blast::MAX_COUNTED_TEXT_BYTES + 4 * 1024 * 1024;

/// One top-level command of a rendered step, read as an object.
pub(super) struct PrintedCommand<'a> {
    /// The command's immediate fields: `step`, `t14`, `(cl ..)`, `:rule`,
    /// `la_generic`, `:args`, `(1 1)`, ..
    fields: Vec<&'a str>,
}

impl<'a> PrintedCommand<'a> {
    /// The command keyword: `step`, `assume`, `anchor`, ..
    pub(super) fn head(&self) -> &'a str {
        self.fields[0]
    }

    /// The id a `step` or `assume` binds; `None` for every other command.
    pub(super) fn name(&self) -> Option<&'a str> {
        matches!(self.head(), "step" | "assume")
            .then(|| self.fields.get(1).copied())
            .flatten()
    }

    /// The field at `index`.
    pub(super) fn field(&self, index: usize) -> Option<&'a str> {
        self.fields.get(index).copied()
    }

    /// How many fields the command has.
    pub(super) fn field_count(&self) -> usize {
        self.fields.len()
    }

    /// The position of a keyword field (`:rule`, `:premises`, `:args`).
    pub(super) fn keyword_position(&self, keyword: &str) -> Option<usize> {
        self.fields.iter().position(|field| *field == keyword)
    }

    /// The field following a keyword.
    pub(super) fn keyword_value(&self, keyword: &str) -> Option<&'a str> {
        self.field(self.keyword_position(keyword)? + 1)
    }

    /// The rule field of a `step`.
    pub(super) fn rule(&self) -> Option<&'a str> {
        self.keyword_value(":rule")
    }

    /// What an external checker binds to this command's id: a `step`'s
    /// clause literals, or an `assume`'s one term. `None` for any other
    /// command, and for a `step` whose clause is not a readable `(cl ..)`.
    pub(super) fn conclusion(&self) -> Option<Vec<&'a str>> {
        match self.head() {
            "step" => clause_literals(self.field(2)?),
            "assume" => (self.fields.len() == 3).then(|| vec![self.fields[2]]),
            _ => None,
        }
    }

    /// The `:premises` list.
    pub(super) fn premises(&self) -> Option<Vec<&'a str>> {
        list_elements(self.keyword_value(":premises")?)
    }

    /// The `:args` list.
    pub(super) fn args(&self) -> Option<Vec<&'a str>> {
        list_elements(self.keyword_value(":args")?)
    }
}

/// One command of a rendered step as the reader found it.
pub(super) enum PrintedCommandRead<'a> {
    /// A balanced command whose fields were read.
    Command(PrintedCommand<'a>),
    /// A balanced command whose fields could not be split. Only a budget
    /// overrun can produce this; a judgement decides what to do with it on
    /// TOKENS ([`rendered_rule_field_names`]), never on `str::contains`.
    Unsplittable(&'a str),
}

/// Every top-level command of one rendered step.
///
/// `Err(Malformed)` when the text is not a whitespace/comment-separated
/// sequence of balanced commands, `Err(BudgetExceeded)` past
/// [`MAX_STEP_BYTES`]. The caller decides on tokens in either case.
pub(super) fn printed_commands(
    rendered: &str,
) -> Result<Vec<PrintedCommandRead<'_>>, AletheSurfaceParseError> {
    let commands = split_alethe_commands_bounded(rendered, MAX_STEP_BYTES)?;
    Ok(commands
        .into_iter()
        .map(|command| match command_fields(command) {
            Some(fields) => PrintedCommandRead::Command(PrintedCommand { fields }),
            None => PrintedCommandRead::Unsplittable(command),
        })
        .collect())
}

/// The immediate fields of one balanced command `(head f1 f2 ..)`; `None`
/// when they cannot be split or the command is empty.
fn command_fields(command: &str) -> Option<Vec<&str>> {
    let inner = command.strip_prefix('(')?.strip_suffix(')')?;
    let fields = split_smt_term_slices_bounded(inner, usize::MAX, MAX_STEP_BYTES).ok()?;
    (!fields.is_empty()).then_some(fields)
}

/// The literals of a printed `(cl ..)` clause; `None` for anything else.
pub(super) fn clause_literals(clause: &str) -> Option<Vec<&str>> {
    let inner = clause.strip_prefix("(cl")?.strip_suffix(')')?;
    if !inner.is_empty() && !inner.starts_with(char::is_whitespace) {
        return None;
    }
    split_smt_term_slices_bounded(inner, usize::MAX, MAX_STEP_BYTES).ok()
}

/// The elements of a printed `(a b ..)` list; `None` for anything else.
fn list_elements(list: &str) -> Option<Vec<&str>> {
    let inner = list.strip_prefix('(')?.strip_suffix(')')?;
    split_smt_term_slices_bounded(inner, usize::MAX, MAX_STEP_BYTES).ok()
}

/// Whether some `:rule` KEYWORD in `text` is followed by one of `rules`,
/// reading SMT-LIB tokens: a quoted symbol `|..|`, a string literal `".."`
/// and a `;` comment are opaque, so none of them can make this answer `true`.
///
/// The backstop for text [`printed_commands`] could not read. It decides on
/// tokens rather than on `str::contains`, which is the defect the command
/// reader exists to close: a quoted symbol or a string literal that spells a
/// rule is an operand, not a claim.
pub(super) fn rendered_rule_field_names(text: &str, rules: &[&str]) -> bool {
    let bytes = text.as_bytes();
    let mut index = 0usize;
    let mut previous: Option<&str> = None;
    while index < bytes.len() {
        let byte = bytes[index];
        if byte.is_ascii_whitespace() || byte == b'(' || byte == b')' {
            index += 1;
            continue;
        }
        if byte == b';' {
            while index < bytes.len() && bytes[index] != b'\n' {
                index += 1;
            }
            previous = None;
            continue;
        }
        let start = index;
        match byte {
            b'"' => match scan_string_term(bytes, index) {
                Ok(end) => index = end,
                Err(_) => return false,
            },
            b'|' => match scan_quoted_symbol(bytes, index) {
                Ok(end) => index = end,
                Err(_) => return false,
            },
            _ => {
                while index < bytes.len()
                    && !bytes[index].is_ascii_whitespace()
                    && !matches!(bytes[index], b'(' | b')' | b'"' | b'|' | b';')
                {
                    index += 1;
                }
            }
        }
        // ASCII delimiters and input boundaries only: valid UTF-8 slice ends.
        let token = &text[start..index];
        if previous == Some(":rule") && rules.contains(&token) {
            return true;
        }
        previous = Some(token);
    }
    false
}

#[cfg(test)]
mod tests {
    use super::{printed_commands, rendered_rule_field_names, PrintedCommandRead};

    fn commands(rendered: &str) -> Vec<(String, Option<String>, Option<Vec<String>>)> {
        printed_commands(rendered)
            .expect("readable")
            .into_iter()
            .map(|read| match read {
                PrintedCommandRead::Command(command) => (
                    command.head().to_string(),
                    command.name().map(ToString::to_string),
                    command
                        .conclusion()
                        .map(|literals| literals.iter().map(ToString::to_string).collect()),
                ),
                PrintedCommandRead::Unsplittable(text) => {
                    ("<unsplittable>".to_string(), Some(text.to_string()), None)
                }
            })
            .collect()
    }

    #[test]
    fn a_command_spanning_lines_is_one_command() {
        // The E03 shape: a quoted symbol carrying a newline, inside the
        // clause of the command that binds the id.
        let rendered = "(step t19 (cl (=> (>= c 0) (P (|g\nh| c)))) :rule resolution :premises (t18 t16))\n(step t20 (cl (P (|g\nh| c)) (not (>= c 0))) :rule or :premises (t19))";
        assert_eq!(
            commands(rendered),
            [
                (
                    "step".to_string(),
                    Some("t19".to_string()),
                    Some(vec!["(=> (>= c 0) (P (|g\nh| c)))".to_string()])
                ),
                (
                    "step".to_string(),
                    Some("t20".to_string()),
                    Some(vec![
                        "(P (|g\nh| c))".to_string(),
                        "(not (>= c 0))".to_string()
                    ])
                ),
            ]
        );
    }

    #[test]
    fn a_string_literal_spanning_lines_is_one_operand() {
        let rendered = "(assume t0 (= s \"a\nb\"))";
        assert_eq!(
            commands(rendered),
            [(
                "assume".to_string(),
                Some("t0".to_string()),
                Some(vec!["(= s \"a\nb\")".to_string()])
            )]
        );
    }

    #[test]
    fn keyword_fields_are_read_as_fields() {
        let rendered = "(step t3.p (cl (not a) b) :rule la_generic :args (1 1))\n(step t3 (cl b) :rule resolution :premises (t2 t3.p t1))";
        let read = printed_commands(rendered).expect("readable");
        let [PrintedCommandRead::Command(bridge), PrintedCommandRead::Command(step)] =
            read.as_slice()
        else {
            panic!("two commands");
        };
        assert_eq!(bridge.rule(), Some("la_generic"));
        assert_eq!(bridge.args(), Some(vec!["1", "1"]));
        assert_eq!(bridge.premises(), None);
        assert_eq!(step.rule(), Some("resolution"));
        assert_eq!(step.premises(), Some(vec!["t2", "t3.p", "t1"]));
        assert_eq!(step.field_count(), 7);
    }

    #[test]
    fn an_anchor_or_a_comment_binds_nothing() {
        assert_eq!(
            commands("; t7 witness\n(anchor :step t7 :args ((:= (z Int) c)))"),
            [("anchor".to_string(), None, None)]
        );
    }

    #[test]
    fn a_spelling_of_a_rule_inside_an_operand_is_not_a_rule_field() {
        for text in [
            "(assume t0 (= (|f :rule or| x) 1))",
            "(assume t0 (= s \" :rule la_generic :args (1 1)\"))",
            "; :rule or",
            "(assume t0 (= (|f\n:rule or\n| x) 1))",
        ] {
            assert!(
                !rendered_rule_field_names(text, &["or", "la_generic"]),
                "{text}"
            );
        }
        assert!(rendered_rule_field_names(
            "(step t1 (cl a b) :rule or :premises (t0)",
            &["or"]
        ));
        assert!(!rendered_rule_field_names(
            "(step t1 (cl a b) :rule or_pos :args (0))",
            &["or"]
        ));
    }
}
