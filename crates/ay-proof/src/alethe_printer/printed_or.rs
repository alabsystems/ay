// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Judge a printed `:rule or` over the term it actually ships.
//!
//! `or` is the clausification step every quantifier instantiation ends with:
//! `forall_inst` concludes the unit clause `(cl (or (not (forall ..)) INST))`
//! and `or` decomposes it into `(cl (not (forall ..)) INST)`. The rule is a
//! function of the PREMISE'S PRINTED TERM, so no premise-free template can
//! judge it, and until 2026-09-16 nothing did.
//!
//! # The false green (the ledger's TENTH shape)
//!
//! Six lines of UFLIA, corpus-free, `main` and every branch beside it:
//!
//! ```smt2
//! (set-logic UFLIA)
//! (declare-fun P (Int) Bool)
//! (declare-fun g (Int) Int)
//! (assert (forall ((y Int)) (! (=> (>= y 0) (P (g y))) :pattern ((P (g y))))))
//! (assert (not (forall ((z Int)) (or (< z 0) (P (g (ite (= z z) z 0)))))))
//! (check-sat)
//! ```
//!
//! `unproved_steps=0 ay_self_checkable=yes` in the default, `--proof` and
//! `--strict-proofs` postures; pinned carcara 1.1.0:
//!
//! ```text
//! [ERROR] checking failed on step 't20' with rule 'or': term '(=> ..)' is of
//!         the wrong form, expected '(or ...)'
//! ```
//!
//! Elaboration represents the authored `(=> A B)` as the internal or-term
//! `(or (not A) B)`, so the tracker's `or` decomposition is a correct step
//! over the object AY reasoned about. The printed document states the
//! AUTHORED implication — as it must, since the `assume` has to match the
//! problem's own text — and then claims `or` over it. The same shape as the
//! sixth through ninth: the object AY verified and the object it ships are
//! not the same object. It is NOT the Skolem channel: the control with the
//! `(ite (= z z) z 0)` simplification removed is equally green and equally
//! refused.
//!
//! # The check
//!
//! Carcara's `or` (`checker/rules/clausification.rs`), MEASURED on the pinned
//! 1.1.0 build rather than read from the older local checkout: the premise's
//! printed clause must be exactly ONE literal, that literal must be an
//! `(or ...)` application, the conclusion must have the same number of
//! literals, and each conclusion literal must EQUAL the operand at its own
//! index — positionally, not as a set (probe `b`: `(cl q p)` from `(or p q)`
//! is `invalid`, "expected terms to be equal: 'p' and 'q'"; probe `c`:
//! `(cl (not p) q)` from `(=> p q)` is `invalid`, the exact error above).
//!
//! Equality is compared over the printed text through
//! [`super::printed_resolution::normalise_printed_spelling`], the same
//! parser-level collapse the resolution judgement uses, so two spellings the
//! checker's parser interns as one term are not read as a divergence.
//!
//! A refusal declines the step to the honest `hole` over its own clause. The
//! derivation exists; what does not exist is a printed `or` instance, and a
//! hole says exactly that.
//!
//! # The `ite` projections
//!
//! `ite1` / `ite2` / `not_ite1` / `not_ite2` are the same kind of function of
//! the premise's PRINTED term, and this pass judges them the same way (the
//! instance check lives in [`ite`]). Until 2026-09-25 nothing did: the
//! array-frame update axiom's instance shipped `ite1` over its AUTHORED
//! equality spelling under `unproved_steps=0 trust_free=yes`, and pinned
//! carcara refused the document.

mod ite;

use super::printed_command::{printed_commands, rendered_rule_field_names, PrintedCommandRead};
use super::printed_resolution::{normalise_printed_spelling, PrintedClause};
use super::{AlethePrintError, AlethePrinter};
use ay_core::kani_compat::DetHashMap;
use ay_core::{ProofId, ProofStep, TermId};

/// The rules this pass judges: each is a function of the printed term of its
/// ONE premise, which no premise-free template can judge.
const JUDGED_PREMISE_RULES: &[&str] = &["or", "ite1", "ite2", "not_ite1", "not_ite2"];

/// Whether the printed-clause ledger must record the premises of `rule`
/// for this pass (`plan_printed_clause_demand`).
pub(super) fn is_judged_premise_rule(rule: &ay_core::AletheRule) -> bool {
    use ay_core::AletheRule as R;
    matches!(rule, R::Or | R::Ite1 | R::Ite2 | R::NotIte1 | R::NotIte2)
}

/// One `(step NAME (cl ..) :rule R :premises (P))` command with `R` in
/// [`JUDGED_PREMISE_RULES`], read as a command object and never as a line of
/// text.
pub(super) struct PrintedPremiseRule<'a> {
    /// The command's own id token.
    pub name: &'a str,
    /// The command's rule field.
    pub rule: &'a str,
    /// The printed conclusion literals.
    pub literals: Vec<&'a str>,
    /// The single premise token, when the command has exactly one.
    pub premise: Option<&'a str>,
}

/// One rendered step as this judgement reads it.
pub(super) struct PrintedPremiseStep<'a> {
    /// Every command whose RULE FIELD is a judged rule.
    pub commands: Vec<PrintedPremiseRule<'a>>,
    /// What every `step` / `assume` command in this rendering binds to its
    /// own name, so an `or` citing a sub-id bound in the same step (`t9.b0`)
    /// is judged against the clause that sub-id actually ships.
    pub bound: DetHashMap<&'a str, Option<Vec<&'a str>>>,
    /// A command the reader could not split whose TOKENS name a judged rule:
    /// a claim this judgement cannot read and therefore cannot approve.
    pub unreadable_claim: bool,
}

/// Read one rendered step for this judgement.
///
/// `None` when the rendered text is not a sequence of balanced commands.
/// A command whose rule field is judged but whose shape this reader cannot
/// decompose is returned with no premise, which the judgement refuses: a
/// reader that cannot read a step cannot approve it.
pub(super) fn read_printed_premise_step(rendered: &str) -> Option<PrintedPremiseStep<'_>> {
    let commands = printed_commands(rendered).ok()?;
    let mut step = PrintedPremiseStep {
        commands: Vec::new(),
        bound: DetHashMap::default(),
        unreadable_claim: false,
    };
    for read in commands {
        let command = match read {
            PrintedCommandRead::Command(command) => command,
            PrintedCommandRead::Unsplittable(text) => {
                step.unreadable_claim |= rendered_rule_field_names(text, JUDGED_PREMISE_RULES);
                continue;
            }
        };
        if let Some(name) = command.name() {
            step.bound.insert(name, command.conclusion());
        }
        let Some(rule) = command
            .rule()
            .filter(|rule| JUDGED_PREMISE_RULES.contains(rule))
        else {
            continue;
        };
        if command.head() != "step" {
            continue;
        }
        let Some(name) = command.name() else {
            continue;
        };
        let literals = command.conclusion().unwrap_or_default();
        let premise = command
            .premises()
            .and_then(|premises| match premises.as_slice() {
                [premise] => Some(*premise),
                _ => None,
            });
        step.commands.push(PrintedPremiseRule {
            name,
            rule,
            literals,
            premise,
        });
    }
    Some(step)
}

/// The `ProofId` a printed premise token names, `None` for a sub-id
/// (`t9.b0`) or anything else this printer binds below a step.
fn top_level_premise(token: &str) -> Option<ProofId> {
    token.strip_prefix('t')?.parse().ok().map(ProofId)
}

fn normalised(text: &str) -> String {
    let mut nodes = 0usize;
    normalise_printed_spelling(text, 0, &mut nodes)
}

/// Whether a printed `or` command is an instance of carcara's `or` over the
/// printed clause of its premise: a unit premise whose term is an `(or ..)`
/// of exactly the conclusion's literals, positionally.
fn printed_or_holds(premise: &[&str], literals: &[&str]) -> bool {
    let [premise_term] = premise else {
        // `get_premise_term`: the premise clause must be a unit.
        return false;
    };
    super::split_application(premise_term, "or").is_some_and(|operands| {
        operands.len() == literals.len()
            && operands
                .iter()
                .zip(literals.iter())
                .all(|(operand, literal)| normalised(operand) == normalised(literal))
    })
}

/// Whether one printed command instantiates its judged rule over the printed
/// clause of its premise.
fn printed_premise_rule_holds(command: &PrintedPremiseRule<'_>, premise: &[&str]) -> bool {
    match command.rule {
        "or" => printed_or_holds(premise, &command.literals),
        rule => ite::printed_ite_holds(rule, premise, &command.literals),
    }
}

impl AlethePrinter<'_> {
    /// Judge every `:rule or` / `ite1` / `ite2` / `not_ite1` / `not_ite2`
    /// command in one rendered step against the PRINTED conclusion of its
    /// premise.
    ///
    /// `Ok(rendered)` when every such command instantiates the rule, or when
    /// the ledger is inactive (an isolated helper or a unit test rendering
    /// one step, with nothing recorded to judge against). A refusal declines
    /// the step to the honest `hole` over its own clause — and a premise this
    /// judgement CANNOT READ is a refusal: a premise bound in this same
    /// rendering is read from it, a top-level premise is read from the
    /// ledger, and a premise the ledger holds as unreadable, unbounded or
    /// absent declines. Until 2026-09-16 an absent premise left the step
    /// unchanged, which is how a command spanning lines — a quoted symbol
    /// `|g\nh|` in the clause of the premise — reopened the tenth false
    /// green with every internal signal green.
    pub(super) fn judge_printed_premise_rules(
        &self,
        step: &ProofStep,
        id: ProofId,
        rendered: String,
    ) -> Result<String, AlethePrintError> {
        // A pre-filter only; the decision below reads commands.
        // Complete rule names only: the wire-rule inventory reads every
        // `:rule NAME` in a printer literal as a rule this printer emits, and
        // a bare `ite` / `not_ite` prefix is no rule pinned carcara knows.
        let may_claim = [
            ":rule or",
            ":rule ite1",
            ":rule ite2",
            ":rule not_ite1",
            ":rule not_ite2",
        ]
        .iter()
        .any(|claim| rendered.contains(claim));
        if !may_claim || !self.printed_clause_ledger_active.get() {
            return Ok(rendered);
        }
        let refused: Option<(String, &str)> = match read_printed_premise_step(&rendered) {
            None => {
                // Not a sequence of commands this reader can split. Decide
                // on TOKENS, not on `contains`: a quoted symbol or a string
                // literal that spells the rule is an operand, not a claim.
                rendered_rule_field_names(&rendered, JUDGED_PREMISE_RULES)
                    .then(|| (id.to_string(), "a judged premise rule"))
            }
            Some(read) if read.unreadable_claim => Some((id.to_string(), "a judged premise rule")),
            Some(read) => self
                .first_refused_premise_rule(&read)
                .map(|(name, rule)| (name.to_string(), rule)),
        };
        let Some((refused_name, refused_rule)) = refused else {
            return Ok(rendered);
        };
        if ay_core::misc_cli_flags().debug_cert {
            ay_core::safe_eprintln!(
                "c !! printed {refused_rule} at {id}: hole (refused {refused_name})"
            );
        }
        let clause: Option<&[TermId]> = match step {
            ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. }
            | ProofStep::Step { clause, .. } => Some(clause),
            _ => None,
        };
        let Some(clause) = clause else {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: format!(
                    "printed step `{refused_name}` claims `{refused_rule}` over a premise whose printed term does not instantiate it"
                ),
            });
        };
        Ok(format!(
            "(step {id} {} :rule {})",
            self.format_clause(clause),
            ay_core::UNPROVED_STEP_RULE
        ))
    }

    /// The `(name, rule)` of the first judged command in `read` that does not
    /// instantiate its rule over the printed clause of its premise, or whose
    /// premise this judgement cannot read.
    fn first_refused_premise_rule<'a>(
        &self,
        read: &PrintedPremiseStep<'a>,
    ) -> Option<(&'a str, &'a str)> {
        let recorded = self.printed_step_clauses.borrow();
        read.commands.iter().find_map(|command| {
            let refuse = || Some((command.name, command.rule));
            let Some(premise) = command.premise else {
                // No single premise token: a shape this reader cannot
                // decompose, or an arity the rule refuses.
                return refuse();
            };
            if let Some(bound) = read.bound.get(premise) {
                // Bound inside this same rendering.
                let Some(bound) = bound else {
                    return refuse();
                };
                return (!printed_premise_rule_holds(command, bound)).then(refuse)?;
            }
            let Some(premise_id) = top_level_premise(premise) else {
                // A sub-id this rendering does not bind.
                return refuse();
            };
            match recorded.get(&premise_id) {
                Some(PrintedClause::Literals(ids)) => {
                    // An id the atom table does not name is a premise this
                    // judgement cannot read, and a premise it cannot read it
                    // cannot approve. Spelled out rather than with `?`: inside
                    // this `find_map` closure `None` means "this command is
                    // fine", so `self.printed_atom_texts(ids)?` APPROVED the
                    // command — the silent shape, pinned by
                    // `an_unaddressable_atom_id_declines_both_judgements`.
                    // Unreachable today (every id is minted against this same
                    // table and both are cleared together in `prepare_proof`);
                    // if it ever becomes reachable it must fail loud, as the
                    // resolution judgement does.
                    let Some(texts) = self.printed_atom_texts(ids) else {
                        return refuse();
                    };
                    let literals: Vec<&str> = texts.iter().map(AsRef::<str>::as_ref).collect();
                    (!printed_premise_rule_holds(command, &literals)).then(refuse)?
                }
                // Unreadable, past the ledger's bounds, or never recorded:
                // the object the checker will read is not one this judgement
                // can read.
                Some(PrintedClause::Unreadable | PrintedClause::Unbounded) | None => refuse(),
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{read_printed_premise_step, top_level_premise};
    use ay_core::ProofId;

    fn read(rendered: &str) -> Vec<(String, Vec<String>, Option<String>)> {
        read_printed_premise_step(rendered)
            .expect("readable")
            .commands
            .into_iter()
            .map(|command| {
                (
                    command.name.to_string(),
                    command.literals.iter().map(ToString::to_string).collect(),
                    command.premise.map(ToString::to_string),
                )
            })
            .collect()
    }

    #[test]
    fn an_or_command_is_read_as_a_command() {
        let rendered = "(step t18 (cl (not (forall ((y Int)) (=> (>= y 0) (P y)))) (=> (>= c 0) (P c))) :rule or :premises (t17))";
        assert_eq!(
            read(rendered),
            [(
                "t18".to_string(),
                vec![
                    "(not (forall ((y Int)) (=> (>= y 0) (P y))))".to_string(),
                    "(=> (>= c 0) (P c))".to_string()
                ],
                Some("t17".to_string())
            )]
        );
        assert_eq!(top_level_premise("t17"), Some(ProofId(17)));
        // A sub-id is bound inside the same step; there is nothing recorded
        // to judge it against.
        assert_eq!(top_level_premise("t17.b0"), None);
        assert_eq!(top_level_premise("h1"), None);
    }

    #[test]
    fn a_quoted_symbol_or_string_spelling_the_rule_is_not_an_or_command() {
        // The same defect the arithmetic reader was refuted on: these are
        // operands, not rules.
        for rendered in [
            r#"(assume t0 (= (|f :rule or| x) 1))"#,
            r#"(assume t0 (= s "q :rule or :premises (t1)"))"#,
            "; :rule or",
        ] {
            assert!(read(rendered).is_empty(), "{rendered}");
        }
        // And a rule named `or_pos` is not `or`.
        assert!(read("(step t1 (cl (not (or a b)) a) :rule or_pos :args (0))").is_empty());
    }

    #[test]
    fn the_ite_projections_are_read_and_the_ite_tautologies_are_not() {
        let rendered = "(step t7 (cl (= 1 0) (= a b)) :rule ite1 :premises (t6))";
        let step = read_printed_premise_step(rendered).expect("readable");
        assert_eq!(step.commands.len(), 1);
        assert_eq!(step.commands[0].rule, "ite1");
        assert_eq!(step.commands[0].premise, Some("t6"));
        for rendered in [
            "(step t1 (cl (not (ite c p q)) c q) :rule ite_pos1)",
            "(step t1 (cl (= (= s s) (and (= s s) (ite c (= s a) (= s b))))) :rule ite_intro)",
        ] {
            assert!(read(rendered).is_empty(), "{rendered}");
        }
    }

    #[test]
    fn an_or_command_with_several_premises_has_no_single_premise_token() {
        let rendered = "(step t2 (cl a b) :rule or :premises (t0 t1))";
        assert_eq!(read(rendered)[0].2, None);
    }

    #[test]
    fn an_or_command_spanning_lines_is_read_as_one_command() {
        // The E03 shape: a legal quoted symbol carrying a newline inside the
        // conclusion. A line scan sees no balanced command; the reader does.
        let rendered = "(step t20 (cl (P (|g\nh| c)) (not (>= c 0))) :rule or :premises (t19))";
        assert_eq!(
            read(rendered),
            [(
                "t20".to_string(),
                vec!["(P (|g\nh| c))".to_string(), "(not (>= c 0))".to_string()],
                Some("t19".to_string())
            )]
        );
    }

    #[test]
    fn a_premise_bound_in_the_same_rendering_is_read_from_it() {
        let rendered =
            "(step t9.b0 (cl (or a b)) :rule hole)\n(step t9 (cl a b) :rule or :premises (t9.b0))";
        let step = read_printed_premise_step(rendered).expect("readable");
        assert_eq!(step.bound.get("t9.b0"), Some(&Some(vec!["(or a b)"])));
        assert!(!step.unreadable_claim);
        assert!(super::printed_or_holds(&["(or a b)"], &["a", "b"]));
        assert!(!super::printed_or_holds(&["(=> a b)"], &["(not a)", "b"]));
        assert!(!super::printed_or_holds(&["(or a b)"], &["b", "a"]));
        assert!(!super::printed_or_holds(&["(or a b)", "c"], &["a", "b"]));
    }
}
