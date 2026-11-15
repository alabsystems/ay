// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A lemma refuted by cases on an `ite` condition `(= v K)`, the printed
//! counterpart of the strict checker's `bv_bitblast/case_split.rs`.
//!
//! ```text
//! (anchor :step t.ks1)
//! (assume t.ks1.h c)              ; c is (= v K)
//!   ... the complete blast of A, v's bits bound to K's through t.ks1.h ...
//! (step t.ks1 (cl (not c) (not A)) :rule subproof :discharge (t.ks1.h))
//! (anchor :step t.ks2)
//! (assume t.ks2.h (not c))
//!   ... the complete blast of A with the unit (not c) ...
//! (step t.ks2 (cl (not (not c)) (not A)) :rule subproof :discharge (t.ks2.h))
//! (step t (cl (not A)) :rule resolution :premises (t.ks1 t.ks2))
//! ```
//!
//! Under `c` the variable `v` is blasted as the LITERAL's bits: `bitblast_const`
//! gives `K`'s, and `trans` with the assumption makes them `v`'s. Every
//! operator over `v` then meets constant bits — `bitblast_udiv` builds the
//! divider for a constant divisor — and a product by `v` is first re-spelled,
//! by `cong` from the assumption, as the product by the literal `K`, so the
//! non-adjacent form (`constant_product.rs`) replaces the multiplier array.
//! Under `(not c)` the assumption is one more unit clause.
//!
//! Each case is an ordinary complete blast, replayed from its own text before
//! it is printed, with its own step namespace and definition prefix; a case
//! that does not print leaves the lemma's honest `hole`.

use super::lazy::Orient;
use super::*;
use ay_core::TermStore;
use std::fmt::Write as _;

/// Case-split candidates tried at most per lemma.
const MAX_CANDIDATES: usize = 2;

/// One case of a split on `condition`, `(= variable value)`.
#[derive(Clone, Debug)]
pub(super) struct Case {
    condition: TermId,
    variable: TermId,
    value: TermId,
    holds: bool,
    /// The step that assumes the case: `condition` or its negation.
    hypothesis: String,
}

impl Case {
    fn binds(&self, term: TermId) -> bool {
        self.holds && term == self.variable
    }

    /// The case as a lemma's settled abstraction is keyed (`lazy.rs`): its
    /// printed condition and polarity, not the step that assumes it.
    pub(super) fn memo_key(&self, printer: &AlethePrinter<'_>) -> String {
        format!("{} {}", self.holds, printer.format_term(self.condition))
    }
}

/// `ite` conditions `(= v K)` or `(= K v)` below `root`, `v` a bit-vector
/// variable and `K` a literal, as `(condition, v, K)`.
fn candidates(terms: &TermStore, root: TermId) -> Vec<(TermId, TermId, TermId)> {
    let mut found: Vec<(TermId, TermId, TermId)> = Vec::new();
    let mut seen = DetHashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if seen.len() > MAX_TERM_NODES || found.len() >= MAX_CANDIDATES {
            break;
        }
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Ite(condition, then_branch, else_branch) => {
                if let Some((variable, value)) = variable_literal(terms, *condition) {
                    if !found.iter().any(|(seen, ..)| seen == condition) {
                        found.push((*condition, variable, value));
                    }
                }
                stack.extend([*condition, *then_branch, *else_branch]);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            _ => {}
        }
    }
    found
}

fn variable_literal(terms: &TermStore, condition: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(condition) else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    if name.as_ref() != "=" || !matches!(terms.sort(*left), Sort::BitVec(_)) {
        return None;
    }
    let is_var = |term: TermId| matches!(terms.get(term), TermData::Var(..));
    let is_literal =
        |term: TermId| matches!(terms.get(term), TermData::Const(Constant::BitVec { .. }));
    if is_var(*left) && is_literal(*right) {
        Some((*left, *right))
    } else if is_literal(*left) && is_var(*right) {
        Some((*right, *left))
    } else {
        None
    }
}

impl<'a, 'p> Blaster<'a, 'p> {
    /// The lemma `final_clause`, refuting `root` (oriented by `orient`) by
    /// cases, concluded as step `id`; `None` when no split prints.
    pub(super) fn case_split_document(
        printer: &'p AlethePrinter<'a>,
        id: ProofId,
        prefix: &str,
        root: TermId,
        orient: &Orient<'_, 'a, 'p>,
        final_clause: &str,
    ) -> Option<String> {
        let goal = final_clause.strip_prefix("(cl ")?.strip_suffix(')')?;
        'candidate: for (condition, variable, value) in candidates(printer.terms, root) {
            let condition_text = printer.format_term(condition);
            let mut document = String::new();
            for (index, holds) in [(1, true), (2, false)] {
                let anchor = format!("{id}.ks{index}");
                let hypothesis = format!("{anchor}.h");
                let assumed = if holds {
                    condition_text.clone()
                } else {
                    format!("(not {condition_text})")
                };
                let case = Case {
                    condition,
                    variable,
                    value,
                    holds,
                    hypothesis: hypothesis.clone(),
                };
                let unit = format!("{anchor}.u");
                let Some(inner) = Self::lemma_document(
                    printer,
                    id,
                    &format!("{prefix}k{index}_"),
                    &[root],
                    orient,
                    final_clause,
                    Some(&unit),
                    Some((&anchor, &case)),
                ) else {
                    continue 'candidate;
                };
                let _ = writeln!(
                    document,
                    "(anchor :step {anchor})\n(assume {hypothesis} {assumed})\n{inner}\n\
                     (step {anchor} (cl (not {assumed}) {goal}) :rule subproof :discharge ({hypothesis}))"
                );
            }
            let _ = write!(
                document,
                "(step {id} {final_clause} :rule resolution :premises ({id}.ks1 {id}.ks2))"
            );
            // Each case fit on its own; the consumer takes them together.
            return consumer_accepts(&document).then_some(document);
        }
        None
    }

    /// Install the case: under `(not c)`, the unit clause the assumption is.
    pub(super) fn assume_case(&mut self) -> Option<()> {
        let Some(case) = self.case.clone() else {
            return Some(());
        };
        if case.holds {
            return Some(());
        }
        let condition = self.bool_of.get(&case.condition).copied()?.not()?;
        let restated = self.step_name(".kh");
        let literal = self.circuit.text(condition);
        self.push_step(&format!(
            "(step {restated} (cl {literal}) :rule reordering :premises ({}))",
            case.hypothesis
        ))?;
        self.plan(vec![condition], ClauseEmit::Existing(restated))
    }

    /// The word of the case's variable under the case: the literal's bits.
    pub(super) fn case_bound_word(&mut self, term: TermId, width: u32) -> Option<Option<usize>> {
        let case = self.case.clone()?;
        if !case.binds(term) {
            return None;
        }
        Some(self.bind_case_variable(&case, width))
    }

    fn bind_case_variable(&mut self, case: &Case, width: u32) -> Option<usize> {
        let TermData::Const(Constant::BitVec { value, width: w }) =
            self.printer.terms.get(case.value).clone()
        else {
            return None;
        };
        if w != width || value.sign() == num_bigint::Sign::Minus {
            return None;
        }
        let bits: Vec<SRef> = (0..u64::from(width))
            .map(|i| self.circuit.constant(value.bit(i)))
            .collect();
        let bbterm = self.bbterm(&bits);
        let variable = self.printer.format_term(case.variable);
        let literal = self.printer.format_term(case.value);
        // `(= v K)`, whichever way the condition spells it.
        let oriented = match self.printer.terms.get(case.condition) {
            TermData::App(_, args) if args.first() == Some(&case.variable) => {
                case.hypothesis.clone()
            }
            _ => {
                let flipped = self.step_name(".ks");
                self.push_step(&format!(
                    "(step {flipped} (cl (= {variable} {literal})) :rule symm :premises ({}))",
                    case.hypothesis
                ))?;
                flipped
            }
        };
        let constant = self.step_name(".kc");
        let step = self.step_name(".kv");
        self.push_step(&format!(
            "(step {constant} (cl (= {literal} {bbterm})) :rule bitblast_const)"
        ))?;
        self.push_step(&format!(
            "(step {step} (cl (= {variable} {bbterm})) :rule trans :premises ({oriented} {constant}))"
        ))?;
        let reference = self.bind_word_reference(variable, width)?;
        self.words.push(Word {
            reference,
            width,
            bits,
            step,
        });
        let word = self.words.len() - 1;
        self.case_words.insert(word, (case.value, oriented));
        Some(word)
    }

    /// A product by the case's variable, re-spelled by `cong` as the product
    /// by its literal, then by the literal's non-adjacent form.
    pub(super) fn case_product(&mut self, operands: &[usize], width: u32) -> Option<usize> {
        let &[first, second] = operands else {
            return None;
        };
        let (bound, position) = [(second, 1_usize), (first, 0)]
            .into_iter()
            .find(|(word, _)| self.case_words.contains_key(word))?;
        let (value, oriented) = self.case_words.get(&bound)?.clone();
        let literal = self.build_word(value, width)?;
        let mut respelled = operands.to_vec();
        respelled[position] = literal;
        let product = self.constant_product(&respelled, width)?;
        let body = self.application("bvmul", operands);
        let reference = self.bind_word_reference(body, width)?;
        let literal_product = self.word_ref(product);
        let congruent = self.step_name(".kp");
        let step = self.step_name("");
        let product_step = self.words[product].step.clone();
        let bits = self.words[product].bits.clone();
        let bbterm = self.bbterm(&bits);
        self.push_step(&format!(
            "(step {congruent} (cl (= {reference} {literal_product})) :rule cong :premises ({oriented}))"
        ))?;
        self.push_step(&format!(
            "(step {step} (cl (= {reference} {bbterm})) :rule trans :premises ({congruent} {product_step}))"
        ))?;
        self.words.push(Word {
            reference,
            width,
            bits,
            step,
        });
        Some(self.words.len() - 1)
    }
}
