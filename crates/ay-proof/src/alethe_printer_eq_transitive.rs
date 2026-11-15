// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface admissibility for Alethe `eq_transitive` steps.
//!
//! `eq_transitive` is a premise-free tautology whose validity is a RELATION
//! among its operands — a transitivity chain — not merely a shape. The surface
//! override channel re-spells operands independently of the term DAG, so a
//! clause that is a perfect chain over the term store can print as a clause
//! that is no chain at all. The check therefore has to run over the text the
//! document ships, which is what [`printed_eq_transitive_chain_holds`] does:
//! it replays the pinned checker's own decision procedure.

use ay_core::{ProofId, TermId, TheoryLemmaKind, UNPROVED_STEP_RULE};

use super::surface_literal::equal_modulo_bitvec_literal_spelling;
use super::{split_alethe_application_bounded, AlethePrinter};

#[path = "alethe_printer_eq_transitive_arith.rs"]
mod arith;
pub use arith::arith_equality_chain_lowering_supported;
#[path = "alethe_printer_eq_transitive_bridge.rs"]
mod bridge;
pub(super) use bridge::bridged_printed_equality;

/// Literal count above which the chain replay declines rather than scanning.
/// `find_chain` is quadratic in the hypothesis count, so this caps emission
/// work; a clause this wide is far outside any shape AY produces.
const MAX_CHAIN_LITERALS: usize = 1_024;

/// Byte cap on one rendered literal handed to the balanced tokenizer.
const MAX_CHAIN_TERM_BYTES: usize = 1024 * 1024;

impl AlethePrinter<'_> {
    /// Resugar supported aliases or decline an unrenderable step to `hole`.
    pub(super) fn format_eq_transitive_or_hole(
        &self,
        id: ProofId,
        clause: &[TermId],
        kind: &TheoryLemmaKind,
    ) -> Option<String> {
        // An equality chain the arithmetic battery labelled first: spelled
        // only when its printed text chains, else `None` (later lanes, then
        // the hole). See `arith`.
        if matches!(kind, TheoryLemmaKind::ArithClauseTautology) {
            return self.format_arith_equality_chain(id, clause);
        }
        if kind.alethe_rule() != "eq_transitive" {
            return None;
        }
        if let [unit] = clause {
            // The OR-packed unit is rendered ONCE, by the same literal
            // renderer `format_clause` uses; the spelling and the decline
            // both ship that exact text.
            let mut printed = String::new();
            self.write_derived_literal_into(&mut printed, *unit);
            return Some(self.packed_eq_transitive_or_hole(id, &printed));
        }
        if let Some(text) = self.resugar_eq_transitive(id, clause) {
            return Some(text);
        }
        (!self.eq_transitive_prints_spec_valid(clause))
            .then(|| self.eq_transitive_bridged_or_hole(id, clause))
    }

    /// Spell the OR-packed transitivity unit `(cl (or ¬e_1 .. ¬e_k e))` as a
    /// derivation the pinned checker re-runs, or decline it to `hole`.
    ///
    /// The lazy-EUF lane states every transitivity explanation as ONE
    /// or-literal (the `EufTransitive` validator flattens it), and the flat
    /// `eq_transitive` spelling above cannot carry a one-literal clause. On the
    /// 31-document evidence ledger this unit was 974 of the 1,524 residual
    /// holes (2026-09-20), every one a pure chain consumed by a single `or`
    /// unpack. The spelling:
    ///
    /// ```text
    /// (step t.et (cl ¬e_1 .. ¬e_k e) :rule eq_transitive)
    /// (step t.o0 (cl (or ¬e_1 .. e) (not ¬e_1)) :rule or_neg :args (0))
    /// ...
    /// (step t.o{k} (cl (or ¬e_1 .. e) (not e)) :rule or_neg :args (k))
    /// (step t (cl (or ¬e_1 .. e)) :rule resolution :premises (t.et t.o0 .. t.o{k}))
    /// ```
    ///
    /// Everything is built from `printed` — the exact text the unit ships —
    /// and its immediate `or` operands as the balanced tokenizer reads them,
    /// never from the term DAG: `t.et` is judged by
    /// [`printed_eq_transitive_chain_holds`] over those operand strings (the
    /// replay of carcara's `find_chain`, which orients every hypothesis
    /// itself, so a flipped equality needs no `eq_symmetric`); each `or_neg`
    /// quotes the operand at the index it names; and the closing
    /// `resolution` is the RUP the checker replays (`¬(or ..)` reduces every
    /// `or_neg` to the negation of one disjunct, and those empty `t.et`).
    ///
    /// When the printed operands do not chain, `t.et` is instead the checked
    /// derivation [`bridge`] gives the flat path (43a040081) for that same
    /// clause, if the only breaks are alternate spellings of closed
    /// bit-vector terms or same-index reads over writes; the `or_neg` repack
    /// is unchanged. Anything else —
    /// the sixth false green's re-spelled surface, a `(distinct ..)` or
    /// n-ary `=` hypothesis, a link through an operator pinned carcara
    /// evaluates wrongly, fewer than three operands with no bridged link
    /// (carcara's `eq_transitive` floor) — ships as the honest hole over the
    /// same text.
    fn packed_eq_transitive_or_hole(&self, id: ProofId, printed: &str) -> String {
        let hole = || format!("(step {id} (cl {printed}) :rule {UNPROVED_STEP_RULE})");
        let Ok(disjuncts) = split_alethe_application_bounded(
            printed,
            "or",
            MAX_CHAIN_LITERALS,
            MAX_CHAIN_TERM_BYTES,
        ) else {
            return hole();
        };
        let Some(chain) = self.printed_chain_step(&format!("{id}.et"), &disjuncts) else {
            return hole();
        };
        or_neg_repack(id, printed, &disjuncts, &chain)
    }

    /// Step `name`, concluding the flat clause `(cl <literals>)`: the plain
    /// `eq_transitive` when the printed literals chain, else the
    /// closed-spelling bridge's checked derivation of exactly that clause,
    /// else `None` (the caller's hole). Shared by the OR-packed unit (as
    /// `{id}.et`) and the equality-predicate `eq_congruent_pred` lowering.
    pub(super) fn printed_chain_step(&self, name: &str, literals: &[&str]) -> Option<String> {
        let clause = format!("(cl {})", literals.join(" "));
        if printed_eq_transitive_chain_holds(literals) {
            return Some(format!("(step {name} {clause} :rule eq_transitive)"));
        }
        if self.work_budget_exhausted() {
            return None;
        }
        let bridged = bridge::bridged_eq_transitive(name, &clause)?;
        self.charge(bridged.len() as u64);
        Some(bridged)
    }

    /// An `eq_transitive` the printed text does not instantiate.
    ///
    /// When the only breaks in the printed chain are alternate spellings of
    /// closed bit-vector terms or same-index reads over writes (the authored
    /// surface re-spells a term AY folded), [`bridge`] proves each missing
    /// link with `evaluate`/`arrays_idx`/`cong` and closes the chain with
    /// checked rules over the same printed clause.
    /// Otherwise this is the honest decline: the clause still ships, named as
    /// unproved.
    pub(super) fn eq_transitive_bridged_or_hole(&self, id: ProofId, clause: &[TermId]) -> String {
        let printed = self.format_clause(clause);
        if !self.work_budget_exhausted() {
            if let Some(bridged) = bridge::bridged_eq_transitive(&id.to_string(), &printed) {
                self.charge(bridged.len() as u64);
                return bridged;
            }
        }
        format!("(step {id} {printed} :rule {UNPROVED_STEP_RULE})")
    }

    /// Whether the active surface is accepted by Alethe `eq_transitive`.
    ///
    /// Judged over the PRINTED clause, never over the term DAG. Before
    /// 2026-09-12 this asked only for shapes — one literal starting `(= `, two
    /// or more starting `(not (= ` — which is necessary and nowhere near
    /// sufficient. The QF_SLIA `2019-Leetcode partition` refutation shipped a
    /// hole-free, `ay_self_checkable=yes` document on exactly that gap: AY's
    /// chain is over `(= (str.at s 2) (str.at s 4))` and friends, the authored
    /// surface re-spells each of those atoms as its
    /// `(= (ite (not (= …)) 1 0) 0)` encoding, every literal still has the
    /// right shape, and no chain survives. Pinned carcara 1.1.0 answers
    /// `broken transitivity chain`.
    pub(super) fn eq_transitive_prints_spec_valid(&self, clause: &[TermId]) -> bool {
        if clause.len() > MAX_CHAIN_LITERALS {
            return false;
        }
        let printed: Vec<String> = clause.iter().map(|&lit| self.format_term(lit)).collect();
        let borrowed: Vec<&str> = printed.iter().map(String::as_str).collect();
        printed_eq_transitive_chain_holds(&borrowed)
    }
}

/// The OR-packed unit `(cl {printed})` from `chain`, a step named `{id}.et`
/// whose clause is exactly the printed `disjuncts` in any order: one `or_neg`
/// per disjunct, then the `resolution` that ships the unit's exact text under
/// the step's own id (see `packed_eq_transitive_or_hole`).
fn or_neg_repack(id: ProofId, printed: &str, disjuncts: &[&str], chain: &str) -> String {
    let mut out = String::with_capacity(chain.len() + printed.len() * (disjuncts.len() + 2));
    out.push_str(chain);
    out.push('\n');
    let mut premises = format!("{id}.et");
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

/// Replay pinned carcara 1.1.0's `eq_transitive` decision procedure over the
/// exact literal text a step is about to ship.
///
/// Mirrors `carcara/src/checker/rules/transitivity.rs::eq_transitive`:
///
/// * at least three literals (`assert_clause_len(conclusion, 3..)`);
/// * the LAST literal is the chain's conclusion and must be a binary `(= t u)`;
/// * every earlier literal must be a `(not (= t u))` hypothesis;
/// * `find_chain` walks greedily from `t` to `u`, consuming at most one
///   hypothesis per hop and never backtracking. Leftover hypotheses are fine
///   (extra disjuncts only weaken the clause); a hop with no matching
///   hypothesis is the `BrokenTransitivityChain` refusal.
///
/// Operand comparison is [`equal_modulo_bitvec_literal_spelling`] rather than
/// byte equality, matching carcara's term identity on the two ways the printed
/// surface can spell one term differently: whitespace inside an application,
/// and alternate bit-vector literal spellings. carcara parses both to one term.
pub(super) fn printed_eq_transitive_chain_holds(literals: &[&str]) -> bool {
    if !(3..=MAX_CHAIN_LITERALS).contains(&literals.len()) {
        return false;
    }
    let Some((conclusion, hypotheses)) = literals.split_last() else {
        return false;
    };
    let Some((goal_left, goal_right)) = split_printed_equality(conclusion) else {
        return false;
    };
    let mut premises: Vec<(&str, &str)> = Vec::with_capacity(hypotheses.len());
    for hypothesis in hypotheses {
        let Some(negated) = split_printed_negation(hypothesis) else {
            return false;
        };
        let Some(pair) = split_printed_equality(negated) else {
            return false;
        };
        premises.push(pair);
    }
    find_chain(goal_left, goal_right, &mut premises)
}

/// carcara's `find_chain`, iterated. `start` marks the prefix of `premises`
/// already consumed, which is exactly the `premises.swap(0, index)` plus
/// `&mut premises[1..]` recursion the checker performs.
fn find_chain(goal_left: &str, goal_right: &str, premises: &mut [(&str, &str)]) -> bool {
    let mut left = goal_left;
    let mut start = 0usize;
    loop {
        if equal_modulo_bitvec_literal_spelling(left, goal_right) {
            return true;
        }
        let step = (start..premises.len()).find_map(|index| {
            let (first, second) = premises[index];
            if equal_modulo_bitvec_literal_spelling(first, left) {
                Some((index, second))
            } else if equal_modulo_bitvec_literal_spelling(second, left) {
                Some((index, first))
            } else {
                None
            }
        });
        let Some((index, next)) = step else {
            return false;
        };
        premises.swap(start, index);
        start += 1;
        left = next;
    }
}

/// One rendered binary `(= a b)` split into its two operand renderings.
fn split_printed_equality(term: &str) -> Option<(&str, &str)> {
    let operands = split_alethe_application_bounded(term, "=", 2, MAX_CHAIN_TERM_BYTES).ok()?;
    match operands.as_slice() {
        [left, right] => Some((left, right)),
        _ => None,
    }
}

/// One rendered `(not X)` split into `X`.
fn split_printed_negation(term: &str) -> Option<&str> {
    let operands = split_alethe_application_bounded(term, "not", 1, MAX_CHAIN_TERM_BYTES).ok()?;
    match operands.as_slice() {
        [only] => Some(only),
        _ => None,
    }
}

#[cfg(test)]
#[path = "alethe_printer_eq_transitive_tests.rs"]
mod tests;
