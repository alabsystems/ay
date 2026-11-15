// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An `ArithClauseTautology` that is a pure equality chain prints as
//! `eq_transitive`.
//!
//! MEASURED 2026-10-09 at 2fc273d06, carcara 1.1.0 (git 9a352ee), plain
//! invocation: `benchmarks/smt/QF_AUFLIA/storeinv_sf_size7.smt2` published a
//! `holey` certificate whose only unproved step was
//! `(cl (or (not (= i2 i3)) (not (= i3 (sk a1 a2))) (= i2 (sk a1 a2))))`
//! (`c !! wire downgrade at ProofId(618): kind ArithClauseTautology prints as
//! hole`), and `storeinv_sf_size5.smt2` one eleven-disjunct chain over `select`
//! reads whose positive equality is the SECOND disjunct. Both are the packed
//! congruence-closure explanations `promote_intrinsic_tautology_leaves`
//! relabels, and its battery (`theory_inference::intrinsic`, order
//! load-bearing) asks the arithmetic recognizer before the EUF ones, so an
//! `Int`-sorted chain is filed `ArithClauseTautology`. No arithmetic lowering
//! can spell it: `la_generic` cannot negate the positive equality into one
//! linear row, `poly_simp` needs one polynomial identity, and the
//! `eq_transitive` spellings were keyed on the kind's own rule name.
//!
//! Its validity needs no arithmetic: read the one positive equality as the
//! conclusion and the clause is an `eq_transitive` instance. The spelling
//! moves that literal LAST in the chain step only; the step's own clause
//! keeps its recorded order and text, so no consumer moves:
//!
//! ```text
//! packed  (step t.et (cl ¬e_1 .. ¬e_k e) :rule eq_transitive)
//!         (step t.o{i} (cl (or ..) (not d_i)) :rule or_neg :args (i))  ; per disjunct
//!         (step t (cl (or ..)) :rule resolution :premises (t.et t.o0 ..))
//! flat    (step t (cl ..) :rule eq_transitive)          ; conclusion already last
//!         (step t.et (cl ¬e_1 .. ¬e_k e) :rule eq_transitive)  ; otherwise
//!         (step t (cl ..) :rule reordering :premises (t.et))
//! ```
//!
//! The kind authorizes nothing here. The chain step is the shared
//! `printed_chain_step`: [`super::printed_eq_transitive_chain_holds`] (the
//! replay of carcara's greedy `find_chain`) over the exact printed literals,
//! or the closed-spelling bridge's checked derivation of exactly them. A
//! clause with no or several positive equalities, a literal that is not an
//! equality, or a printed chain neither accepts answers `None`: the caller
//! tries its remaining lanes and finally keeps the honest `hole`.

use ay_core::kani_compat::DetHashMap;
use ay_core::{ProofId, TermId, TermStore};

use super::{or_neg_repack, split_printed_equality, MAX_CHAIN_LITERALS, MAX_CHAIN_TERM_BYTES};
use crate::alethe_printer::{split_alethe_application_bounded, AlethePrinter};

/// Rendering work one screen ask may spend on a single lemma.
const SCREEN_WORK_BUDGET: u64 = 4 * 1024 * 1024;

impl AlethePrinter<'_> {
    /// The checked `eq_transitive` spelling of an arithmetic tautology whose
    /// printed clause is an equality chain, or `None`. See the module docs.
    pub(super) fn format_arith_equality_chain(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        if clause.len() > MAX_CHAIN_LITERALS {
            return None;
        }
        if let [unit] = clause {
            // Rendered once, by the literal renderer `format_clause` uses.
            let printed = self.format_derived_literal(*unit);
            let disjuncts = split_alethe_application_bounded(
                &printed,
                "or",
                MAX_CHAIN_LITERALS,
                MAX_CHAIN_TERM_BYTES,
            )
            .ok()?;
            let chain = conclusion_last(&disjuncts)?;
            let step = self.printed_chain_step(&format!("{id}.et"), &chain)?;
            // The repack quotes the unit once per disjunct: charged before
            // it is built, as the negation-shell bridge charges its own. An
            // exhausted budget declines here and the step boundary discards
            // the document.
            let quoted = disjuncts.len() as u64 + 2;
            self.charge((printed.len() as u64).saturating_mul(quoted));
            if self.work_budget_exhausted() {
                return None;
            }
            return Some(or_neg_repack(id, &printed, &disjuncts, &step));
        }
        let printed = self.format_derived_clause_literals(clause);
        let literals: Vec<&str> = printed.iter().map(String::as_str).collect();
        let chain = conclusion_last(&literals)?;
        if chain == literals {
            return self.printed_chain_step(&id.to_string(), &literals);
        }
        let step = self.printed_chain_step(&format!("{id}.et"), &chain)?;
        Some(format!(
            "{step}\n(step {id} (cl {}) :rule reordering :premises ({id}.et))",
            literals.join(" ")
        ))
    }
}

/// `literals` with its one printed positive binary `(= ..)` moved last and
/// every other literal in its recorded order, or `None` unless exactly one
/// literal is a positive equality (carcara reads the conclusion off
/// `conclusion.last()` and requires every other literal to be negated).
fn conclusion_last<'t>(literals: &[&'t str]) -> Option<Vec<&'t str>> {
    let mut positives = literals
        .iter()
        .enumerate()
        .filter(|(_, literal)| split_printed_equality(literal).is_some());
    let (conclusion, _) = positives.next()?;
    if positives.next().is_some() {
        return None;
    }
    let mut chain: Vec<&str> = Vec::with_capacity(literals.len());
    chain.extend(
        literals
            .iter()
            .enumerate()
            .filter(|&(index, _)| index != conclusion)
            .map(|(_, literal)| *literal),
    );
    chain.push(literals[conclusion]);
    Some(chain)
}

/// Whether the exporter lowers this `ArithClauseTautology` clause to the
/// checked `eq_transitive` derivation above under `term_overrides` — the
/// wire-gap screen's question (`Executor::proof_has_known_wire_gap`). Each
/// ask renders under at most `SCREEN_WORK_BUDGET` and is charged to
/// `remaining_work`, the allowance the screen shares across one proof's
/// arithmetic lemmas, so many individually bounded lemmas cannot multiply it;
/// an exhausted allowance answers `false` and the screen keeps the gap.
#[must_use]
pub fn arith_equality_chain_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&DetHashMap<TermId, String>>,
    remaining_work: &mut u64,
) -> bool {
    if *remaining_work == 0 {
        return false;
    }
    let printer = AlethePrinter::new_with_overrides_and_budget(
        terms,
        term_overrides,
        Some((*remaining_work).min(SCREEN_WORK_BUDGET)),
    );
    let supported = printer
        .format_arith_equality_chain(ProofId(0), clause)
        .is_some();
    *remaining_work = remaining_work.saturating_sub(printer.work_used());
    supported && !printer.work_budget_exhausted()
}

#[cfg(test)]
#[path = "alethe_printer_eq_transitive_arith_tests.rs"]
mod tests;
