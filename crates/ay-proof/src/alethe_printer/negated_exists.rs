// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An external spelling of AY's `qnt_neg_exists` tautology.
//!
//! `qnt_neg_exists` concludes `(cl E F)` for `E = (exists B P)` and its De
//! Morgan dual `F = (forall B (not P))`. Pinned carcara has no rule of that
//! name, so the step printed as `hole` and every certificate that used the
//! dual (a negated existential, `(assert (not (exists ..)))`) was at best
//! holey. The tautology is derivable from rules carcara checks:
//!
//! ```text
//! tK.d  (cl (= E (not F)))                        connective_def
//! tK.p  (cl (not (= E (not F))) E (not (not F)))  equiv_pos1
//! tK.r  (cl E (not (not F)))                      resolution tK.d tK.p
//! tK.n  (cl (not (not (not F))) F)                not_not
//! tK    (cl E F)                                  resolution tK.r tK.n
//! ```
//!
//! MEASURED on pinned carcara 1.1.0 [9a352ee]: a hand-written certificate of
//! `(assert (not (exists ((x Int)) (< x 13))))` with exactly this chain checks
//! `valid`. The chain is printed only when the internal pair is the exact
//! dual AND the printed `E`/`F` are dual as text (same binder list, body
//! `(not P)`), since `connective_def` compares what it reads; otherwise the
//! step keeps its `hole`.

use super::surface_tokens::split_smt_terms;
use super::{AlethePrinter, AssembledRendering, HashMap};
use ay_core::{ProofId, TermData, TermId, TermStore};

impl AlethePrinter<'_> {
    /// The checked derivation of a `qnt_neg_exists` step, or `None` when the
    /// pair is not an exact (printed) dual.
    pub(super) fn format_qnt_neg_exists_chain(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let (e, f) = self.printed_negated_exists_duals(clause)?;
        let definition = format!("(= {e} (not {f}))");
        Some(format!(
            "(step {id}.d (cl {definition}) :rule connective_def)\n\
             (step {id}.p (cl (not {definition}) {e} (not (not {f}))) :rule equiv_pos1)\n\
             (step {id}.r (cl {e} (not (not {f}))) :rule resolution :premises ({id}.d {id}.p))\n\
             (step {id}.n (cl (not (not (not {f}))) {f}) :rule not_not)\n\
             (step {id} (cl {e} {f}) :rule resolution :premises ({id}.r {id}.n))"
        ))
    }

    fn printed_negated_exists_duals(&self, clause: &[TermId]) -> Option<(String, String)> {
        let [exists, forall] = clause else {
            return None;
        };
        let TermData::Exists(exists_binders, exists_body, _) = self.terms.get(*exists) else {
            return None;
        };
        let TermData::Forall(forall_binders, forall_body, _) = self.terms.get(*forall) else {
            return None;
        };
        if exists_binders != forall_binders
            || !matches!(self.terms.get(*forall_body), TermData::Not(inner) if inner == exists_body)
        {
            return None;
        }
        let e = self.format_term(*exists);
        let f = self.format_term(*forall);
        let (e_binders, e_body) = printed_quantifier(&e, "exists")?;
        let (f_binders, f_body) = printed_quantifier(&f, "forall")?;
        if e_binders != f_binders || f_body != format!("(not {e_body})") {
            return None;
        }
        Some((e, f))
    }
}

/// Whether the printer can derive this exact dual with standard Alethe rules
/// in the remaining proof-wide rendering allowance. Both the internal terms
/// and their effective wire spellings must match.
pub fn qnt_neg_exists_step_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    remaining: &mut u64,
) -> bool {
    if *remaining == 0 {
        return false;
    }
    let printer =
        AlethePrinter::new_with_overrides_and_budget(terms, term_overrides, Some(*remaining))
            .with_assembled_rendering(AssembledRendering::CachedWithinBudget);
    let duals = printer.printed_negated_exists_duals(clause);
    let used = printer.work_used().saturating_add(1);
    let fits = used <= *remaining;
    *remaining = remaining.saturating_sub(used);
    fits && !printer.work_budget_exhausted() && duals.is_some()
}

/// `(binder list, body)` of a printed `(QUANTIFIER (..) BODY)`.
fn printed_quantifier(printed: &str, quantifier: &str) -> Option<(String, String)> {
    let inner = printed.strip_prefix('(')?.strip_suffix(')')?;
    let tokens = split_smt_terms(inner)?;
    let [head, binders, body] = tokens.as_slice() else {
        return None;
    };
    (head == quantifier).then(|| (binders.clone(), body.clone()))
}
