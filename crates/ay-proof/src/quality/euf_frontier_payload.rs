// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fresh per-step payload for fixed-size, opaque-operand EUF routes.
//!
//! Whole-proof term/type/declaration/arena/scope authentication is unchanged.
//! These validators then decode equality heads and compare operand TermIds;
//! they never read those operands' subtrees. Charge every decoded/cloned head
//! and argument vector anew, rather than visiting an opaque store tree again.
//! This is NOT a cross-step payload cache or a semantic acceptance shortcut.
//!
//! Scope is deliberately fixed-size: three-edge flat EufTransitive, one-premise
//! flat EufCongruent with at most four arguments, two-premise Step::Trans,
//! and direct-App Step::Cong with at most four arguments/four unit premises.
//! Every equality premise has at most one Not shell. Their graph/matcher
//! scratch and comparisons are bounded by the existing 8×work/4×byte model on
//! these heads. Step::Cong additionally pays its explicit argument/premise
//! product, including unused premises. Packed/long-Not/wider/other routes keep
//! their legacy payload walks.

use super::*;

fn equality(terms: &TermStore, term: TermId) -> Option<[TermId; 2]> {
    terms.entry_stamp(term)?;
    let TermData::App(Symbol::Named(op), args) = terms.get(term) else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    (op == "=").then_some([*left, *right])
}

fn negative_equality(terms: &TermStore, term: TermId) -> Option<TermId> {
    terms.entry_stamp(term)?;
    let TermData::Not(eq) = terms.get(term) else {
        return None;
    };
    let _ = equality(terms, *eq)?;
    Some(*eq)
}

fn heads(
    step: &ProofStep,
    terms: &TermStore,
    clauses: &[Option<Vec<TermId>>],
) -> Option<(Vec<TermId>, usize)> {
    match step {
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::EufTransitive,
            clause,
            ..
        } if clause.len() == 4 => {
            let mut heads = Vec::with_capacity(7);
            for &literal in &clause[..3] {
                heads.push(literal);
                heads.push(negative_equality(terms, literal)?);
            }
            let _ = equality(terms, clause[3])?;
            heads.push(clause[3]);
            Some((heads, 0))
        }
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::EufCongruent,
            clause,
            ..
        } if clause.len() == 2 => {
            let premise = negative_equality(terms, clause[0])?;
            let [left, right] = equality(terms, clause[1])?;
            for term in [left, right] {
                terms.entry_stamp(term)?;
                let TermData::App(_, args) = terms.get(term) else {
                    return None;
                };
                if args.len() > 4 {
                    return None;
                }
            }
            Some((vec![clause[0], premise, clause[1], left, right], 0))
        }
        ProofStep::Step {
            rule: AletheRule::Trans,
            clause,
            premises,
            args,
        } if clause.len() == 1 && premises.len() == 2 && args.is_empty() => {
            let _ = equality(terms, clause[0])?;
            let mut heads = vec![clause[0]];
            for &id in premises {
                let [literal] = clauses.get(id.0 as usize)?.as_ref()?.as_slice() else {
                    return None;
                };
                let _ = equality(terms, *literal)?;
                heads.push(*literal);
            }
            Some((heads, 0))
        }
        ProofStep::Step {
            rule: AletheRule::Cong,
            clause,
            premises,
            args,
        } if clause.len() == 1 && premises.len() <= 4 && args.is_empty() => {
            let [left, right] = equality(terms, clause[0])?;
            let mut arity = 0usize;
            for term in [left, right] {
                terms.entry_stamp(term)?;
                let TermData::App(_, args) = terms.get(term) else {
                    return None;
                };
                if args.len() > 4 {
                    return None;
                }
                arity = arity.max(args.len());
            }
            let mut heads = vec![clause[0], left, right];
            for &id in premises {
                let [literal] = clauses.get(id.0 as usize)?.as_ref()?.as_slice() else {
                    return None;
                };
                let _ = equality(terms, *literal)?;
                heads.push(*literal);
            }
            // validate_cong searches the complete premise vector at each
            // changed argument. Pay this worst case, even for unused extras.
            Some((heads, arity.checked_mul(premises.len())?))
        }
        _ => None,
    }
}

pub(super) fn meter(
    step: &ProofStep,
    terms: &TermStore,
    clauses: &[Option<Vec<TermId>>],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Option<PayloadStats>, ProofCheckError> {
    if !matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::EufTransitive | TheoryLemmaKind::EufCongruent,
            ..
        } | ProofStep::Step {
            rule: AletheRule::Trans | AletheRule::Cong,
            ..
        }
    ) {
        return Ok(None);
    }
    // No arena reads or small temporary vector allocation precede admission.
    charge_progress(progress, 0, 0)?;
    // At most seven TermIds, with fixed branch/shape checks. Pay their bound
    // even on a shape refusal before returning to the unchanged legacy walk.
    charge_progress(progress, 128, 7 * size_of::<TermId>())?;
    let Some((heads, comparison_work)) = heads(step, terms, clauses) else {
        return Ok(None);
    };
    charge_progress(progress, comparison_work, 0)?;
    let mut payload = PayloadStats {
        work: 128 + comparison_work,
        bytes: 7 * size_of::<TermId>(),
        fp_assignments: 1,
        ..PayloadStats::default()
    };
    let mut refused = false;
    let mut counting = |work: usize, bytes: usize| {
        if refused {
            return false;
        }
        let Some(w) = payload.work.checked_add(work) else {
            refused = true;
            return false;
        };
        let Some(b) = payload.bytes.checked_add(bytes) else {
            refused = true;
            return false;
        };
        payload.work = w;
        payload.bytes = b;
        if !progress(work, bytes) {
            refused = true;
            return false;
        }
        true
    };
    // Each listed head is charged independently, including repeated heads
    // that the validator might clone twice. Children are copied as TermIds,
    // never recursively visited; exactly the opaque-operand boundary above.
    let mut children = Vec::new();
    for term in heads {
        children.clear();
        charge_progress(&mut counting, 1, size_of::<TermId>())?;
        meter_reachable_node(terms, term, &mut children, &mut counting)?;
    }
    payload.unfolded_work = payload.work;
    Ok(Some(payload))
}

#[cfg(test)]
mod tests;
