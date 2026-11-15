// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Argument equalities retain their provenance, never just a derived unit.
//! No arithmetic, fp.eq substitution, or transitive NaN/equality closure.

use super::*;
use ay_core::FpOp;

#[derive(Clone, Copy)]
pub(super) struct NanPremise {
    root: TermId,
    subject: TermId,
}

#[derive(Clone, Copy)]
pub(super) enum EqualityEvidence {
    Authored(TermId),
    NaN {
        left: TermId,
        right: TermId,
        left_nan: TermId,
        right_nan: TermId,
    },
}

pub(super) fn collect(
    executor: &mut Executor,
    authored: &[TermId],
    attempt: &mut Attempt,
) -> Option<Vec<NanPremise>> {
    if authored.len() > MAX_ROOTS {
        return None;
    }
    let mut result = Vec::new();
    for &root in authored {
        attempt.tick(executor)?;
        charge(&mut attempt.work, 2)?;
        let TermData::App(Symbol::Named(name), args) = executor.ctx.terms.get(root) else {
            continue;
        };
        // Length/arity before a bounded exact identity comparison. Unrelated
        // g(x_i) units do not trigger a subtree walk or an FP-pair enumeration.
        if name.len() != "fp.isNaN".len() || args.len() != 1 {
            continue;
        }
        charge(&mut attempt.work, "fp.isNaN".len() + 3)?;
        if name.as_str() != "fp.isNaN" || executor.ctx.terms.sort(root) != &Sort::Bool {
            continue;
        }
        let subject = args[0];
        if !matches!(executor.ctx.terms.sort(subject),
            Sort::FloatingPoint(eb, sb) if *eb >= 2 && *sb >= 2)
        {
            continue;
        }
        charge(&mut attempt.work, 2)?;
        result.push(NanPremise { root, subject });
    }
    attempt.tick(executor)?;
    Some(result)
}

pub(super) fn find_nan(
    nans: &[NanPremise],
    left: TermId,
    right: TermId,
    work: &mut usize,
) -> Option<EqualityEvidence> {
    let mut left_nan = None;
    let mut right_nan = None;
    for premise in nans {
        charge(work, 3)?;
        if left_nan.is_none() && premise.subject == left {
            left_nan = Some(premise.root);
        }
        if right_nan.is_none() && premise.subject == right {
            right_nan = Some(premise.root);
        }
        if let (Some(left_nan), Some(right_nan)) = (left_nan, right_nan) {
            return Some(EqualityEvidence::NaN {
                left,
                right,
                left_nan,
                right_nan,
            });
        }
    }
    None
}

impl EqualityEvidence {
    pub(super) fn literal(self, executor: &mut Executor, work: &mut usize) -> Option<TermId> {
        if !open(executor) {
            return None;
        }
        match self {
            Self::Authored(root) => Some(root),
            Self::NaN { left, right, .. } => {
                charge(work, 4)?;
                Some(
                    executor
                        .ctx
                        .terms
                        .mk_app(Symbol::named("="), [left, right], Sort::Bool),
                )
            }
        }
    }

    pub(super) fn emit(
        self,
        executor: &mut Executor,
        equality: TermId,
        proof: &mut Proof,
        work: &mut usize,
    ) -> Option<ProofId> {
        if !open(executor) {
            return None;
        }
        let id = match self {
            Self::Authored(root) => {
                spend(work)?;
                proof.add_assume(root, None)
            }
            Self::NaN {
                left_nan,
                right_nan,
                ..
            } => {
                // Fixed-size two assumptions, one three-literal theorem and
                // two resolutions; pay before any terms/steps/clones are made.
                charge(work, 32)?;
                let not_left = executor.ctx.terms.mk_not_raw(left_nan);
                let not_right = executor.ctx.terms.mk_not_raw(right_nan);
                let left = proof.add_assume(left_nan, None);
                let right = proof.add_assume(right_nan, None);
                let theorem = proof.add_theory_lemma_with_kind(
                    "fp",
                    vec![not_left, not_right, equality],
                    TheoryLemmaKind::FpClassification {
                        operation: FpOp::IsNaN,
                    },
                );
                let one = proof.add_resolution(vec![not_right, equality], left_nan, theorem, left);
                proof.add_resolution(vec![equality], right_nan, one, right)
            }
        };
        if !open(executor) {
            return None;
        }
        Some(id)
    }
}

#[cfg(test)]
#[path = "equality_evidence/tests.rs"]
mod tests;
