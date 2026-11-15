// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The closing step of a closed collapsing fold, chosen by the checker.
//!
//! `plan_collapsing_fold` bridges `(= rebuilt folded)`, where every argument
//! of `rebuilt` is a literal constant, with one evaluation step. The planner
//! carries no authority, so that step must be one the UNTOUCHED strict checker
//! re-derives. The route is decided by the checker's own routines before
//! anything is emitted:
//!
//! 1. a Bool/Int/Real fold keeps its ground `evaluate`;
//! 2. the #ppp-c7 lane keeps its closed `BvBitBlast` bridge;
//! 3. otherwise the `BvLiaTautology` + `BoolTautology` pair, when
//!    `authenticate_bv_lia_unsat_query` proves the root that the strict
//!    validator recovers from that lemma, `(not (= rebuilt folded))`, UNSAT.
//!    The strict validator makes the same call on the same root;
//! 4. otherwise a directional `evaluate`, when the strict ground evaluator
//!    re-derives it, pinned Carcara parses and computes its head correctly,
//!    and the fold does not conclude the plan's own literal-constant target
//!    (#4751: that refutation stays with the original-assertion rebuild, as
//!    for every other constant-fold bridge);
//! 5. otherwise the fold declines, and the later fold bridges get their turn.
//!
//! Route 3 used to be unconditional. The bounded BV/LIA interpreter models
//! bit-vectors only up to 64 bits wide. A closed fold over a wider constant
//! produced a lemma the strict checker refuses ("query is outside the checked
//! BV/LIA fragment: an ill-sorted or unsupported term occurs in the source
//! query"). The case is a 128-bit `w` whose pinned definition `(= w c)` is
//! substituted into itself and folds to `true`. model-checker-consumer's realloc validation
//! queries hit it when an unrelated array conjunct routed them through the
//! `PropagateValues` replay. One refused step rejects the whole certificate,
//! so the default posture withdrew a correct `unsat` as `unknown (incomplete
//! self-check-rejected)`. Such a fold now closes with the exact wide
//! evaluator behind `evaluate`, which pinned Carcara checks `valid`, when it
//! sits inside a larger rewritten term. In the realloc reproducers it concludes
//! the rewritten assertion itself, the plan's literal target `true`, so it
//! declines and that candidate stays with the original-assertion rebuild.

use super::*;

#[cfg(test)]
mod tests;

/// The heads a closed fold may close with `evaluate`. The strict ground
/// evaluator admits more Bool/Int-valued heads over bit-vector literals, but
/// pinned Carcara must also parse the printed step and compute it correctly.
/// `bv2nat`, the internal spelling of `ubv_to_int` and `bv2int`
/// (`TermStore::mk_bv2nat`), is left out on purpose: pinned Carcara rejects
/// the identifier at parse time ("identifier 'bv2nat' is not defined"), so a
/// document carrying it is invalid however the step is judged internally.
const CARCARA_EVALUATED_CLOSED_FOLD_HEADS: &[&str] =
    &["=", "distinct", "bvult", "bvule", "bvugt", "bvuge"];

/// The single step that closes `(cl (= rebuilt folded))`.
pub(super) enum ClosedFoldEvaluation {
    /// Ground `evaluate` of the equality.
    Evaluate,
    /// One closed `BvBitBlast` lemma (#ppp-c7 metering).
    BitBlastBridge,
    /// `BvLiaTautology` over the authenticated root `negated`, then the
    /// propositional double-negation strip.
    BvLiaTautology { negated: TermId },
}

impl PropagationChainPlanner<'_> {
    /// The strictly admissible closing step for `equality`, which is
    /// `(= rebuilt folded)`, or `None` when the checker accepts no route.
    pub(super) fn closed_fold_evaluation_route(
        &mut self,
        cx: &PlanCx<'_>,
        rebuilt: TermId,
        new_args: &[TermId],
        equality: TermId,
    ) -> Option<ClosedFoldEvaluation> {
        let arithmetic_only = matches!(
            self.terms.sort(rebuilt),
            Sort::Bool | Sort::Int | Sort::Real
        ) && new_args
            .iter()
            .all(|&arg| matches!(self.terms.sort(arg), Sort::Bool | Sort::Int | Sort::Real));
        if arithmetic_only {
            return Some(ClosedFoldEvaluation::Evaluate);
        }
        if cx.closed_bv_bitblast_bridge {
            return Some(ClosedFoldEvaluation::BitBlastBridge);
        }
        let negated = self.terms.mk_not_raw(equality);
        if ay_proof::authenticate_bv_lia_unsat_query(self.terms, &[negated], None).is_ok() {
            return Some(ClosedFoldEvaluation::BvLiaTautology { negated });
        }
        self.closed_fold_evaluate_admissible(cx, rebuilt, equality)
            .then_some(ClosedFoldEvaluation::Evaluate)
    }

    /// Whether `(= rebuilt folded)` is an `evaluate` conclusion that both the
    /// strict validator and pinned Carcara judge correctly.
    ///
    /// The strict validator is directional: it evaluates the left-hand side
    /// only, and the right-hand side must already be a Bool, Int or Real
    /// literal. `rebuilt` applies one operator to literal constants, so that
    /// operator is the only one Carcara computes. It must be one pinned
    /// Carcara both parses and computes correctly
    /// ([`CARCARA_EVALUATED_CLOSED_FOLD_HEADS`]), and never one it computes
    /// wrongly
    /// (`ay_core::pinned_carcara::EVALUATE_OPERATORS_PINNED_CARCARA_MISJUDGES`).
    ///
    /// A fold to the plan's own literal-constant target is refused, as
    /// `plan_eq_refl_fold` and the other constant-fold bridges refuse it
    /// (#4751): that target is a preprocessing-time refutation, and the
    /// original-assertion rebuild keeps it with its theory certificates.
    fn closed_fold_evaluate_admissible(
        &self,
        cx: &PlanCx<'_>,
        rebuilt: TermId,
        equality: TermId,
    ) -> bool {
        let TermData::App(head, _) = self.terms.get(rebuilt) else {
            return false;
        };
        if !CARCARA_EVALUATED_CLOSED_FOLD_HEADS.contains(&head.name())
            || ay_core::pinned_carcara::EVALUATE_OPERATORS_PINNED_CARCARA_MISJUDGES
                .contains(&head.name())
        {
            return false;
        }
        let TermData::App(Symbol::Named(name), sides) = self.terms.get(equality) else {
            return false;
        };
        let [left, right] = sides.as_slice() else {
            return false;
        };
        let literal_right = matches!(
            self.terms.get(*right),
            TermData::Const(Constant::Bool(_) | Constant::Int(_) | Constant::Rational(_))
        );
        name == "="
            && *left == rebuilt
            && literal_right
            && !cx.refuses_constant_conclusion(*right)
            && ay_proof::recognize_ground_evaluate(self.terms, equality)
    }

    /// Emit the step `route` names for `equality`.
    pub(super) fn emit_closed_fold_evaluation(
        &mut self,
        cx: &mut PlanCx<'_>,
        route: ClosedFoldEvaluation,
        equality: TermId,
    ) -> ProofId {
        match route {
            ClosedFoldEvaluation::Evaluate => {
                cx.chain
                    .add_rule_step(AletheRule::Evaluate, vec![equality], Vec::new(), Vec::new())
            }
            ClosedFoldEvaluation::BitBlastBridge => cx.chain.add_step(ProofStep::TheoryLemma {
                theory: "theory".to_owned(),
                clause: vec![equality],
                farkas: None,
                kind: TheoryLemmaKind::BvBitBlast,
                lia: None,
            }),
            // The double-negation strip is the one `emit_forall_inst_unit_chain`
            // uses; both lemmas are re-proved by the untouched checker.
            ClosedFoldEvaluation::BvLiaTautology { negated } => {
                let double_negated = self.terms.mk_not_raw(negated);
                let lemma = cx.chain.add_step(ProofStep::TheoryLemma {
                    theory: "theory".to_owned(),
                    clause: vec![double_negated],
                    farkas: None,
                    kind: TheoryLemmaKind::BvLiaTautology,
                    lia: None,
                });
                let triple_negated = self.terms.mk_not_raw(double_negated);
                let strip = cx.chain.add_step(ProofStep::TheoryLemma {
                    theory: "theory".to_owned(),
                    clause: vec![triple_negated, equality],
                    farkas: None,
                    kind: TheoryLemmaKind::BoolTautology,
                    lia: None,
                });
                cx.chain
                    .add_resolution(vec![equality], double_negated, lemma, strip)
            }
        }
    }
}
