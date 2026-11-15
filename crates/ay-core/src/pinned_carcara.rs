// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pinned Carcara verdicts that are not evidence.
//!
//! Every gate that runs pinned carcara 1.1.0 (git 9a352ee) counts only its
//! literal `valid` as external verification. Three defects of that checker
//! make even a literal `valid` worthless on some documents:
//!
//! * [`evaluate`]: inside an `evaluate` step it computes some operators
//!   wrongly (a negative signed bit-vector operand, `bvsub`, `extract`,
//!   `rotate_left`, integer `div`/`mod`), so it accepts false evaluations;
//! * [`binder_capture`]: it expands `:named` labels and `define-fun`s at parse
//!   time, before any scope lookup, so it reads a binder that rebinds or
//!   captures a definition's name as a different formula;
//! * [`aci_simp`]: its `aci_simp` drops repeated arguments of `+`, `*`,
//!   `bvadd`, `bvmul`, `bvxor` and `concat` as if they were idempotent, so it
//!   accepts false equalities such as `(= (bvmul a a) a)`.
//!
//! [`pinned_carcara_misjudgments`] runs the three scans over a (problem,
//! proof) pair, each reading every token where pinned Carcara's own lexer ends
//! it, so a non-ASCII space or a literal glued to its operator hides nothing
//! from them. When the result is not empty the checker's verdict says nothing
//! in either direction, and a gate that acts on it must refuse it: a `valid`
//! is never counted as verified, and no test may pass on it. This is the one
//! implementation: every in-tree Carcara runner that acts on a verdict calls
//! it (the ay-dpll and ay-proof test runners, `ay z3-audit`, the z3-parity
//! UNSAT proof gate), and the scripts reach it through `ay check
//! carcara-guard`. Only the controls that pin these defects against the real
//! checker read its raw verdict, on purpose.

pub mod aci_simp;
pub mod binder_capture;
pub mod evaluate;
mod lexer;

pub use aci_simp::{
    aci_simp_steps_pinned_carcara_misjudges, ACI_SIMP_OPERATORS_PINNED_CARCARA_DEDUPLICATES,
};
pub use binder_capture::binders_pinned_carcara_misreads;
pub use evaluate::{
    evaluate_steps_pinned_carcara_misjudges, EVALUATE_OPERATORS_PINNED_CARCARA_MISJUDGES,
};

/// Why pinned Carcara's verdict on one (problem, proof) pair is not evidence.
/// Empty means no scan flags anything.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PinnedCarcaraMisjudgments {
    /// The `evaluate` steps (whole commands) applying an operator pinned
    /// Carcara computes wrongly, directly or through a name it expands.
    pub evaluate_steps: Vec<String>,
    /// `(bound name, definition)` for each binder pinned Carcara reads as
    /// rebinding or capturing a definition.
    pub binders: Vec<(String, String)>,
    /// The `aci_simp` steps (whole commands) over an operator pinned Carcara
    /// deduplicates wrongly whose conclusion is not an AC identity.
    pub aci_simp_steps: Vec<String>,
}

impl PinnedCarcaraMisjudgments {
    /// No scan flags anything: the checker's verdict can be read.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.evaluate_steps.is_empty() && self.binders.is_empty() && self.aci_simp_steps.is_empty()
    }
}

impl std::fmt::Display for PinnedCarcaraMisjudgments {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "pinned Carcara's verdict is not evidence: misjudged evaluate steps={:?}; \
             misread binders={:?}; misjudged aci_simp steps={:?}",
            self.evaluate_steps, self.binders, self.aci_simp_steps
        )
    }
}

/// Every scan over `problem` (the exact bytes handed to the checker) and
/// `proof`.
#[must_use]
pub fn pinned_carcara_misjudgments(problem: &str, proof: &str) -> PinnedCarcaraMisjudgments {
    PinnedCarcaraMisjudgments {
        evaluate_steps: evaluate_steps_pinned_carcara_misjudges(problem, proof)
            .into_iter()
            .map(str::to_string)
            .collect(),
        binders: binders_pinned_carcara_misreads(problem, proof),
        aci_simp_steps: aci_simp_steps_pinned_carcara_misjudges(problem, proof)
            .into_iter()
            .map(str::to_string)
            .collect(),
    }
}

/// `Ok` when pinned Carcara's verdict on this pair can be read at all, and
/// the reasons it cannot otherwise. A runner calls this BEFORE it acts on the
/// checker (it needs no checker), so its refusal is the same whether or not
/// the checker is installed, and a refused pair can never pass a test.
///
/// # Errors
///
/// The non-empty [`PinnedCarcaraMisjudgments`] of the pair.
pub fn pinned_carcara_can_judge(
    problem: &str,
    proof: &str,
) -> Result<(), PinnedCarcaraMisjudgments> {
    let misjudgments = pinned_carcara_misjudgments(problem, proof);
    if misjudgments.is_empty() {
        Ok(())
    } else {
        Err(misjudgments)
    }
}

/// The problem of the false-`valid` control: SATISFIABLE, because `(bvsge
/// #xf #xe)` is -1 >= -2 (z3 answers `sat`).
pub const FALSE_VALID_CONTROL_PROBLEM: &str =
    "(set-logic QF_BV)\n(assert (bvsge #xf #xe))\n(check-sat)\n";

/// A refutation of [`FALSE_VALID_CONTROL_PROBLEM`] resting on one false
/// `evaluate` step, for which pinned Carcara nonetheless prints `valid`
/// (pinned against the real checker by the ay-dpll test
/// `a_valid_verdict_resting_on_a_misjudged_evaluate_is_not_evidence`). Every
/// gate's negative control feeds this pair and must refuse it.
pub const FALSE_VALID_CONTROL_PROOF: &str = "(assume t0 (bvsge #xf #xe))\n\
     (step t1 (cl (= (bvsge #xf #xe) false)) :rule evaluate)\n\
     (step t2 (cl (not (= (bvsge #xf #xe) false)) (not (bvsge #xf #xe)) false) \
     :rule equiv_pos2)\n\
     (step t3 (cl (not false)) :rule false)\n\
     (step t4 (cl) :rule resolution :premises (t2 t1 t0 t3))\n";

/// The false step of [`FALSE_VALID_CONTROL_PROOF`] alone, under a step id no
/// emitter uses. Pinned Carcara checks every step, yet accepts this one, so a
/// real refutation with this step appended is still `valid` to it although
/// the document now asserts `(bvsge #xf #xe)` is false. A runner whose problem
/// is fixed builds its negative control that way: its own valid document plus
/// this step, which it must refuse.
pub const FALSE_VALID_CONTROL_STEP: &str =
    "(step t_false_valid_control (cl (= (bvsge #xf #xe) false)) :rule evaluate)\n";

/// The problem of the false-`valid` `aci_simp` control: SATISFIABLE, because
/// `a = #x02` makes `(bvmul a a)` `#x04` (z3 answers `sat`).
pub const FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM: &str = "(set-logic QF_BV)\n\
     (declare-const a (_ BitVec 8))\n(assert (not (= (bvmul a a) a)))\n(check-sat)\n";

/// A refutation of [`FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM`] resting on one
/// false `aci_simp` step, for which pinned Carcara nonetheless prints `valid`
/// (pinned against the real checker by the ay-dpll test
/// `a_valid_verdict_resting_on_a_misjudged_aci_simp_is_not_evidence`).
pub const FALSE_VALID_ACI_SIMP_CONTROL_PROOF: &str = "(assume h1 (not (= (bvmul a a) a)))\n\
     (step t1 (cl (= (bvmul a a) a)) :rule aci_simp)\n\
     (step t2 (cl) :rule resolution :premises (h1 t1))\n";

#[cfg(test)]
mod aci_simp_tests;
#[cfg(test)]
mod binder_capture_tests;
#[cfg(test)]
mod evaluate_tests;
#[cfg(test)]
mod lexer_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_false_valid_control_is_flagged_and_a_clean_pair_is_not() {
        let flagged =
            pinned_carcara_misjudgments(FALSE_VALID_CONTROL_PROBLEM, FALSE_VALID_CONTROL_PROOF);
        assert_eq!(
            flagged.evaluate_steps,
            vec!["(step t1 (cl (= (bvsge #xf #xe) false)) :rule evaluate)".to_string()]
        );
        assert!(
            flagged.binders.is_empty() && !flagged.is_empty(),
            "{flagged}"
        );
        let refused =
            pinned_carcara_can_judge(FALSE_VALID_CONTROL_PROBLEM, FALSE_VALID_CONTROL_PROOF);
        assert_eq!(refused, Err(flagged.clone()));
        assert!(flagged.to_string().contains("is not evidence"), "{flagged}");
        let clean = pinned_carcara_misjudgments(
            "(set-logic QF_BV)\n(assert (bvult #x1 #x0))\n(check-sat)\n",
            "(assume t0 (bvult #x1 #x0))\n\
             (step t1 (cl (= (bvult #x1 #x0) false)) :rule evaluate)\n",
        );
        assert!(clean.is_empty(), "{clean}");
        assert_eq!(
            pinned_carcara_can_judge(
                "(set-logic QF_BV)\n(assert (bvult #x1 #x0))\n(check-sat)\n",
                "(assume t0 (bvult #x1 #x0))\n",
            ),
            Ok(())
        );
        let captured = pinned_carcara_misjudgments(
            "(declare-const y Int)\n(assert (! (= y 0) :named n))\n\
             (assert (forall ((y Int)) n))\n",
            "",
        );
        assert_eq!(
            captured.binders,
            vec![("y".to_string(), "n".to_string())],
            "{captured}"
        );
        assert!(captured.evaluate_steps.is_empty());
        // The binder route refuses through the same entry point every runner
        // calls, not only through the scan.
        assert_eq!(
            pinned_carcara_can_judge(
                "(declare-const y Int)\n(assert (! (= y 0) :named n))\n\
                 (assert (forall ((y Int)) n))\n",
                "",
            ),
            Err(captured)
        );
    }

    /// A clean refutation with [`FALSE_VALID_CONTROL_STEP`] appended is
    /// refused, naming exactly that step.
    #[test]
    fn a_clean_refutation_carrying_the_false_step_is_refused() {
        let problem = "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n";
        let proof =
            "(assume h1 p)\n(assume h2 (not p))\n(step t3 (cl) :rule resolution :premises (h1 h2))\n";
        assert_eq!(pinned_carcara_can_judge(problem, proof), Ok(()));
        let twin = format!("{proof}{FALSE_VALID_CONTROL_STEP}");
        let refused = pinned_carcara_can_judge(problem, &twin).expect_err("the false step");
        assert_eq!(
            refused.evaluate_steps,
            vec![FALSE_VALID_CONTROL_STEP.trim_end().to_string()]
        );
    }
}
