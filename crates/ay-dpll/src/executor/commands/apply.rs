// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `(apply <tactic>)` — run a Z3-style goal-to-goal tactic over the current
//! goal and print the resulting goal(s).
//!
//! # Soundness
//!
//! `(apply)` is a **read-only** query over the goal: it prints a transformed
//! goal but MUST NOT mutate the executor's real assertion stack — a subsequent
//! `(check-sat)` has to solve the *original* problem. This is enforced here by
//! transforming a *clone* of `self.ctx.assertions`; the tactic may intern new
//! terms into the shared store, but the assertion stack itself is never touched.
//!
//! Every tactic exposed on the `apply` surface is **verdict-preserving** (see
//! [`crate::api::Tactic`]): the printed subgoals are equisatisfiable to the
//! input assertions. Most are additionally *equivalence-preserving* (the printed
//! goals have exactly the same models); the exception is `tseitin-cnf`, which
//! introduces fresh existential aux variables, so the CNF's models differ from
//! the input's on those new variables while `check-sat` is preserved. The
//! previous behavior — a constant *empty* goal echoed for every tactic — was
//! unsound: an empty goal is semantically `true` (trivially SAT), so a
//! downstream tool solving the apply output would report SAT for an UNSAT
//! problem. This replaces that stub with a real transformation.

use ay_frontend::ApplyTactic;

use crate::api::{Goal, Tactic};
use crate::executor::Executor;

impl Executor {
    /// Apply a Z3-style tactic to the current goal and format the resulting
    /// goal(s) in Z3's `(goals (goal ...) ...)` shape.
    ///
    /// The real assertion stack is never mutated (see the module docs): the
    /// tactic runs over a clone of `self.ctx.assertions`. A case-splitting tactic
    /// (e.g. `split-clause`) yields SEVERAL `(goal ...)` blocks whose disjunction
    /// is equisatisfiable to the input; a failing tactic (e.g. `fail`) prints an
    /// honest `(error "tactic failed: ...")`, exactly like Z3.
    pub(crate) fn apply_tactic_goal(&mut self, tactic: &ApplyTactic) -> String {
        // GOAL PRESERVATION IS A SOUNDNESS PROPERTY: transform a clone so a
        // following (check-sat) still solves the ORIGINAL assertions.
        //
        // Build the goal the way Z3 does: recursively split top-level `and` into
        // separate formulas, drop `true` conjuncts, and collapse to `{false}` on
        // any `false` conjunct. This decomposition is visible for EVERY tactic —
        // `skip` on `(and a b c)` prints the three formulas `a b c` at depth 0,
        // and `split-clause` can split a clause that was buried under a top-level
        // `and`. The transform is equivalence-preserving, so a following
        // (check-sat) is unaffected.
        let root = Goal::root_flattened(&self.ctx.terms, &self.ctx.assertions);
        // Resolve through the SHARED name→transform registry so the SMT-LIB
        // `(apply ...)` surface and the C-API `Z3_mk_tactic` surface always
        // agree (see [`Tactic::from_apply`]).
        let native = Tactic::from_apply(tactic);
        // `apply_goals` reads `self.ctx.assertions` via the clone above and may
        // intern new terms in the store; `self.ctx.assertions` is left untouched.
        match native.apply_goals(&mut self.ctx.terms, root) {
            Ok(goals) => self.format_goals(&goals),
            Err(failure) => format!("(error \"tactic failed: {}\")", failure.message),
        }
    }

    /// Format one or more goals in Z3's exact `(goals (goal ...) ...)` shape,
    /// each block carrying its own `:precision precise :depth <n>` line.
    ///
    /// With a single empty goal this prints the canonical empty goal
    /// `(goals\n(goal\n  :precision precise :depth <n>)\n)` — correct only because
    /// there genuinely are no assertions (an empty conjunction is `true`).
    fn format_goals(&self, goals: &[Goal]) -> String {
        let mut out = String::from("(goals\n");
        for goal in goals {
            out.push_str("(goal\n");
            for &id in &goal.formulas {
                out.push_str("  ");
                out.push_str(&self.format_term(id));
                out.push('\n');
            }
            out.push_str(&format!("  :precision precise :depth {})\n", goal.depth));
        }
        out.push(')');
        out
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests {
    use crate::executor::Executor;
    use ay_frontend::parse;

    /// Run a full SMT-LIB script, returning the ordered non-empty command outputs.
    fn outputs(script: &str) -> Vec<String> {
        let mut exec = Executor::new();
        let cmds = parse(script).expect("script must parse");
        cmds.iter()
            .filter_map(|cmd| exec.execute(cmd).expect("command must execute"))
            .collect()
    }

    /// The unsound constant goal the old stub echoed for *every* `(apply <t>)`.
    /// An empty goal is semantically `true` (trivially SAT).
    const OLD_UNSOUND_EMPTY_STUB: &str = "(goals\n(goal\n  :precision precise :depth 1)\n)";

    #[test]
    fn apply_simplify_on_unsat_conjunction_is_not_the_old_unsound_empty_stub() {
        // Regression for the soundness hole: the old stub echoed a constant EMPTY
        // goal for every apply. An empty goal is `true` (trivially SAT), so a tool
        // solving the apply output would report SAT for this UNSAT problem. The
        // real tactic must print the residual goal, which mentions `x`.
        let out = outputs(
            "(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n(apply simplify)\n",
        );
        let goal = out.last().expect("apply produces a goal");
        assert_ne!(
            goal.as_str(),
            OLD_UNSOUND_EMPTY_STUB,
            "apply must emit the real residual goal, not the unsound empty stub"
        );
        assert!(
            goal.contains('x'),
            "the residual goal must mention the constrained variable x: {goal}"
        );
    }

    #[test]
    fn apply_skip_is_the_identity_goal_at_depth_zero() {
        // skip is the identity: the single original assertion survives (in AY's
        // normal form) and the goal depth is 0.
        let out = outputs("(declare-const x Int)\n(assert (> x 0))\n(apply skip)\n");
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (< 0 x)\n  :precision precise :depth 0)\n)"),
            "skip must echo the original assertion unchanged at depth 0; got {out:?}"
        );
    }

    #[test]
    fn apply_skip_flattens_a_nested_top_level_and_at_depth_zero() {
        // Z3-PARITY REGRESSION: Z3's goal decomposes a top-level `and` into
        // separate formulas as it is asserted, so this is visible even for the
        // identity `skip`. z3 4.x byte-verified on
        //   (assert (and (and a b) c))(apply skip)
        // prints the three formulas a, b, c at depth 0 (fully recursive). AY must
        // match — it previously kept the single `(and a b c)` formula.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(declare-const c Bool)\n(assert (and (and a b) c))\n(apply skip)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  a\n  b\n  c\n  :precision precise :depth 0)\n)"),
            "skip must recursively flatten the nested top-level `and` at depth 0; got {out:?}"
        );
    }

    #[test]
    fn apply_split_clause_splits_a_clause_buried_under_a_top_level_and() {
        // Z3-PARITY REGRESSION: because the goal flattens its top-level `and`, a
        // clause hidden under it becomes a first-class goal formula that
        // split-clause can split. z3 4.x byte-verified on
        //   (assert (and c (or a b)))(apply split-clause)
        // flattens to {c, (or a b)} and splits into two goals {c, a} and {c, b}
        // at depth 1. AY previously reported "goal does not contain any clause".
        // (NB: `(and a (or a b))` is NOT used here — AY's eager `mk_and`
        // absorption soundly reduces `a ∧ (a ∨ b)` to just `a`, so there is no
        // clause left; `c` avoids that absorption while still exercising the
        // flatten-then-split path z3 takes.)
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(declare-const c Bool)\n(assert (and c (or a b)))\n(apply split-clause)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some(
                "(goals\n(goal\n  c\n  a\n  :precision precise :depth 1)\n(goal\n  c\n  b\n  :precision precise :depth 1)\n)"
            ),
            "split-clause must flatten the top-level `and` and split the buried clause; got {out:?}"
        );
    }

    #[test]
    fn apply_does_not_mutate_the_real_assertion_stack() {
        // GOAL PRESERVATION is a soundness property: apply is a read-only query;
        // the real assertion stack must be untouched so a following check-sat
        // still solves the ORIGINAL problem.
        let mut exec = Executor::new();
        for cmd in &parse("(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n")
            .expect("setup parses")
        {
            exec.execute(cmd).expect("setup executes");
        }
        let before = exec.ctx.assertions.clone();
        for cmd in &parse("(apply simplify)").expect("apply parses") {
            exec.execute(cmd).expect("apply executes");
        }
        assert_eq!(
            exec.ctx.assertions, before,
            "(apply) must not mutate the real assertion stack"
        );
    }

    #[test]
    fn check_sat_after_apply_still_solves_the_original_unsat_problem() {
        // The old stub swallowed nothing (it was a pure echo), but the invariant
        // we lock in is that apply leaves the verdict of the ORIGINAL problem
        // intact: x>5 ∧ x<3 is UNSAT before and after the apply.
        let out = outputs(
            "(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n(apply simplify)\n(check-sat)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("unsat"),
            "check-sat after apply must still return the original verdict; got {out:?}"
        );
    }

    #[test]
    fn check_sat_after_apply_skip_preserves_a_sat_verdict() {
        let out = outputs("(declare-const x Int)\n(assert (> x 0))\n(apply skip)\n(check-sat)\n");
        assert_eq!(
            out.last().map(String::as_str),
            Some("sat"),
            "check-sat after apply skip must still return sat; got {out:?}"
        );
    }

    #[test]
    fn apply_elim_and_splits_top_level_conjunction() {
        // `elim-and` (Z3's and-elimination name) splits the top-level `and` into
        // separate goal formulas, just like Z3's goal model.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(declare-const c Bool)\n(assert (and (and a b) c))\n(apply elim-and)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  a\n  b\n  c\n  :precision precise :depth 1)\n)"),
            "elim-and must split the nested conjunction into a, b, c; got {out:?}"
        );
    }

    #[test]
    fn check_sat_after_apply_elim_and_preserves_the_verdict() {
        // GOAL PRESERVATION: elim-and is equivalence-preserving, so the ORIGINAL
        // verdict is untouched (UNSAT here: a ∧ ¬a).
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(assert (and (and a (not a)) b))\n(apply elim-and)\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
    }

    #[test]
    fn apply_propagate_values_propagates_a_literal_and_drops_the_folded_clause() {
        // z3 4.15.4 byte-verified: (assert p)(assert (or (not p) q)) under
        // propagate-values yields the goal (p q) — the clause folds to q under
        // p ↦ true. This is the transform the pass previously never made.
        let out = outputs(
            "(declare-const p Bool)\n(declare-const q Bool)\n(assert p)\n(assert (or (not p) q))\n(apply propagate-values)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  p\n  q\n  :precision precise :depth 1)\n)"),
            "propagate-values must fold the clause under the asserted literal; got {out:?}"
        );
    }

    #[test]
    fn apply_propagate_values_drops_an_atom_implied_by_a_variable_equality() {
        // z3 4.15.4 byte-verified: (= x 5) ∧ (> x 3) → goal ((= x 5)).
        let out = outputs(
            "(declare-const x Int)\n(assert (= x 5))\n(assert (> x 3))\n(apply propagate-values)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (= x 5)\n  :precision precise :depth 1)\n)"),
            "propagate-values must drop the implied inequality; got {out:?}"
        );
    }

    #[test]
    fn apply_propagate_values_collapses_a_conflict_to_false() {
        // z3 4.15.4 byte-verified: (= x 5) ∧ (= x 6) → goal (false).
        let out = outputs(
            "(declare-const x Int)\n(assert (= x 5))\n(assert (= x 6))\n(apply propagate-values)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  false\n  :precision precise :depth 1)\n)"),
            "conflicting values must collapse the printed goal to false; got {out:?}"
        );
    }

    #[test]
    fn apply_propagate_values_identity_keeps_the_goal_shape() {
        // NEGATIVE case, z3 4.15.4 byte-verified: nothing propagates, the goal
        // survives verbatim at depth 1 (a primitive still increments depth).
        let out = outputs("(declare-const x Int)\n(assert (<= x 5))\n(apply propagate-values)\n");
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (<= x 5)\n  :precision precise :depth 1)\n)"),
            "no-op propagate-values must keep the goal shape; got {out:?}"
        );
    }

    #[test]
    fn check_sat_after_apply_propagate_values_preserves_the_verdict() {
        // GOAL PRESERVATION: apply is read-only; the strengthened pass must not
        // leak into the real assertion stack (UNSAT stays UNSAT).
        let out = outputs(
            "(declare-const x Int)\n(assert (= x 5))\n(assert (= x 6))\n(apply propagate-values)\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
    }

    #[test]
    fn apply_propagate_ineqs_drops_the_subsumed_bound_and_is_not_skip() {
        // z3 4.15.4 byte-verified: (<= x 5) ∧ (<= x 10) → goal ((<= x 5)).
        // ALSO a lock against silent regression: `ApplyTactic` is
        // #[non_exhaustive] and `Tactic::from_apply` has a `_ => Skip`
        // catch-all, so a forgotten mapping arm would silently turn
        // propagate-ineqs into the identity — the output must differ from
        // (apply skip)'s.
        let script = "(declare-const x Int)\n(assert (<= x 5))\n(assert (<= x 10))\n";
        let ineqs = outputs(&format!("{script}(apply propagate-ineqs)\n"));
        let skip = outputs(&format!("{script}(apply skip)\n"));
        assert_eq!(
            ineqs.last().map(String::as_str),
            Some("(goals\n(goal\n  (<= x 5)\n  :precision precise :depth 1)\n)"),
            "propagate-ineqs must drop the weaker bound; got {ineqs:?}"
        );
        assert_ne!(
            ineqs.last(),
            skip.last(),
            "propagate-ineqs must not silently regress to skip"
        );
    }

    #[test]
    fn apply_propagate_ineqs_re_emits_value_equalities_at_the_end() {
        // z3 4.15.4 byte-verified: (= x 5) ∧ b → goal (b (= x 5)).
        let out = outputs(
            "(declare-const x Int)\n(declare-const b Bool)\n(assert (= x 5))\n(assert b)\n(apply propagate-ineqs)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  b\n  (= x 5)\n  :precision precise :depth 1)\n)"),
            "the value equality must move to the end of the goal; got {out:?}"
        );
    }

    #[test]
    fn apply_propagate_ineqs_does_no_value_propagation() {
        // z3 4.15.4 byte-verified: propagate-ineqs must NOT substitute x ↦ 5
        // into other formulas (that is propagate-values' job): the var–var
        // equality and the derived formula survive verbatim.
        let out = outputs(
            "(declare-const x Int)\n(declare-const y Int)\n(assert (= x y))\n(assert (<= x 10))\n(apply propagate-ineqs)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (= x y)\n  (<= x 10)\n  :precision precise :depth 1)\n)"),
            "var-var equalities and unrelated formulas pass through in place; got {out:?}"
        );
    }

    #[test]
    fn check_sat_after_apply_propagate_ineqs_preserves_the_verdict() {
        // GOAL PRESERVATION: contradictory bounds are kept (no false collapse)
        // and the real assertion stack is untouched — UNSAT stays UNSAT.
        let out = outputs(
            "(declare-const x Int)\n(assert (<= x 3))\n(assert (>= x 7))\n(apply propagate-ineqs)\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
    }

    #[test]
    fn apply_qe_light_eliminates_existential_to_a_closed_printable_goal() {
        // qe-light is a real z3 tactic, backed by AY's Cooper `QeLight` pass. It
        // replaces the in-fragment `(exists ((x Int)) (= (* 2 x) y))` with the
        // quantifier-free equivalent over its FREE variable `y` — the bound `x`
        // is genuinely eliminated (not stripped and freed), so the printed goal
        // is closed and faithfully equisatisfiable. z3's own `qe-light` leaves
        // the existential in place; AY's is more aggressive but equivalent over
        // `y` (both denote "y is even").
        let out = outputs(
            "(declare-const y Int)\n(assert (exists ((x Int)) (= (* 2 x) y)))\n(apply qe-light)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (= 0 (mod y 2))\n  :precision precise :depth 1)\n)"),
            "qe-light must eliminate the existential to the closed goal (= 0 (mod y 2)); got {out:?}"
        );
    }

    #[test]
    fn apply_qe_light_on_negated_existential_stays_sound_not_freed() {
        // SOUNDNESS REGRESSION. The earlier qe-light path re-interned the bound
        // variable via `mk_var(name)`, which (because the elaborator uses
        // `mk_fresh_var`, leaving the name unregistered) minted a phantom
        // variable and left the real bound variable dangling FREE. That flipped
        // this UNSAT assertion into a satisfiable printed goal `(x_0 <= 0) ∨ (x_0
        // >= 5)`. With the fix, `∃x. 0<x<5 ≡ true`, so `¬true ≡ false`: the
        // printed goal is `false` (UNSAT), matching the input verdict exactly.
        let out =
            outputs("(assert (not (exists ((x Int)) (and (< 0 x) (< x 5)))))\n(apply qe-light)\n");
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  false\n  :precision precise :depth 1)\n)"),
            "negated eliminable existential must print the closed goal `false`, never a \
             satisfiable freed-variable goal; got {out:?}"
        );
    }

    #[test]
    fn check_sat_after_apply_qe_light_preserves_the_negated_unsat_verdict() {
        // GOAL PRESERVATION: (apply) is read-only, so the following check-sat must
        // still return the ORIGINAL verdict (UNSAT here).
        let out = outputs(
            "(assert (not (exists ((x Int)) (and (< 0 x) (< x 5)))))\n(apply qe-light)\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
    }

    #[test]
    fn apply_qe_light_leaves_out_of_fragment_quantifier_intact() {
        // A two-variable existential is outside Cooper's single-variable fragment:
        // qe-light must keep the quantifier verbatim, never a partial/unsound
        // strip.
        let out = outputs("(assert (exists ((x Int) (y Int)) (< x y)))\n(apply qe-light)\n");
        let goal = out.last().expect("apply produces a goal");
        assert!(
            goal.contains("exists"),
            "out-of-fragment existential must be kept intact; got {goal}"
        );
    }

    // -----------------------------------------------------------------------
    // qe — z3's quantifier-elimination tactic, realized by the same Cooper pass
    // as qe-light. Fixture: the development design notes
    // S5_lia_qe_evenness.smt2 (Z3 4.16.0 oracle).
    // -----------------------------------------------------------------------

    #[test]
    fn apply_qe_eliminates_the_s5_evenness_existential_like_z3() {
        // SOUNDNESS REGRESSION S5. (exists x. 2x = a) ≡ "a is even". The old stub
        // printed an EMPTY goal (≡ true — WRONG, a=1 is a counterexample); z3
        // 4.16.0's (apply qe) prints (goal (= 0 (mod a 2)) ... :depth 1). AY must
        // match the oracle byte-for-byte on the S5 script.
        let out = outputs(
            "(set-logic LIA)\n(declare-const a Int)\n(assert (exists ((x Int)) (= (* 2 x) a)))\n(apply qe)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (= 0 (mod a 2))\n  :precision precise :depth 1)\n)"),
            "qe must eliminate the S5 existential to the evenness constraint; got {out:?}"
        );
    }

    #[test]
    fn check_sat_after_apply_qe_with_odd_witness_is_unsat() {
        // GOAL PRESERVATION + false-variant control: with (= a 1) added, the S5
        // formula is UNSAT (1 is odd). (apply qe) is read-only — a following
        // check-sat must still solve the ORIGINAL problem and return unsat,
        // proving apply neither dropped a constraint nor minted a verdict.
        let out = outputs(
            "(declare-const a Int)\n(assert (exists ((x Int)) (= (* 2 x) a)))\n(assert (= a 1))\n(apply qe)\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
    }

    #[test]
    fn apply_qe_keeps_out_of_fragment_quantifier_verbatim() {
        // A two-variable existential is outside Cooper's single-variable
        // fragment. AY's qe keeps the quantifier VERBATIM (the identity is
        // equivalence-preserving) — a documented sound divergence from z3's
        // LIA-complete qe; never a partial/unsound strip.
        let out = outputs("(assert (exists ((x Int) (y Int)) (< x y)))\n(apply qe)\n");
        let goal = out.last().expect("apply produces a goal");
        assert!(
            goal.contains("exists"),
            "out-of-fragment existential must be kept verbatim by qe; got {goal}"
        );
    }

    #[test]
    fn apply_qe_does_not_mutate_the_real_assertion_stack() {
        // GOAL PRESERVATION is a soundness property: (apply qe) is a read-only
        // query; the real assertion stack must be untouched so a following
        // check-sat solves the ORIGINAL problem.
        let mut exec = Executor::new();
        for cmd in &parse("(declare-const a Int)\n(assert (exists ((x Int)) (= (* 2 x) a)))\n")
            .expect("setup parses")
        {
            exec.execute(cmd).expect("setup executes");
        }
        let before = exec.ctx.assertions.clone();
        for cmd in &parse("(apply qe)").expect("apply parses") {
            exec.execute(cmd).expect("apply executes");
        }
        assert_eq!(
            exec.ctx.assertions, before,
            "(apply qe) must not mutate the real assertion stack"
        );
    }

    #[test]
    fn flatten_and_is_not_a_z3_tactic_and_is_rejected() {
        // Z3 has no `flatten-and` tactic; a Z3 replacement rejects it exactly as
        // Z3 does, rather than recognizing an AY-only alias.
        let err = parse("(apply flatten-and)")
            .expect_err("flatten-and must be a parse error")
            .to_string();
        assert!(
            err.contains("unknown tactic") && err.contains("flatten-and"),
            "expected an unknown-tactic error like z3, got: {err}"
        );
    }

    // -----------------------------------------------------------------------
    // nnf (negation normal form). Each expected output was cross-checked against
    // z3 4.15.4's `(apply nnf)` on the same script (see the per-test comment);
    // AY agrees up to its own atom/argument canonicalization and idempotent
    // dedup — the two goals are logically EQUIVALENT (verified by the following
    // check-sat tests and, in `preprocess::nnf`, an input-XOR-nnf property test).
    // -----------------------------------------------------------------------

    #[test]
    fn apply_nnf_pushes_negation_through_and_to_atom_literals() {
        // ¬(x>0 ∧ x<5) ≡ ¬(x>0) ∨ ¬(x<5). z3 4.15.4 prints
        //   (or (not (> x 0)) (not (< x 5)))
        // AY prints the same clause with `>` canonicalized to `<` (same atom).
        let out =
            outputs("(declare-const x Int)\n(assert (not (and (> x 0) (< x 5))))\n(apply nnf)\n");
        assert_eq!(
            out.last().map(String::as_str),
            Some(
                "(goals\n(goal\n  (or (not (< 0 x)) (not (< x 5)))\n  :precision precise :depth 1)\n)"
            ),
            "nnf must push the negation to the atoms; got {out:?}"
        );
    }

    #[test]
    fn apply_nnf_iff_splits_into_two_or_clauses_like_z3() {
        // Bool `=` is iff. z3: (a↔b) ⇒ (or (not a) b) ∧ (or a (not b)), printed as
        // two goal formulas after the top-level `and` is split.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(assert (= a b))\n(apply nnf)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some(
                "(goals\n(goal\n  (or b (not a))\n  (or a (not b))\n  :precision precise :depth 1)\n)"
            ),
            "iff must become (¬a∨b)∧(a∨¬b) split into two clauses; got {out:?}"
        );
    }

    #[test]
    fn apply_nnf_xor_uses_the_conjunctive_form_like_z3() {
        // z3: (a⊕b) ⇒ (or a b) ∧ (or (not a) (not b)) — the conjunctive parity
        // form, split into two goal formulas. AY matches verbatim.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(assert (xor a b))\n(apply nnf)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some(
                "(goals\n(goal\n  (or a b)\n  (or (not a) (not b))\n  :precision precise :depth 1)\n)"
            ),
            "xor must become (a∨b)∧(¬a∨¬b); got {out:?}"
        );
    }

    #[test]
    fn apply_nnf_bool_ite_uses_the_conjunctive_form_like_z3() {
        // z3: (ite a b c) ⇒ (or (not a) b) ∧ (or a c), split into two formulas.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(declare-const c Bool)\n(assert (ite a b c))\n(apply nnf)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (or b (not a))\n  (or a c)\n  :precision precise :depth 1)\n)"),
            "bool ite must become (¬a∨b)∧(a∨c); got {out:?}"
        );
    }

    #[test]
    fn apply_nnf_negated_implies_splits_into_literals_like_z3() {
        // ¬(a→b) ≡ a ∧ ¬b. z3 prints the two literals `a` and `(not b)` as
        // separate goal formulas; AY matches verbatim.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(assert (not (=> a b)))\n(apply nnf)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  a\n  (not b)\n  :precision precise :depth 1)\n)"),
            "¬(a→b) must split into a and (not b); got {out:?}"
        );
    }

    #[test]
    fn apply_nnf_does_not_mutate_the_real_assertion_stack() {
        // GOAL PRESERVATION: (apply) is a read-only query; the assertion stack
        // must be untouched so a following check-sat solves the ORIGINAL problem.
        let mut exec = Executor::new();
        for cmd in &parse("(declare-const a Bool)\n(declare-const b Bool)\n(assert (= a b))\n")
            .expect("setup parses")
        {
            exec.execute(cmd).expect("setup executes");
        }
        let before = exec.ctx.assertions.clone();
        for cmd in &parse("(apply nnf)").expect("apply parses") {
            exec.execute(cmd).expect("apply executes");
        }
        assert_eq!(
            exec.ctx.assertions, before,
            "(apply nnf) must not mutate the real assertion stack"
        );
    }

    #[test]
    fn check_sat_after_apply_nnf_preserves_an_unsat_verdict() {
        // GOAL PRESERVATION: nnf is equivalence-preserving, so the ORIGINAL
        // verdict is intact. (a ↔ ¬a) is UNSAT before and after the apply.
        let out =
            outputs("(declare-const a Bool)\n(assert (= a (not a)))\n(apply nnf)\n(check-sat)\n");
        assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
    }

    #[test]
    fn check_sat_after_apply_nnf_preserves_a_sat_verdict() {
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(assert (xor a b))\n(apply nnf)\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("sat"), "{out:?}");
    }

    // -----------------------------------------------------------------------
    // bit-blast (QF_BV goal -> pure-Boolean goal). Each check-sat cross-check
    // was independently verified against z3 4.15.4 on the same script.
    // -----------------------------------------------------------------------

    /// Whether a printed `(goals ...)` block mentions any bit-vector operator or
    /// sort — used to assert the blasted goal is pure Boolean.
    fn mentions_bv(goal: &str) -> bool {
        // BV operator tokens and the `(_ BitVec n)` sort / `#b`/`#x` literals.
        const BV_TOKENS: &[&str] = &[
            "BitVec",
            "bvadd",
            "bvsub",
            "bvmul",
            "bvand",
            "bvor",
            "bvxor",
            "bvnot",
            "bvneg",
            "bvnand",
            "bvnor",
            "bvxnor",
            "bvult",
            "bvule",
            "bvugt",
            "bvuge",
            "bvslt",
            "bvsle",
            "bvsgt",
            "bvsge",
            "bvshl",
            "bvlshr",
            "bvashr",
            "concat",
            "extract",
            "zero_extend",
            "sign_extend",
            "#b",
            "#x",
        ];
        BV_TOKENS.iter().any(|t| goal.contains(t))
    }

    #[test]
    fn apply_bit_blast_on_qf_bv_produces_a_pure_bool_goal() {
        // (apply bit-blast) on a QF_BV goal must print a goal with NO bit-vector
        // terms — every BV var/op is replaced by its Boolean circuit.
        let out = outputs(
            "(declare-const x (_ BitVec 4))\n(declare-const y (_ BitVec 4))\n(assert (bvult (bvadd x y) (bvand x y)))\n(apply bit-blast)\n",
        );
        let goal = out.last().expect("apply produces a goal");
        assert!(
            goal.starts_with("(goals"),
            "bit-blast must print a (goals ...) block; got {goal}"
        );
        assert!(
            !mentions_bv(goal),
            "the blasted goal must contain NO bit-vector terms; got {goal}"
        );
    }

    #[test]
    fn apply_bit_blast_does_not_mutate_the_real_assertion_stack() {
        // GOAL PRESERVATION: (apply) is a read-only query; the BV assertion stack
        // must be untouched so a following check-sat solves the ORIGINAL problem.
        let mut exec = Executor::new();
        for cmd in &parse(
            "(declare-const x (_ BitVec 8))\n(declare-const y (_ BitVec 8))\n(assert (= (bvadd x y) y))\n",
        )
        .expect("setup parses")
        {
            exec.execute(cmd).expect("setup executes");
        }
        let before = exec.ctx.assertions.clone();
        for cmd in &parse("(apply bit-blast)").expect("apply parses") {
            exec.execute(cmd).expect("apply executes");
        }
        assert_eq!(
            exec.ctx.assertions, before,
            "(apply bit-blast) must not mutate the real assertion stack"
        );
    }

    #[test]
    fn check_sat_after_apply_bit_blast_preserves_an_unsat_verdict() {
        // x = x+1 (mod 2^4) is UNSAT; the verdict is intact across the read-only
        // apply. Cross-checked: z3 4.15.4 also reports unsat.
        let out = outputs(
            "(declare-const x (_ BitVec 4))\n(assert (= x (bvadd x #b0001)))\n(apply bit-blast)\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
    }

    #[test]
    fn check_sat_after_apply_bit_blast_preserves_a_sat_verdict() {
        // A satisfiable QF_BV goal stays SAT across the apply. z3 4.15.4: sat.
        let out = outputs(
            "(declare-const x (_ BitVec 4))\n(declare-const y (_ BitVec 4))\n(assert (bvult x y))\n(assert (bvult y (bvadd x x)))\n(apply bit-blast)\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("sat"), "{out:?}");
    }

    #[test]
    fn apply_bit_blast_on_a_bv_free_goal_is_an_honest_identity() {
        // z3's bit-blast on a non-BV goal is the identity. AY's `BitBlast` pass
        // reports no progress on a BV-free goal, so `(apply bit-blast)` echoes the
        // original assertion (here depth 1 — a primitive was applied).
        let out = outputs(
            "(declare-const p Bool)\n(declare-const q Bool)\n(assert (or p q))\n(apply bit-blast)\n",
        );
        let goal = out.last().expect("apply produces a goal");
        assert!(
            goal.contains("(or p q)") && !mentions_bv(goal),
            "a BV-free goal must be echoed unchanged; got {goal}"
        );
    }

    #[test]
    fn apply_bit_blast_blasts_rotate_and_bvcomp_to_pure_bool() {
        // The newly-supported wire ops — a constant rotate and bvcomp — must blast
        // to a pure-Boolean goal with NO bit-vector terms (cross-checked vs z3
        // 4.15.4, which likewise blasts `(_ rotate_left k)` and `bvcomp`).
        let out = outputs(
            "(declare-const x (_ BitVec 4))\n(declare-const y (_ BitVec 4))\n(assert (bvult ((_ rotate_left 1) x) ((_ rotate_right 1) y)))\n(assert (= (bvcomp x y) #b1))\n(apply bit-blast)\n",
        );
        let goal = out.last().expect("apply produces a goal");
        assert!(
            goal.starts_with("(goals") && !mentions_bv(goal),
            "rotate/bvcomp must blast to a pure-Boolean goal; got {goal}"
        );
    }

    #[test]
    fn apply_bit_blast_on_out_of_fragment_bvudiv_honestly_fails() {
        // SOUNDNESS / HONESTY: z3's bit-blast on a `bvudiv` goal errors with
        //   (error "tactic failed: operator bvudiv is not supported, ...")
        // rather than echoing the input. AY must likewise HONESTLY FAIL — never a
        // silent successful identity for a goal it did not actually blast.
        let out = outputs(
            "(declare-const x (_ BitVec 4))\n(declare-const y (_ BitVec 4))\n(assert (= (bvudiv x y) #b0001))\n(apply bit-blast)\n",
        );
        let goal = out.last().expect("apply produces output");
        assert!(
            goal.starts_with("(error \"tactic failed:") && goal.contains("bvudiv"),
            "an out-of-fragment bvudiv goal must produce an honest tactic-failure \
             error naming bvudiv, NOT the input verbatim; got {goal}"
        );
        assert!(
            !goal.contains("(goals"),
            "honest failure must not emit a (goals ...) block; got {goal}"
        );
    }

    #[test]
    fn apply_bit_blast_out_of_fragment_does_not_echo_the_input_goal() {
        // Regression for the rejected FAKE: the old pass echoed the input verbatim
        // as a successful (goals ...) block on an out-of-fragment goal. The honest
        // path emits an error, so the printed output must NOT contain the input's
        // bvudiv term as a blasted goal.
        let out = outputs(
            "(declare-const x (_ BitVec 8))\n(declare-const y (_ BitVec 8))\n(assert (bvuge (bvsdiv x y) y))\n(apply bit-blast)\n",
        );
        let goal = out.last().expect("apply produces output");
        assert!(
            goal.starts_with("(error \"tactic failed:"),
            "an out-of-fragment bvsdiv goal must fail honestly, not echo a goal; got {goal}"
        );
    }

    #[test]
    fn apply_split_clause_prints_one_goal_per_disjunct() {
        // Matches z3: `(apply split-clause)` on {(or a b), c} prints TWO goals,
        // {a, c} and {b, c}, each at depth 1.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(declare-const c Bool)\n(assert (or a b))\n(assert c)\n(apply split-clause)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some(
                "(goals\n(goal\n  a\n  c\n  :precision precise :depth 1)\n(goal\n  b\n  c\n  :precision precise :depth 1)\n)"
            ),
            "split-clause must print two goals like z3; got {out:?}"
        );
    }

    #[test]
    fn check_sat_after_split_clause_is_the_disjunction_verdict() {
        // GOAL PRESERVATION: split-clause is a sound case split, so a following
        // check-sat still solves the ORIGINAL problem. Here (or a b) ∧ c is SAT.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(declare-const c Bool)\n(assert (or a b))\n(assert c)\n(apply split-clause)\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("sat"), "{out:?}");
    }

    #[test]
    fn apply_fail_prints_the_z3_tactic_failed_error() {
        // z3 prints `(error "tactic failed: fail tactic")` — AY matches exactly.
        let out = outputs("(declare-const x Int)\n(assert (> x 5))\n(apply fail)\n");
        assert_eq!(
            out.last().map(String::as_str),
            Some("(error \"tactic failed: fail tactic\")"),
            "{out:?}"
        );
    }

    #[test]
    fn apply_or_else_uses_the_fallback_when_the_first_fails() {
        // (or-else fail elim-and): fail fails, so elim-and runs on the original.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(assert (and a b))\n(apply (or-else fail elim-and))\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  a\n  b\n  :precision precise :depth 1)\n)"),
            "or-else must fall through to the fallback on failure; got {out:?}"
        );
    }

    #[test]
    fn apply_repeat_reaches_the_fixpoint_at_depth_one() {
        // (repeat elim-and) on a nested and flattens fully and stops; depth 1,
        // matching z3's repeat elim-and.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(declare-const c Bool)\n(assert (and (and a b) c))\n(apply (repeat elim-and))\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  a\n  b\n  c\n  :precision precise :depth 1)\n)"),
            "{out:?}"
        );
    }

    #[test]
    fn apply_then_split_clause_simplify_bumps_each_subgoal_depth() {
        // (then split-clause simplify): split into 2 goals (depth 1) then simplify
        // each (depth 2). Matches z3's per-goal depth accounting.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(assert (or a b))\n(apply (then split-clause simplify))\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some(
                "(goals\n(goal\n  a\n  :precision precise :depth 2)\n(goal\n  b\n  :precision precise :depth 2)\n)"
            ),
            "{out:?}"
        );
    }

    #[test]
    fn apply_then_simplify_solve_eqs_is_depth_two() {
        // Explicit acceptance: (apply (then simplify solve-eqs)) is depth 2, even
        // though solve-eqs makes no progress here (each primitive counts once).
        let out = outputs(
            "(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n(apply (then simplify solve-eqs))\n",
        );
        let goal = out.last().expect("apply produces a goal");
        assert!(
            goal.contains(":depth 2)"),
            "then simplify solve-eqs must be depth 2; got {goal}"
        );
    }

    // -----------------------------------------------------------------------
    // PROBE Z3-PARITY (when/fail-if gating). Each expected output below is the
    // VERBATIM output of z3 4.15.4 on the same script, so these are genuine
    // cross-checks of the probe VALUES that drive when/fail-if — not just
    // AY-internal consistency.
    // -----------------------------------------------------------------------

    #[test]
    fn apply_when_num_consts_on_pure_bool_goal_skips_like_z3() {
        // ACCEPTANCE: z3's num-consts EXCLUDES Boolean constants, so on (or a b)
        // with a,b : Bool it is 0. `(when (> num-consts 0) split-clause)` must
        // therefore SKIP (gate false) and print the goal unchanged at depth 0 —
        // NOT split. z3 4.15.4 prints exactly:
        //   (goals
        //   (goal
        //     (or a b)
        //     :precision precise :depth 0)
        //   )
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(assert (or a b))\n(apply (when (> num-consts 0) split-clause))\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (or a b)\n  :precision precise :depth 0)\n)"),
            "num-consts must exclude Bool consts -> gate false -> skip; got {out:?}"
        );
    }

    #[test]
    fn apply_when_num_consts_on_mixed_goal_gates_true_like_z3() {
        // z3 counts the single Int constant x (the Bool p is excluded), so
        // num-consts = 1 > 0 and split-clause RUNS. The goal has no top-level
        // clause, so it fails with z3's exact error. z3 4.15.4 prints:
        //   (error "tactic failed: split-clause tactic failed, goal does not contain any clause")
        let out = outputs(
            "(declare-const x Int)\n(declare-const p Bool)\n(assert (> x 0))\n(assert p)\n(apply (when (> num-consts 0) split-clause))\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some(
                "(error \"tactic failed: split-clause tactic failed, goal does not contain any clause\")"
            ),
            "num-consts must count the Int const (Bool excluded) -> gate true -> split-clause runs and fails; got {out:?}"
        );
    }

    #[test]
    fn apply_when_size_splits_top_level_conjunction_like_z3() {
        // z3 splits the top-level `and` into two formulas, so size = 2. The
        // `(when (= size 2) fail)` gate is therefore true and fails with z3's
        // exact error. (Verified with z3 4.15.4: `(and a b)` -> size 2.)
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(assert (and a b))\n(apply (when (= size 2) fail))\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(error \"tactic failed: fail tactic\")"),
            "size must count post-split conjuncts (z3: (and a b) -> 2); got {out:?}"
        );
    }

    #[test]
    fn apply_when_num_exprs_splits_top_level_conjunction_like_z3() {
        // z3's num-exprs on (and a b) is 2: it splits the top-level `and` into
        // [a, b] and does NOT count the split-away `and` node. The
        // `(when (= num-exprs 2) fail)` gate is true and fails. (z3 4.15.4.)
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(assert (and a b))\n(apply (when (= num-exprs 2) fail))\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(error \"tactic failed: fail tactic\")"),
            "num-exprs must exclude the split-away `and` node (z3: (and a b) -> 2); got {out:?}"
        );
    }

    #[test]
    fn apply_fail_if_num_consts_on_bool_goal_does_not_fire_like_z3() {
        // Cross-check the OTHER gate: `(fail-if (> num-consts 0))` on a pure-Bool
        // goal must NOT fail (num-consts = 0), so it acts as skip and prints the
        // goal at depth 0. z3 4.15.4 prints the goal, no error.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(assert (or a b))\n(apply (fail-if (> num-consts 0)))\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (or a b)\n  :precision precise :depth 0)\n)"),
            "fail-if must not fire when num-consts excludes the Bool consts (0); got {out:?}"
        );
    }

    #[test]
    fn apply_tseitin_cnf_rewrites_non_cnf_into_a_clausal_goal() {
        // (apply tseitin-cnf) on a DNF formula must emit a real CNF goal at depth
        // 1 — NOT the old unsound empty stub — introducing a fresh aux var for
        // the nested conjunction. The exact clause set differs from z3's (z3
        // distributes small formulas), but it is genuinely clausal and
        // equisatisfiable (verified by the check-sat regressions below).
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(declare-const c Bool)\n(assert (or (and a b) c))\n(apply tseitin-cnf)\n",
        );
        let goal = out.last().expect("apply produces a goal");
        assert_ne!(
            goal.as_str(),
            OLD_UNSOUND_EMPTY_STUB,
            "tseitin-cnf must emit the real CNF goal, not the unsound empty stub"
        );
        assert!(
            goal.contains(":depth 1)"),
            "tseitin-cnf is one primitive: {goal}"
        );
        assert!(
            goal.contains("tseitin"),
            "a nested conjunction must introduce a fresh aux var: {goal}"
        );
        assert!(
            goal.contains("(or"),
            "the CNF goal must contain disjunctive clauses: {goal}"
        );
    }

    #[test]
    fn apply_non_z3_cnf_alias_is_rejected() {
        // Z3 5.0.0 rejects `cnf`; AY's exact compatibility surface must too.
        assert!(
            parse("(apply cnf)").is_err(),
            "`cnf` is not a Z3 5.0.0 tactic"
        );
    }

    #[test]
    fn check_sat_after_apply_tseitin_cnf_preserves_a_sat_verdict() {
        // GOAL PRESERVATION (equisatisfiability): (apply) is read-only, so the
        // following check-sat still solves the ORIGINAL problem. (or (and a b) c)
        // is SAT.
        let out = outputs(
            "(declare-const a Bool)\n(declare-const b Bool)\n(declare-const c Bool)\n(assert (or (and a b) c))\n(apply tseitin-cnf)\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("sat"), "{out:?}");
    }

    #[test]
    fn check_sat_after_apply_tseitin_cnf_preserves_an_unsat_verdict() {
        // (and a (not a)) wrapped so the top is not a bare conjunction: xor with
        // itself style. Here: (= a (not a)) is UNSAT; tseitin-cnf must keep it so.
        let out = outputs(
            "(declare-const a Bool)\n(assert (= a (not a)))\n(apply tseitin-cnf)\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
    }

    #[test]
    fn apply_tseitin_cnf_does_not_mutate_the_real_assertion_stack() {
        // GOAL PRESERVATION is a soundness property: apply is a read-only query;
        // the real assertion stack (including the aux-var-free original) must be
        // untouched so a following check-sat solves the ORIGINAL problem.
        let mut exec = Executor::new();
        for cmd in &parse(
            "(declare-const a Bool)\n(declare-const b Bool)\n(declare-const c Bool)\n(assert (or (and a b) c))\n",
        )
        .expect("setup parses")
        {
            exec.execute(cmd).expect("setup executes");
        }
        let before = exec.ctx.assertions.clone();
        for cmd in &parse("(apply tseitin-cnf)").expect("apply parses") {
            exec.execute(cmd).expect("apply executes");
        }
        assert_eq!(
            exec.ctx.assertions, before,
            "(apply tseitin-cnf) must not mutate the real assertion stack"
        );
    }

    // -----------------------------------------------------------------------
    // P3 batch N+1: full z3-4.15.4 registry semantics on the (apply) surface.
    // Every expected output measured against z3 4.15.4 (2026-07-18 sweep).
    // -----------------------------------------------------------------------

    #[test]
    fn apply_class_s_strategy_name_is_the_truthful_identity_at_depth_zero() {
        // (apply qflia) prints the goal unchanged (z3 runs the whole strategy
        // and empties the goal — a documented goal-shape divergence, never a
        // verdict). The verdict twin below proves csu still decides.
        let out = outputs("(declare-const x Int)\n(assert (> x 5))\n(apply qflia)\n");
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (< 5 x)\n  :precision precise :depth 0)\n)"),
            "class S must be the truthful identity; got {out:?}"
        );
    }

    #[test]
    fn check_sat_using_class_s_name_still_decides_both_verdicts() {
        // csu verdict twins (battery item 2): registration must not change the
        // engine-computed verdict in either direction.
        let sat = outputs("(declare-const x Int)\n(assert (> x 5))\n(check-sat-using qflia)\n");
        assert_eq!(sat.last().map(String::as_str), Some("sat"), "{sat:?}");
        let unsat = outputs(
            "(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n(check-sat-using qflia)\n",
        );
        assert_eq!(unsat.last().map(String::as_str), Some("unsat"), "{unsat:?}");
    }

    #[test]
    fn apply_diff_neq_fails_honestly_with_the_z3_byte_text() {
        // CLASS F pinned test (review objection: the silent-Skip hazard). The
        // SMT-LIB path must FAIL — never a silent identity success.
        let out = outputs("(declare-const x Int)\n(assert (> x 5))\n(apply diff-neq)\n");
        assert_eq!(
            out.last().map(String::as_str),
            Some("(error \"tactic failed: goal is not diff neq\")"),
            "diff-neq must fail honestly with z3's byte text; got {out:?}"
        );
    }

    #[test]
    fn apply_or_else_diff_neq_skip_falls_through_like_z3() {
        // CLASS F or-else routing parity (battery item 5): the honest failure
        // is caught and the fallback branch runs on the ORIGINAL goal, exactly
        // like z3 (measured: z3 takes the fallback, depth 0 for skip).
        let out =
            outputs("(declare-const x Int)\n(assert (> x 5))\n(apply (or-else diff-neq skip))\n");
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (< 5 x)\n  :precision precise :depth 0)\n)"),
            "or-else must fall through the honest diff-neq failure; got {out:?}"
        );
    }

    #[test]
    fn apply_or_else_pb2bv_skip_takes_the_fallback_like_z3() {
        // Second F-class routing pin (measured z3: fallback, depth 0).
        let out =
            outputs("(declare-const x Int)\n(assert (> x 5))\n(apply (or-else pb2bv skip))\n");
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (< 5 x)\n  :precision precise :depth 0)\n)"),
            "{out:?}"
        );
    }

    #[test]
    fn apply_bv1_blast_is_identity_on_a_bv_free_goal_like_z3() {
        // Review objection 3: z3's bv1-blast SUCCEEDS (identity, depth 1) on
        // the Int probe — an unconditional failure would wrongly divert
        // (or-else bv1-blast X) to the fallback. Measured z3 4.15.4.
        let out = outputs("(declare-const x Int)\n(assert (> x 5))\n(apply bv1-blast)\n");
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (< 5 x)\n  :precision precise :depth 1)\n)"),
            "bv1-blast on a BV-free goal must be the depth-1 identity; got {out:?}"
        );
    }

    #[test]
    fn apply_bv1_blast_fails_on_a_bv_goal_with_the_z3_byte_text() {
        // Measured z3 4.15.4 on the 8-bit BV probe.
        let out = outputs(
            "(declare-const b (_ BitVec 8))\n(assert (= (bvadd b #x01) #x03))\n(apply bv1-blast)\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(error \"tactic failed: bv1 blaster cannot be applied to goal\")"),
            "{out:?}"
        );
    }

    #[test]
    fn apply_or_else_bv1_blast_simplify_keeps_branch_one_on_int_goals_like_z3() {
        // Battery item 5 (the design's own or-else routing check): on a
        // BV-free goal z3 KEEPS branch 1 (bv1-blast succeeds, depth 1); an
        // unconditional FailMsg realization would wrongly take the fallback.
        let out = outputs(
            "(declare-const x Int)\n(assert (> x 5))\n(apply (or-else bv1-blast simplify))\n",
        );
        assert_eq!(
            out.last().map(String::as_str),
            Some("(goals\n(goal\n  (< 5 x)\n  :precision precise :depth 1)\n)"),
            "or-else must keep the succeeding bv1-blast branch; got {out:?}"
        );
    }

    #[test]
    fn apply_fail_if_undecided_matches_z3_semantics() {
        // Measured z3 4.15.4 (c7/c8): undecided goal -> `(error "tactic
        // failed: undecided")`; a {false} goal is decided -> identity.
        let undecided =
            outputs("(declare-const x Int)\n(assert (> x 5))\n(apply fail-if-undecided)\n");
        assert_eq!(
            undecided.last().map(String::as_str),
            Some("(error \"tactic failed: undecided\")"),
            "{undecided:?}"
        );
        let decided = outputs("(assert false)\n(apply fail-if-undecided)\n");
        assert_eq!(
            decided.last().map(String::as_str),
            Some("(goals\n(goal\n  false\n  :precision precise :depth 0)\n)"),
            "a decided (false) goal must pass through unchanged; got {decided:?}"
        );
    }

    #[test]
    fn apply_if_picks_the_else_branch_on_a_false_probe_like_z3() {
        // Measured z3 4.15.4 (c1/c2): num-consts excludes Bool consts, so the
        // probe is false on a pure-Bool goal -> else branch (skip) -> the goal
        // prints unchanged at depth 0. `if` and `cond` are synonyms.
        for head in ["if", "cond"] {
            let out = outputs(&format!(
                "(declare-const a Bool)\n(declare-const b Bool)\n(assert (and a b))\n(apply ({head} (> num-consts 0) elim-and skip))\n",
            ));
            assert_eq!(
                out.last().map(String::as_str),
                Some("(goals\n(goal\n  a\n  b\n  :precision precise :depth 0)\n)"),
                "({head}) with a false probe must run the else branch; got {out:?}"
            );
        }
    }

    #[test]
    fn apply_if_propagates_the_chosen_branch_failure_like_z3() {
        // Measured z3 4.15.4 (c3): `(apply (if (> 1 0) fail skip))` ERRORS —
        // the chosen branch's failure propagates; it never falls through to
        // the other branch (the semantic trap: or-else-style fallthrough here
        // would be a real z3 divergence).
        let out =
            outputs("(declare-const x Int)\n(assert (> x 5))\n(apply (if (> 1 0) fail skip))\n");
        assert_eq!(
            out.last().map(String::as_str),
            Some("(error \"tactic failed: fail tactic\")"),
            "the chosen if-branch failure must propagate; got {out:?}"
        );
    }

    #[test]
    fn apply_when_with_a_batch_probe_gates_soundly() {
        // `is-unbounded` (newly registered) is TRUE on {x > 5} (x has no upper
        // bound — matches measured libz3). The gated `smt` is the identity, so
        // the goal passes through at depth 0; the follow-up check-sat proves
        // the apply changed nothing.
        let out = outputs(
            "(declare-const x Int)\n(assert (> x 5))\n(apply (when is-unbounded smt))\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("sat"), "{out:?}");
        let goal = &out[out.len() - 2];
        assert_eq!(
            goal.as_str(),
            "(goals\n(goal\n  (< 5 x)\n  :precision precise :depth 0)\n)",
            "when(is-unbounded, smt) must be a sound identity gate; got {goal}"
        );
    }

    #[test]
    fn check_sat_after_class_f_apply_failure_still_decides() {
        // An honest tactic failure must not poison the script: the following
        // check-sat still solves the ORIGINAL problem (z3 parity, c9-style).
        let out = outputs(
            "(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n(apply diff-neq)\n(check-sat)\n",
        );
        assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
    }

    #[test]
    fn unknown_tactic_is_a_parse_error_not_a_silent_empty_goal() {
        // z3 rejects `(apply no-such-tactic)` with an "unknown tactic" error; AY
        // must too, rather than silently accepting it as an (unsound) empty goal.
        let err = parse("(apply no-such-tactic)")
            .expect_err("unknown tactic must be a parse error")
            .to_string();
        assert!(
            err.contains("unknown tactic"),
            "expected an unknown-tactic error like z3, got: {err}"
        );
    }
}
