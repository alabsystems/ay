// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked `assume` bridge for a binary authored `(distinct a b)` whose
//! canonical term is `(not (= x y))`.
//!
//! AY interns a binary `distinct` as the negated equality, with the equality's
//! operands in `TermId` order. The canonical text can therefore differ from
//! the problem file's in its head (`distinct` versus `not`/`=`), in operand
//! ORDER, and in bit-vector literal notation (`#x07` versus `#b00000111`).
//! Pinned carcara matches an `assume` against the problem syntactically, so the
//! authored text has to reach the `assume` while every consumer of the unit
//! reads the canonical literal. Measured on
//! `model_checker_consumer_quantified_models/signed_range64_fill_unsat.smt2`: without this
//! bridge the published leaf was `(assume t0 (not (= #b00000111 (select a
//! #b1..1))))` for the authored `(distinct (select a #xffffffffffffffff) #x07)`
//! and carcara 1.1.0 refused the document at `t0`.
//!
//! ```text
//! (assume tK.a (distinct a b))
//! (step tK.de (cl (= (distinct a b) (not (= a b)))) :rule distinct_elim)
//! (step tK.e (cl (not (= (distinct a b) (not (= a b)))) (not (distinct a b)) (not (= a b)))
//!   :rule equiv_pos2)
//! straight: (step tK (cl (not (= x y))) :rule resolution :premises (tK.e tK.de tK.a))
//! swapped:  (step tK.n (cl (not (= a b))) :rule resolution :premises (tK.e tK.de tK.a))
//!           (step tK (cl (not (= x y))) :rule not_symm :premises (tK.n))
//! ```
//!
//! Every step instantiates a rule pinned carcara implements, over operands
//! copied verbatim from the authored text. The only identification the bridge
//! makes is [`same_printed_term`] on each operand pair: byte identity, or
//! alternate bit-vector literal spellings that carcara's parser builds into one
//! constant. So `(not (= a b))` IS `(not (= x y))` to the checker (straight),
//! or `(not (= b a))` is (swapped). Any other operand difference, an n-ary
//! `distinct`, or a canonical term that is not a negated binary equality
//! declines the bridge and leaves the fail-closed surface validators in charge.

use super::super::surface_literal::same_printed_term;
use super::*;

/// The authored operands of a supported bridge, and whether the canonical
/// equality lists them in the opposite order.
struct DistinctEliminationOperands {
    left: String,
    right: String,
    swapped: bool,
}

fn distinct_elimination_operands(
    surface: &str,
    canonical: &str,
) -> Option<DistinctEliminationOperands> {
    let authored = split_application(surface, "distinct")?;
    let [left, right] = authored.as_slice() else {
        return None;
    };
    let negated = split_application(canonical, "not")?;
    let [equality] = negated.as_slice() else {
        return None;
    };
    let operands = split_application(equality, "=")?;
    let [first, second] = operands.as_slice() else {
        return None;
    };
    let swapped = if same_printed_term(left, first) && same_printed_term(right, second) {
        false
    } else if same_printed_term(left, second) && same_printed_term(right, first) {
        true
    } else {
        return None;
    };
    Some(DistinctEliminationOperands {
        left: left.clone(),
        right: right.clone(),
        swapped,
    })
}

/// Terms assumed by a premise of an explicitly annotated generic resolution.
///
/// Such a step keeps its dedicated distinct/equality bridge
/// (`distinct_eq_resolution_bridge`), which reads the PRINTED `(distinct a b)`
/// literal; confining the spelling to the `assume` would leave that step to
/// the blanket annotated-resolution surface gate, which refuses any document
/// carrying overrides. Only the steps' direct `assume` premises matter: the
/// bridge inspects exactly those printed clauses.
pub(super) fn annotated_resolution_premise_terms(proof: &Proof) -> HashSet<TermId> {
    let mut terms = HashSet::default();
    for step in &proof.steps {
        let ProofStep::Step {
            rule,
            premises,
            args,
            ..
        } = step
        else {
            continue;
        };
        if args.is_empty() || !super::super::resolution_args::is_generic_resolution(rule) {
            continue;
        }
        for premise in premises {
            if let Some(ProofStep::Assume(term)) = proof.steps.get(premise.0 as usize) {
                terms.insert(*term);
            }
        }
    }
    terms
}

/// Whether `surface` / `canonical` is a pair this bridge can print.
pub(super) fn distinct_elimination_is_supported(surface: &str, canonical: &str) -> bool {
    distinct_elimination_operands(surface, canonical).is_some()
}

/// The exact bridge text for proof id `id`, or `None` when the pair is not a
/// supported binary `distinct` elimination.
pub(super) fn render_distinct_elimination_bridge(
    id: ProofId,
    surface: &str,
    canonical: &str,
) -> Option<String> {
    let DistinctEliminationOperands {
        left,
        right,
        swapped,
    } = distinct_elimination_operands(surface, canonical)?;
    let eliminated = format!("(not (= {left} {right}))");
    let elimination = format!("(= {surface} {eliminated})");
    let mut output = format!(
        "(assume {id}.a {surface})\n\
         (step {id}.de (cl {elimination}) :rule distinct_elim)\n\
         (step {id}.e (cl (not {elimination}) (not {surface}) {eliminated}) :rule equiv_pos2)\n"
    );
    if swapped {
        output.push_str(&format!(
            "(step {id}.n (cl {eliminated}) :rule resolution :premises ({id}.e {id}.de {id}.a))\n\
             (step {id} (cl {canonical}) :rule not_symm :premises ({id}.n))"
        ));
    } else {
        output.push_str(&format!(
            "(step {id} (cl {canonical}) :rule resolution :premises ({id}.e {id}.de {id}.a))"
        ));
    }
    Some(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::try_export_alethe_with_problem_scope_and_overrides;
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{Symbol, TermStore};

    /// `(not (= x y))` / `(= x y)` refutation whose negated root carries the
    /// authored `surface`; returns the exported document (or its error) and
    /// the canonical text of the negated root.
    fn export_with_distinct_surface(
        build: impl FnOnce(&mut TermStore) -> (TermId, TermId),
        surface: &str,
    ) -> (Result<String, AlethePrintError>, String) {
        let mut terms = TermStore::new();
        let (left, right) = build(&mut terms);
        let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
        let negated = terms.mk_not_raw(equality);
        let canonical = crate::render_term_canonical(&terms, negated);
        let mut proof = Proof::new();
        let disequality = proof.add_assume(negated, None);
        let positive = proof.add_assume(equality, None);
        proof.add_resolution(Vec::new(), equality, positive, disequality);
        let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
        overrides.insert(negated, surface.to_string());
        let output = try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &[negated, equality],
            Some(&overrides),
        );
        (output, canonical)
    }

    fn int_pair(terms: &mut TermStore) -> (TermId, TermId) {
        (terms.mk_var("x", Sort::Int), terms.mk_var("y", Sort::Int))
    }

    fn operands_of(canonical: &str) -> (String, String) {
        let negated = split_application(canonical, "not").expect("canonical is a negation");
        let operands = split_application(&negated[0], "=").expect("canonical negates an equality");
        (operands[0].clone(), operands[1].clone())
    }

    #[test]
    fn swapped_authored_distinct_is_confined_with_distinct_elim_and_not_symm() {
        let mut terms = TermStore::new();
        let (x, y) = int_pair(&mut terms);
        let equality = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
        let negated = terms.mk_not_raw(equality);
        let (first, second) = operands_of(&crate::render_term_canonical(&terms, negated));
        let surface = format!("(distinct {second} {first})");

        let (output, canonical) = export_with_distinct_surface(int_pair, &surface);
        let output = output.expect("a swapped binary distinct has a checked assume bridge");
        let eliminated = format!("(not (= {second} {first}))");
        assert!(
            output.contains(&format!("(assume t0.a {surface})")),
            "{output}"
        );
        assert!(
            output.contains(&format!(
                "(step t0.de (cl (= {surface} {eliminated})) :rule distinct_elim)"
            )),
            "{output}"
        );
        assert!(
            output.contains(&format!(
                "(step t0 (cl {canonical}) :rule not_symm :premises (t0.n))"
            )),
            "{output}"
        );
        assert!(
            !output.contains(&format!("(assume t0 {canonical})")),
            "the canonical negated equality is not an assertion of the problem:\n{output}"
        );
    }

    #[test]
    fn straight_authored_distinct_resolves_directly_to_the_canonical_unit() {
        let mut terms = TermStore::new();
        let (x, y) = int_pair(&mut terms);
        let equality = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
        let negated = terms.mk_not_raw(equality);
        let (first, second) = operands_of(&crate::render_term_canonical(&terms, negated));
        let surface = format!("(distinct {first} {second})");

        let (output, canonical) = export_with_distinct_surface(int_pair, &surface);
        let output = output.expect("a straight binary distinct has a checked assume bridge");
        assert!(
            output.contains(&format!("(assume t0.a {surface})")),
            "{output}"
        );
        assert!(
            output.contains(&format!(
                "(step t0 (cl {canonical}) :rule resolution :premises (t0.e t0.de t0.a))"
            )),
            "{output}"
        );
        assert!(!output.contains(":rule not_symm"), "{output}");
    }

    #[test]
    fn bitvector_literal_notation_is_one_carcara_term_in_the_bridge() {
        let bv_pair = |terms: &mut TermStore| {
            let p = terms.mk_var("p", Sort::bitvec(8));
            let seven = terms.mk_bitvec(7.into(), 8);
            (p, seven)
        };
        let mut terms = TermStore::new();
        let (p, seven) = bv_pair(&mut terms);
        let equality = terms.mk_app(Symbol::named("="), [p, seven], Sort::Bool);
        let negated = terms.mk_not_raw(equality);
        let (first, second) = operands_of(&crate::render_term_canonical(&terms, negated));
        let hex = |operand: &str| {
            if operand == "p" {
                "p".to_string()
            } else {
                "#x07".to_string()
            }
        };
        // Authored in hexadecimal and in the opposite order to the canonical
        // `#b` rendering: `same_printed_term` identifies the literals.
        let surface = format!("(distinct {} {})", hex(&second), hex(&first));
        assert!(
            first.starts_with("#b") || second.starts_with("#b"),
            "canonical BV constant renders in binary: {first} {second}"
        );

        let (output, canonical) = export_with_distinct_surface(bv_pair, &surface);
        let output = output.expect("alternate BV literal notation still bridges");
        assert!(
            output.contains(&format!("(assume t0.a {surface})")),
            "{output}"
        );
        assert!(output.contains(":rule distinct_elim"), "{output}");
        assert!(
            output.contains(&format!(
                "(step t0 (cl {canonical}) :rule not_symm :premises (t0.n))"
            )),
            "{output}"
        );
    }

    #[test]
    fn distinct_over_different_operands_declines_the_bridge() {
        assert!(!distinct_elimination_is_supported(
            "(distinct x z)",
            "(not (= x y))"
        ));
        assert!(!distinct_elimination_is_supported(
            "(distinct x #x07)",
            "(not (= x #b00000110))"
        ));
        assert!(!distinct_elimination_is_supported(
            "(distinct x y z)",
            "(not (= x y))"
        ));
        assert!(!distinct_elimination_is_supported(
            "(distinct x y)",
            "(not (< x y))"
        ));
        assert!(!distinct_elimination_is_supported(
            "(distinct x y)",
            "(= x y)"
        ));
        let (output, _) = export_with_distinct_surface(int_pair, "(distinct x z)");
        assert!(
            output.map_or(true, |text| !text.contains("(assume t0.a")),
            "a mismatched operand must never be bridged"
        );
    }
}
