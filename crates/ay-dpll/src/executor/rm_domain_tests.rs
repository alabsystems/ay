// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the RoundingMode finite-domain coverage pass.

use super::*;
use crate::executor::Executor;
use crate::executor_types::SolveResult;

/// The authored shape the RoundingMode finite-domain expansion branches on
/// (`unsat_cert/rm_domain_expansion.rs`'s `RM_WRONG_PIN_UNSAT_SCRIPT`).
const RM_PIN_SCRIPT: &str = "(declare-const rm RoundingMode) \
     (assert (= (fp.roundToIntegral rm ((_ to_fp 8 24) RNE 2.5)) ((_ to_fp 8 24) RNE 2.0))) \
     (assert (= rm roundTowardPositive))";

fn rm_pin_executor() -> Executor {
    let commands = ay_frontend::parse(RM_PIN_SCRIPT).expect("RM pin fixture parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("RM pin fixture executes");
    executor
}

fn declared_rm_var(executor: &Executor) -> TermId {
    (0..executor.ctx.terms.len())
        .map(|index| TermId(u32::try_from(index).expect("arena index fits u32")))
        .find(|&id| matches!(executor.ctx.terms.get(id), TermData::Var(name, _) if name == "rm"))
        .expect("the fixture declares `rm`")
}

/// `roots[rm := RTN]` built the way every producer builds a branch image:
/// [`TermStore::substitute_terms`], which reinterns `App("=", args)`
/// directly and therefore does NOT canonicalize the operand order the way
/// `mk_eq` does.
fn substituted_rtn_branch(executor: &mut Executor) -> Vec<TermId> {
    let roots = executor.ctx.assertions.clone();
    let rtn = rm_literal_term(&mut executor.ctx.terms, RoundingMode::RTN);
    let variable = declared_rm_var(executor);
    let mut map = ay_core::kani_compat::DetHashMap::default();
    map.insert(variable, rtn);
    roots
        .iter()
        .map(|&root| executor.ctx.terms.substitute_terms(root, &map))
        .collect()
}

fn axioms_of(executor: &mut Executor, roots: &[TermId]) -> Vec<TermId> {
    match executor.rm_domain_axioms(roots) {
        RmDomainAxioms::Axioms(axioms) => axioms,
        RmDomainAxioms::NoMention => {
            panic!("the fixture mentions RoundingMode in a domain position")
        }
        RmDomainAxioms::FailClose => panic!("the fixture is fully coverable"),
    }
}

/// The regression: a literal-only equality that is NOT the term `mk_eq`
/// builds gets its own pin, because the distinct-5 axiom names only the
/// canonically-ordered atoms.
///
/// Without the pin this atom reaches the SAT layer as a FREE Boolean —
/// `check_fp_support` passes an equality whose two operands are both
/// literal modes — and the branch measured `unknown` where `unsat` was
/// available, at the probe AND at top level alike.
#[test]
fn a_substitution_built_rm_equality_gets_its_own_domain_pin() {
    let mut executor = rm_pin_executor();
    let image = substituted_rtn_branch(&mut executor);
    let atom = image[1];

    // The premise of the whole regression: this atom is a DIFFERENT
    // interned term from the one the smart constructor produces, so the
    // distinct-5 axiom cannot be speaking about it.
    let (left, right) = match executor.ctx.terms.get(atom) {
        TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2 => {
            (args[0], args[1])
        }
        other => panic!("the substituted root must be a binary equality, got {other:?}"),
    };
    let canonical = executor.ctx.terms.mk_eq(left, right);
    assert_ne!(
        canonical, atom,
        "fixture no longer exercises the non-canonical atom this pins"
    );

    let axioms = axioms_of(&mut executor, &image);
    let pin = executor.ctx.terms.mk_not(atom);
    assert!(
        axioms.contains(&pin),
        "the RM domain pass must pin the atom that is actually in the DAG"
    );
}

/// ...and the canonical spelling keeps the axiom set it always had. The
/// pass stays byte-compatible for every query built through the smart
/// constructors, which is every query the frontend and the public API
/// produce.
#[test]
fn a_canonical_rm_equality_adds_no_pin() {
    let mut executor = rm_pin_executor();
    let rtn = rm_literal_term(&mut executor.ctx.terms, RoundingMode::RTN);
    let rtp = rm_literal_term(&mut executor.ctx.terms, RoundingMode::RTP);
    let canonical = executor.ctx.terms.mk_eq(rtn, rtp);

    let axioms = axioms_of(&mut executor, &[canonical]);
    assert_eq!(
        axioms.len(),
        1,
        "distinct-5 alone already names the canonical atom: {:?}",
        axioms
            .iter()
            .map(|&t| executor.format_term(t))
            .collect::<Vec<_>>()
    );
}

/// PRODUCER/CHECKER PARITY, the F1 fence. Every axiom this pass emits —
/// distinct-5, each coverage disjunction, and every pin — must be one
/// AY's OWN strict RoundingMode checker re-derives from scratch.
///
/// This is what "make AY able to prove what it computes" means at an
/// injection site: `check_sat` hands each of these to
/// `push_array_axiom_assertion_site`, and `promote_rounding_mode_domain_lemmas`
/// can only label the ones `recognize_rounding_mode_domain` accepts. An
/// axiom outside that language is one AY asserts and then refuses to check.
///
/// MEASURED at 47773e309, the revision this replaces emitted exactly one
/// such axiom: the reflexive pin `(= RTP RTP)`, which the RM checker
/// rejects (it is `eq_reflexive` — a fact with no RoundingMode content —
/// not a five-element-domain fact).
#[test]
fn every_emitted_axiom_is_re_derived_by_the_strict_rm_checker() {
    let mut executor = rm_pin_executor();
    let image = substituted_rtn_branch(&mut executor);
    let mut roots = image.clone();
    // Add a declared RM constant so a coverage disjunction is emitted too,
    // and the guard covers all three axiom families this pass produces.
    let declared = executor.ctx.terms.mk_var("rm_other".to_string(), rm_sort());
    let rtz = rm_literal_term(&mut executor.ctx.terms, RoundingMode::RTZ);
    roots.push(executor.ctx.terms.mk_eq(declared, rtz));

    let axioms = axioms_of(&mut executor, &roots);
    assert!(
        axioms.len() >= 3,
        "the fixture must exercise distinct-5, a pin, and a coverage disjunction: {:?}",
        axioms
            .iter()
            .map(|&t| executor.format_term(t))
            .collect::<Vec<_>>()
    );
    for &axiom in &axioms {
        assert!(
            ay_proof::recognize_rounding_mode_domain(&executor.ctx.terms, &[axiom]),
            "Pass B emitted an axiom AY's own strict RoundingMode checker rejects: {}",
            executor.format_term(axiom)
        );
    }
}

/// A reflexive literal equality gets NO pin, and needs none.
///
/// It is TRUE by reflexivity rather than by the five-element domain fact,
/// so the only axiom that would state it is `eq_reflexive`, which the
/// strict RoundingMode checker rightly refuses. MEASURED (this test): the
/// solver already decides the raw-interned atom in BOTH polarities without
/// any axiom from this pass, so declining to pin costs nothing.
#[test]
fn a_reflexive_literal_equality_needs_no_pin() {
    let mut executor = rm_pin_executor();
    let rtp = rm_literal_term(&mut executor.ctx.terms, RoundingMode::RTP);
    // `mk_eq` folds `(= RTP RTP)` to `true`, so the only way this atom
    // exists is a direct intern — exactly what `substitute_terms` does.
    let atom = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![rtp, rtp], Sort::Bool);
    assert!(
        matches!(executor.ctx.terms.get(atom), TermData::App(..)),
        "the reflexive atom must survive as an application, not fold"
    );

    let axioms = axioms_of(&mut executor, &[atom]);
    assert_eq!(
        axioms.len(),
        1,
        "a reflexive literal equality must add no pin: {:?}",
        axioms
            .iter()
            .map(|&t| executor.format_term(t))
            .collect::<Vec<_>>()
    );

    let negated = executor.ctx.terms.mk_not(atom);
    assert!(
        solve_over(&executor, negated).is_unsat(),
        "`(not (= RTP RTP))` must refute without a pin"
    );
    assert!(
        matches!(solve_over(&executor, atom), SolveResult::Sat),
        "`(= RTP RTP)` must stay satisfiable without a pin"
    );
}

/// A fresh top-level solve over a single root, sharing `source`'s arena.
fn solve_over(source: &Executor, root: TermId) -> SolveResult {
    let mut top = Executor::new();
    top.ctx = source.ctx.clone();
    top.ctx
        .process_command(&ay_frontend::Command::ResetAssertions)
        .expect("the derived query resets the outer assertions");
    top.ctx.add_assertion_with_parsed(
        root,
        ay_frontend::command::Term::Symbol(
            crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.to_string(),
        ),
    );
    top.begin_public_solve(false);
    top.bind_unsat_query_assumptions(&[]);
    top.check_sat().expect("the top-level solve completes")
}

/// The recognizer's own scope, tested where the checker gate cannot mask it.
///
/// Both guards below are individually invisible end-to-end — the strict-checker
/// gate in [`RmLiteralAtoms::pins`] declines whatever they let through — so
/// they are asserted here directly. They are not redundant decoration: a
/// producer must construct only VALID axioms and rely on the checker to catch
/// drift, never the other way round.
#[test]
fn the_pin_recognizer_declines_reflexive_and_foreign_sorted_operands() {
    let mut executor = rm_pin_executor();
    let terms = &mut executor.ctx.terms;
    let rtn = rm_literal_term(terms, RoundingMode::RTN);
    let rtp = rm_literal_term(terms, RoundingMode::RTP);
    let equals = Symbol::named("=");

    // Positive control: two DIFFERENT modes at the RoundingMode sort.
    assert_eq!(
        literal_pins::rm_literal_disequality_operands(terms, &equals, &[rtn, rtp]),
        Some((rtn, rtp)),
        "a different-mode literal equality is the shape this pins"
    );

    // Reflexive: `not (= m m)` is FALSE, so emitting it would be unsound.
    assert!(
        literal_pins::rm_literal_disequality_operands(terms, &equals, &[rtn, rtn]).is_none(),
        "a reflexive literal equality must never yield a disequality pin"
    );

    // Foreign sort: `rm_literal_mode` matches by NAME alone, so without the
    // sort guard two Int constants that borrow mode spellings look like modes.
    let int_rne = terms.mk_app(Symbol::named("RNE"), vec![], Sort::Int);
    let int_rtz = terms.mk_app(Symbol::named("RTZ"), vec![], Sort::Int);
    assert!(
        literal_pins::rm_literal_disequality_operands(terms, &equals, &[int_rne, int_rtz])
            .is_none(),
        "an Int-sorted equality must never yield a RoundingMode domain pin"
    );
}

/// A literal spelling the strict checker does not read yields NO pin.
///
/// `rm_literal_mode` accepts a `Var`-form mode and the long SMT-LIB spellings;
/// the checker's `mode_index` accepts only a nullary `App` at the RoundingMode
/// sort under one of the five SHORT names. The pass must not emit an axiom that
/// falls in that gap — it would be one AY asserts and then refuses to check.
#[test]
fn an_unreadable_literal_spelling_yields_no_unchecked_pin() {
    for spelling in ["var", "long-name"] {
        let mut executor = rm_pin_executor();
        let (left, right) = {
            let terms = &mut executor.ctx.terms;
            if spelling == "var" {
                (
                    terms.mk_var("RTN".to_string(), rm_sort()),
                    terms.mk_var("RTP".to_string(), rm_sort()),
                )
            } else {
                (
                    terms.mk_app(Symbol::named("roundTowardNegative"), vec![], rm_sort()),
                    terms.mk_app(Symbol::named("roundTowardPositive"), vec![], rm_sort()),
                )
            }
        };
        // The recognizer accepts it: both operands ARE mode literals at the
        // RoundingMode sort, and the modes differ.
        assert!(
            literal_pins::rm_literal_disequality_operands(
                &executor.ctx.terms,
                &Symbol::named("="),
                &[left, right]
            )
            .is_some(),
            "{spelling}: the fixture must reach the checker gate to test it"
        );
        let atom = executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), vec![left, right], Sort::Bool);

        let axioms = axioms_of(&mut executor, &[atom]);
        assert_eq!(
            axioms.len(),
            1,
            "{spelling}: a spelling the strict checker cannot read must add no pin: {:?}",
            axioms
                .iter()
                .map(|&t| executor.format_term(t))
                .collect::<Vec<_>>()
        );
        for &axiom in &axioms {
            assert!(
                ay_proof::recognize_rounding_mode_domain(&executor.ctx.terms, &[axiom]),
                "{spelling}: emitted an axiom the strict checker rejects: {}",
                executor.format_term(axiom)
            );
        }
    }
}

/// The pinned language is finite and small: the twenty ordered pairs of the
/// five canonical mode terms.
///
/// This is what makes [`RmLiteralAtoms::pins`]'s budget arm a backstop rather
/// than a live guard, and it is asserted rather than asserted-in-prose: every
/// admissible pin has both operands among five hash-consed terms.
#[test]
fn the_pinned_language_is_the_twenty_ordered_pairs() {
    let mut executor = rm_pin_executor();
    let lits: Vec<TermId> = RM_MODES
        .iter()
        .map(|&mode| rm_literal_term(&mut executor.ctx.terms, mode))
        .collect();
    let mut roots = Vec::new();
    for &left in &lits {
        for &right in &lits {
            roots.push(executor.ctx.terms.mk_app(
                Symbol::named("="),
                vec![left, right],
                Sort::Bool,
            ));
        }
    }

    let axioms = axioms_of(&mut executor, &roots);
    // distinct-5, then the pins. Ten of the twenty ordered different-mode pairs
    // ARE the atoms `mk_distinct` canonicalized to, so they are skipped.
    assert_eq!(
        axioms.len(),
        1 + 10,
        "every emitted axiom: {:?}",
        axioms
            .iter()
            .map(|&t| executor.format_term(t))
            .collect::<Vec<_>>()
    );
    for &axiom in &axioms {
        assert!(
            ay_proof::recognize_rounding_mode_domain(&executor.ctx.terms, &[axiom]),
            "emitted an axiom the strict checker rejects: {}",
            executor.format_term(axiom)
        );
    }
}
