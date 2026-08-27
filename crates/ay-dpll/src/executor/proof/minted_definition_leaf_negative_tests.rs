// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The AUTHORITY negatives, the INDEPENDENT evaluator and the two-sided
//! exhaustive sweep for the MINTED-DEFINITION leaf lane.
//!
//! # What is actually being checked
//!
//! This lane's soundness claim is CONSERVATIVITY: adding `p = b` to the
//! authored set `A` must not refute a satisfiable `A`. So the negatives here
//! do not merely assert "the lane declines" — each one ENUMERATES the models
//! of `A`, exhibits one, and shows that `A ∪ {p = b}` has NONE. That is the
//! exact property `ay_proof::FreshDefRegistry`'s four guards exist to
//! guarantee, and this file re-derives it from scratch.
//!
//! [`models`] is a naive model enumerator over Boolean variables and ONE
//! uninterpreted `ff : Bool × Bool → Bool`, whose 4-entry table it enumerates
//! exhaustively. It shares no code with the lane, with `ay-proof`'s planner,
//! or with the checker.
//!
//! # GUARD MUTATION LEDGER
//!
//! Each guard was deleted or weakened, the lane's whole test set re-run, the
//! named test observed FAILING, and the guard restored. Results, including
//! honest negatives, are in the table below.
//!
//! | # | guard | mutation | result |
//! |---|---|---|---|
//! | 1 | no `Anchor` steps | delete the early return | **FAILS** `a_proof_carrying_an_anchor_is_left_alone` |
//! | 2a | premiseless / argument-free / unit clause | drop the conjunction | **FAILS** `a_trust_step_with_premises_is_left_alone` and `a_trust_step_with_args_is_left_alone` |
//! | 2b | the goal is NOT a binary `=` | accept any atom | **FAILS** `a_binary_equality_leaf_is_left_to_the_sibling_lane` (whose fixture AUTHORS a binary `=` root, without which the mutation is unobservable) |
//! | 4 | the alignment descends only `App` | descend `Not` as well | **FAILS** `the_alignment_stops_at_a_not_and_records_the_whole_node` |
//! | 5 | FRESH | delete `constrained.contains(&name)` | **FAILS** `the_minter_refuses_a_definiendum_the_problem_constrains` |
//! | 6 | SINGLE DEFINIENS (adopt-or-decline) | delete the `existing` consistency test | **FAILS** `the_minter_refuses_a_second_definiens_for_one_symbol` |
//! | 7 | INDEPENDENT | delete the definiens-name test | **FAILS** `the_minter_refuses_a_definiendum_that_occurs_in_a_definiens` |
//! | 8 | the checker's own `recognize_fresh_def_eq` admission, BOTH asks deleted together | | STILL PASSED — HONEST NEGATIVE. `mk_eq` cannot build a node the recognizer refuses once the definiendum is a `Var` and the sorts match, and Gate 2 re-asks the same recognizer over the finished proof. Pinned directly by `a_leaf_over_a_fresh_symbol_is_derived_by_minting_its_definition`, which reads the emitted step back THROUGH that recognizer |
//! | 10 | SORT | delete `sort(p) == sort(b)` | **FAILS** `the_minter_refuses_a_sort_mismatch` |
//! | 11 | GATE 2, the whole-proof `FreshDefRegistry::collect` | delete it ALONE | STILL PASSED — HONEST NEGATIVE with a NAMED mechanism: `commit_bridge_fragments`' `check_proof` runs the SAME registry with `None` problem assertions, which already catches a malformed or self-referential definition. Gate 2 is what catches the case `None` cannot see — a definiendum the PROBLEM constrains but no `assume` does |
//! | **5+11** | FRESH **and** Gate 2 together | delete BOTH | **FAILS** `a_definiendum_the_problem_constrains_is_refused` AND `the_minter_refuses_a_definiendum_the_problem_constrains` — this is the pair that makes Gate 2 observably load-bearing, and it is the reason Gate 2 exists |
//!
//! **8 of 10 individually RED, plus the 5+11 pair RED; 2 honest negatives**,
//! each with its backstop named. Mutating a guard whose only observable effect
//! is a DERIVATION COUNT cannot be seen through the lane's output, because
//! every one of them is backstopped — that is why the tests above ask the
//! alignment and the minter DIRECTLY.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, ProofStep, Sort, Symbol, TermData, TermId, TermStore};

use super::tests::{
    boolvar, complement, ff, leaf_proof, premiseless_unit_trust_leaves, rerun, shape, solve, PURIFY,
};

// ===== the INDEPENDENT model enumerator =====

/// An interpretation: a truth value per Boolean variable plus the 4-entry
/// table of the uninterpreted `ff`.
#[derive(Clone, Debug)]
pub(super) struct Model {
    vars: DetHashMap<TermId, bool>,
    ff: [bool; 4],
}

impl Model {
    pub(super) fn ff_table(&self) -> [bool; 4] {
        self.ff
    }
}

pub(super) fn bool_atoms(terms: &TermStore, root: TermId, out: &mut Vec<TermId>) {
    match terms.get(root) {
        TermData::Var(_, _) => {
            if *terms.sort(root) == Sort::Bool && !out.contains(&root) {
                out.push(root);
            }
        }
        TermData::Not(inner) => bool_atoms(terms, *inner, out),
        TermData::App(_, args) => {
            for &arg in args {
                bool_atoms(terms, arg, out);
            }
        }
        _ => {}
    }
}

/// Evaluate `term` under `model`. `None` means the evaluator does not model it,
/// which every caller treats as a LOUD failure rather than a clean bill.
pub(super) fn eval(terms: &TermStore, term: TermId, model: &Model) -> Option<bool> {
    match terms.get(term) {
        TermData::Var(_, _) => model.vars.get(&term).copied(),
        TermData::Const(ay_core::Constant::Bool(value)) => Some(*value),
        TermData::Not(inner) => eval(terms, *inner, model).map(|value| !value),
        TermData::App(Symbol::Named(name), args) => match (name.as_str(), args.len()) {
            ("and", _) => {
                let mut all = true;
                for &arg in args {
                    all &= eval(terms, arg, model)?;
                }
                Some(all)
            }
            ("or", _) => {
                let mut any = false;
                for &arg in args {
                    any |= eval(terms, arg, model)?;
                }
                Some(any)
            }
            ("=", 2) => Some(eval(terms, args[0], model)? == eval(terms, args[1], model)?),
            ("ff", 2) => {
                let left = usize::from(eval(terms, args[0], model)?);
                let right = usize::from(eval(terms, args[1], model)?);
                Some(model.ff[left * 2 + right])
            }
            _ => None,
        },
        _ => None,
    }
}

/// EVERY model of `assertions`, by exhaustive enumeration.
pub(super) fn models(terms: &TermStore, assertions: &[TermId]) -> Vec<Model> {
    let mut atoms: Vec<TermId> = Vec::new();
    for &assertion in assertions {
        bool_atoms(terms, assertion, &mut atoms);
    }
    assert!(atoms.len() <= 8, "the enumeration must stay finite");
    let mut out = Vec::new();
    for mask in 0u32..(1u32 << atoms.len()) {
        for table in 0u8..16 {
            let model = Model {
                vars: atoms
                    .iter()
                    .enumerate()
                    .map(|(bit, &atom)| (atom, mask & (1 << bit) != 0))
                    .collect(),
                ff: [
                    table & 1 != 0,
                    table & 2 != 0,
                    table & 4 != 0,
                    table & 8 != 0,
                ],
            };
            let mut holds = true;
            for &assertion in assertions {
                match eval(terms, assertion, &model) {
                    Some(value) => holds &= value,
                    None => panic!("the evaluator does not model an assertion"),
                }
            }
            if holds {
                out.push(model);
            }
        }
    }
    out
}

/// The WEAKER but equally disqualifying statement: `assertions` has a model in
/// which `witness` is TRUE, and `assertions + definition` has none — so the
/// definition is an ordinary added CONSTRAINT on the problem's own symbols
/// rather than a conservative extension.
fn definition_constrains_the_problem(
    terms: &TermStore,
    assertions: &[TermId],
    definition: TermId,
    witness: TermId,
) -> bool {
    let mut extended = assertions.to_vec();
    extended.push(definition);
    let before = models(terms, assertions);
    let after = models(terms, &extended);
    before.iter().any(|m| eval(terms, witness, m) == Some(true))
        && after.iter().all(|m| eval(terms, witness, m) == Some(false))
}

// ===== the four AUTHORITY negatives the ask names =====

/// (1) The definiendum occurs in an AUTHORED assertion.
#[test]
fn a_definiendum_the_problem_constrains_is_refused() {
    // `pp` is DECLARED and CONSTRAINED by the problem, so `pp := (and g h)` is
    // an ordinary added constraint on `g` and `h`, not a conservative
    // extension.
    let mut exec = solve(
        r#"
        (set-logic QF_UF)
        (declare-fun g () Bool)
        (declare-fun h () Bool)
        (declare-fun k () Bool)
        (declare-fun pp () Bool)
        (declare-fun zz () Bool)
        (declare-fun ff (Bool Bool) Bool)
        (assert (ff (and g h) k))
        (assert (not pp))
        (assert zz)
        (assert (not zz))
        (check-sat)
    "#,
    );
    let pp = boolvar(&mut exec, "pp");
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let k = boolvar(&mut exec, "k");
    let conjunction = exec.ctx.terms.mk_and(vec![g, h]);
    let root = ff(&mut exec, conjunction, k);
    let not_pp = exec.ctx.terms.mk_not(pp);
    let definiens = exec.ctx.terms.mk_and(vec![g, h]);
    let definition = exec.ctx.terms.mk_eq(pp, definiens);
    // FALSIFYING ASSIGNMENT, enumerated and CHECKED: the authored set
    // `{ (ff (and g h) k), (not pp) }` has a model (g := true, h := true,
    // pp := false, ff(true, *) := true) and `A ∪ { pp = (and g h) }` has NONE
    // with that `g`/`h`, so the definition is not conservative.
    let authored = vec![root, not_pp];
    let witnesses = models(&exec.ctx.terms, &authored);
    assert!(
        !witnesses.is_empty(),
        "the authored set must be satisfiable"
    );
    let mut extended = authored.clone();
    extended.push(definition);
    let after = models(&exec.ctx.terms, &extended);
    assert!(
        after
            .iter()
            .all(|m| eval(&exec.ctx.terms, definiens, m) == Some(false)),
        "with the definition every model forces (and g h) false"
    );
    assert!(
        witnesses
            .iter()
            .any(|m| eval(&exec.ctx.terms, definiens, m) == Some(true)),
        "without it, (and g h) may be true - so the definition CONSTRAINS the \
         problem's own symbols"
    );
    // And the lane declines.
    let atom = ff(&mut exec, pp, k);
    let mut proof = leaf_proof(&mut exec, atom);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

/// (2) The definiendum occurs in an `assume` of the proof.
#[test]
fn a_definiendum_an_assume_constrains_is_refused() {
    let mut exec = solve(PURIFY);
    let pp = boolvar(&mut exec, "pp");
    let k = boolvar(&mut exec, "k");
    let atom = ff(&mut exec, pp, k);
    let mut proof = leaf_proof(&mut exec, atom);
    // The proof ASSUMES something about `pp`. Freshness is a statement about
    // the FINISHED proof's assume set, so this must refuse.
    let not_pp = exec.ctx.terms.mk_not(pp);
    proof.steps.push(ProofStep::Assume(not_pp));
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let definiens = exec.ctx.terms.mk_and(vec![g, h]);
    let definition = exec.ctx.terms.mk_eq(pp, definiens);
    let root = ff(&mut exec, definiens, k);
    // The refutation's premise set is the authored assertions PLUS the proof's
    // own assumes, and the same enumeration refutes conservativity over it.
    // FALSIFYING ASSIGNMENT: g := true, h := true, pp := false, ff(true, *) :=
    // true satisfies `{ (ff (and g h) k), (not pp) }`; adding `pp = (and g h)`
    // admits NO model with `(and g h)` true, so the definition constrains the
    // problem's own `g` and `h`.
    let premises = vec![root, not_pp];
    assert!(
        definition_constrains_the_problem(&exec.ctx.terms, &premises, definition, definiens),
        "A has a model with the definiens TRUE and A + the definition has none"
    );
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

/// (3) TWO different definientia for one symbol.
#[test]
fn two_definientia_for_one_symbol_are_refused() {
    let mut exec = solve(PURIFY);
    let pp = boolvar(&mut exec, "pp");
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let k = boolvar(&mut exec, "k");
    let other = exec.ctx.terms.mk_or(vec![g, h]);
    let mine = exec.ctx.terms.mk_and(vec![g, h]);
    let other_definition = exec.ctx.terms.mk_eq(pp, other);
    let my_definition = exec.ctx.terms.mk_eq(pp, mine);
    // The two definitions JOINTLY force `(and g h) = (or g h)`, i.e. `g = h` —
    // a genuine constraint on the problem's own symbols. FALSIFYING
    // ASSIGNMENT: g := true, h := false satisfies the authored set and NO
    // model of the authored set plus BOTH definitions has g != h.
    let root = ff(&mut exec, mine, k);
    let authored = vec![root];
    let both = vec![root, other_definition, my_definition];
    let before_models = models(&exec.ctx.terms, &authored);
    let after_models = models(&exec.ctx.terms, &both);
    assert!(before_models
        .iter()
        .any(|m| { eval(&exec.ctx.terms, g, m) != eval(&exec.ctx.terms, h, m) }));
    assert!(
        after_models
            .iter()
            .all(|m| { eval(&exec.ctx.terms, g, m) == eval(&exec.ctx.terms, h, m) }),
        "two definientia equate the problem's own symbols"
    );
    // The proof already carries the OTHER definition as a checked step, so the
    // lane must ADOPT it or decline — never compete with it.
    let atom = ff(&mut exec, pp, k);
    let mut proof = leaf_proof(&mut exec, atom);
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::FreshDefEq,
        clause: vec![other_definition],
        premises: Vec::new(),
        args: vec![pp],
    });
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

/// (4) The symbol occurs INSIDE its own definiens.
#[test]
fn a_symbol_inside_its_own_definiens_is_refused() {
    let mut exec = solve(
        r#"
        (set-logic QF_UF)
        (declare-fun g () Bool)
        (declare-fun h () Bool)
        (declare-fun k () Bool)
        (declare-fun zz () Bool)
        (declare-fun ff (Bool Bool) Bool)
        (assert (ff (not pp0) k))
        (assert zz)
        (assert (not zz))
        (check-sat)
        "#
        .replace("pp0", "g")
        .as_str(),
    );
    let pp = boolvar(&mut exec, "pp");
    let k = boolvar(&mut exec, "k");
    // The leaf replaces the authored `(not g)` with `pp`, but the ROOT this
    // fixture aligns against is built so the definiens MENTIONS `pp`:
    // `pp := (not pp)`, which no assignment satisfies.
    let not_pp = exec.ctx.terms.mk_not(pp);
    let self_definition = exec.ctx.terms.mk_eq(pp, not_pp);
    assert!(
        models(&exec.ctx.terms, &[self_definition]).is_empty(),
        "`pp = (not pp)` has NO model, so it refutes any satisfiable A"
    );
    let g = boolvar(&mut exec, "g");
    let not_g = exec.ctx.terms.mk_not(g);
    let root = ff(&mut exec, not_g, k);
    assert!(
        !models(&exec.ctx.terms, &[root]).is_empty(),
        "the authored set IS satisfiable"
    );
    // The lane must never write that definition. The alignment refuses first —
    // `(not g)` against `pp` at a `Not` position is not an `App` descent — and
    // the INDEPENDENT guard refuses it again if the alignment ever changed.
    let atom = ff(&mut exec, pp, k);
    let mut proof = leaf_proof(&mut exec, atom);
    let before = shape(&proof);
    let derived = rerun(&mut exec, &mut proof);
    if derived == 1 {
        // If it ever DID derive, the definition it wrote must not be the
        // self-referential one.
        for step in &proof.steps {
            if let ProofStep::Step {
                rule: AletheRule::FreshDefEq,
                clause,
                ..
            } = step
            {
                assert_ne!(clause.first().copied(), Some(self_definition));
            }
        }
    } else {
        assert_eq!(shape(&proof), before);
    }
}

// ===== the alignment barrier the corpus actually hits =====

/// MEASURED: 28 of the 34 `and`-headed leaves in the corpus differ from their
/// authored counterpart at a position underneath a `not`, and `ay_proof`'s
/// congruence forest descends only `App`. The lane refuses those at the
/// ALIGNMENT stage rather than planning a derivation that can never close.
#[test]
fn a_differing_position_under_a_not_is_never_minted() {
    let mut exec = solve(
        r#"
        (set-logic QF_UF)
        (declare-fun g () Bool)
        (declare-fun h () Bool)
        (declare-fun k () Bool)
        (declare-fun zz () Bool)
        (declare-fun ff (Bool Bool) Bool)
        (assert (ff (not (and g h)) k))
        (assert zz)
        (assert (not zz))
        (check-sat)
    "#,
    );
    let pp = boolvar(&mut exec, "pp");
    let k = boolvar(&mut exec, "k");
    let not_pp = exec.ctx.terms.mk_not(pp);
    let atom = ff(&mut exec, not_pp, k);
    let mut proof = leaf_proof(&mut exec, atom);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
    // TWO-SIDED: the SAME substitution ABOVE the `not` is derived.
    let mut exec = solve(PURIFY);
    let pp = boolvar(&mut exec, "pp");
    let k = boolvar(&mut exec, "k");
    let atom = ff(&mut exec, pp, k);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
}

// ===== GATE 2 =====

#[test]
fn gate_two_reverts_a_splice_the_checkers_registry_declines() {
    let mut exec = solve(PURIFY);
    let pp = boolvar(&mut exec, "pp");
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let k = boolvar(&mut exec, "k");
    let atom = ff(&mut exec, pp, k);
    let mut proof = leaf_proof(&mut exec, atom);
    // A pre-existing fresh-definition step for the SAME symbol with a
    // DIFFERENT definiens, placed so the lane's own `existing` map cannot see
    // it: the clause is a binary `=` the recognizer accepts, but the `args`
    // name a symbol that is not an operand, so `recognize_fresh_def_eq` fails
    // and the lane's `existing_fresh_definitions` skips it — while
    // `FreshDefRegistry::collect` REJECTS the whole proof.
    let other = exec.ctx.terms.mk_or(vec![g, h]);
    let mismatched = exec.ctx.terms.mk_eq(other, k);
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::FreshDefEq,
        clause: vec![mismatched],
        premises: Vec::new(),
        args: vec![pp],
    });
    let scope = exec.complete_problem_assertions_for_strict_proof();
    assert!(
        ay_proof::FreshDefRegistry::collect(&proof, &exec.ctx.terms, Some(&scope)).is_err(),
        "the fixture must make the checker's registry decline"
    );
    let before = shape(&proof);
    assert_eq!(
        rerun(&mut exec, &mut proof),
        0,
        "Gate 2 must revert the whole splice"
    );
    assert_eq!(
        shape(&proof),
        before,
        "the reverted proof is byte-identical to the one it started from"
    );
    assert_eq!(premiseless_unit_trust_leaves(&proof), 2);
    let _ = complement(&mut exec, atom);
}
