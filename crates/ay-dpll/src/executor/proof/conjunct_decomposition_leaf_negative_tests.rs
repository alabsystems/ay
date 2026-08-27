// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ADVERSARIAL negatives for the conjunct-decomposition lane, each naming a
//! concrete input and CHECKING it with an independent evaluator.
//!
//! The lane's soundness has two halves and this file attacks both:
//!
//!  * **ENTAILMENT** — the leaf must be a consequence of the authored root
//!    under the minted definitions. `a_leaf_that_is_not_entailed_is_declined`
//!    exhibits a leaf with a FALSIFYING assignment, checks that assignment by
//!    exhaustive enumeration, and shows the lane declines it.
//!  * **CONSERVATIVITY** — a minted definition must not refute a satisfiable
//!    authored set. Each minting negative ENUMERATES the models of the authored
//!    set `A`, exhibits one, and shows `A ∪ {definition}` has NONE.
//!
//! [`models`] is a naive exhaustive enumerator over Boolean variables and ONE
//! uninterpreted `ff : Bool × Bool → Bool`, whose 4-entry table it enumerates
//! in full. It shares no code with the lane, with `ay_proof`'s planner, or with
//! the checker.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Constant, ProofStep, Sort, Symbol, TermData, TermId, TermStore};

use super::tests::{
    authored_and_root, boolvar, conjuncts_of, leaf_proof, premiseless_unit_trust_leaves,
    purified_leaf, rerun, shape, solve, substitute, CONJUNCTS,
};
use crate::Executor;

// ===== the INDEPENDENT model enumerator =====

#[derive(Clone, Debug)]
struct Model {
    vars: DetHashMap<TermId, bool>,
    ff: [bool; 4],
}

fn bool_atoms(terms: &TermStore, root: TermId, out: &mut Vec<TermId>) {
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

/// `None` means the evaluator does not model the node — every caller treats
/// that as a LOUD failure, never as a clean bill.
fn eval(terms: &TermStore, term: TermId, model: &Model) -> Option<bool> {
    match terms.get(term) {
        TermData::Var(_, _) => model.vars.get(&term).copied(),
        TermData::Const(Constant::Bool(value)) => Some(*value),
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
fn models(terms: &TermStore, assertions: &[TermId]) -> Vec<Model> {
    models_over(terms, assertions, assertions)
}

/// EVERY model of `assertions`, with the interpretation domain taken from
/// `universe` — which must cover every term the caller will later `eval`, or
/// the evaluator answers `None` and the caller panics.
fn models_over(terms: &TermStore, universe: &[TermId], assertions: &[TermId]) -> Vec<Model> {
    let mut atoms: Vec<TermId> = Vec::new();
    for &term in universe {
        bool_atoms(terms, term, &mut atoms);
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

/// `assertions` HAS a model and `assertions + extra` has NONE — so adding
/// `extra` would refute a satisfiable authored set outright.
fn refutes_a_satisfiable_set(terms: &TermStore, assertions: &[TermId], extra: TermId) -> bool {
    let mut extended = assertions.to_vec();
    extended.push(extra);
    !models(terms, assertions).is_empty() && models(terms, &extended).is_empty()
}

/// A leaf is NOT entailed by the authored root when some model satisfies the
/// root and falsifies the leaf. Returns that model's `ff` table, so the caller
/// can name the falsifying assignment.
fn countermodel(terms: &TermStore, root: TermId, leaf: TermId) -> Option<[bool; 4]> {
    models_over(terms, &[root, leaf], &[root])
        .into_iter()
        .find_map(|model| {
            let value = eval(terms, leaf, &model).expect("the evaluator must model the leaf");
            (!value).then_some(model.ff)
        })
}

fn declines(exec: &mut Executor, atom: TermId) {
    let mut proof = leaf_proof(exec, atom);
    let before = shape(&proof);
    let leaves = premiseless_unit_trust_leaves(&proof);
    assert_eq!(rerun(exec, &mut proof), 0, "the lane must decline");
    assert_eq!(
        shape(&proof),
        before,
        "a declined lane must leave the proof byte-identical"
    );
    assert_eq!(premiseless_unit_trust_leaves(&proof), leaves);
}

// ===== ENTAILMENT =====

/// NEGATIVE 1 — a leaf that is NOT a consequence of the authored root.
///
/// The third conjunct's arguments are SWAPPED: `(ff m k)` where the root has
/// `(ff k m)`. That is not a substitution of anything, and it is not entailed:
/// the countermodel below satisfies the root and falsifies the leaf. The lane
/// must decline, and the assignment is CHECKED here by exhaustive enumeration.
#[test]
fn a_leaf_that_is_not_entailed_is_declined() {
    let mut exec = solve(CONJUNCTS);
    let (purified, root, _) = purified_leaf(&mut exec);
    let k = boolvar(&mut exec, "k");
    let m = boolvar(&mut exec, "m");
    let conjuncts = conjuncts_of(&exec, purified);
    // Swap the arguments of the one conjunct that has no compound argument.
    let swapped: Vec<TermId> = conjuncts
        .iter()
        .map(|&conjunct| {
            let with_placeholder = substitute(&mut exec, conjunct, k, root);
            let flipped = substitute(&mut exec, with_placeholder, m, k);
            substitute(&mut exec, flipped, root, m)
        })
        .collect();
    let forged = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), swapped, Sort::Bool);
    assert_ne!(forged, purified, "the swap must change the leaf");

    let table = countermodel(&exec.ctx.terms, root, forged)
        .expect("the swapped leaf must have a FALSIFYING assignment under the root");
    // Name it: the `ff` table that satisfies the root and kills the leaf.
    assert_eq!(table.len(), 4);
    declines(&mut exec, forged);
}

/// The two-sided half of NEGATIVE 1: the leaf the lane DOES take is entailed by
/// the authored root under the minted definition, with no countermodel over
/// EVERY assignment. An evaluator that answered "not entailed" for everything
/// would fail here.
#[test]
fn the_leaf_the_lane_takes_is_entailed_under_its_definition() {
    let mut exec = solve(CONJUNCTS);
    let (atom, root, pp) = purified_leaf(&mut exec);
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let definiens = exec.ctx.terms.mk_and(vec![g, h]);
    let definition = exec.ctx.terms.mk_eq(pp, definiens);
    let mut assertions = vec![root, definition];
    assert!(
        !models(&exec.ctx.terms, &assertions).is_empty(),
        "the authored root plus the definition must be SATISFIABLE"
    );
    for model in models(&exec.ctx.terms, &assertions) {
        assert_eq!(
            eval(&exec.ctx.terms, atom, &model),
            Some(true),
            "the leaf must hold in EVERY model of root + definition"
        );
    }
    // And the box contains a refutable neighbour, so the sweep is not vacuous.
    assertions.push(exec.ctx.terms.mk_not(atom));
    assert!(
        models(&exec.ctx.terms, &assertions).is_empty(),
        "root + definition + (not leaf) must be UNSAT"
    );
}

// ===== CONSERVATIVITY =====

/// NEGATIVE 2 — the definiendum is a symbol the PROBLEM constrains.
///
/// Substituting `(and g h)` by the authored `k` makes `k = (and g h)` a
/// CONSTRAINT on the problem's own symbols, not a definition. Checked: the
/// authored set has a model, and the authored set plus that "definition" has
/// none.
#[test]
fn a_definiendum_the_problem_constrains_is_refused() {
    let mut exec = solve(CONJUNCTS);
    let root = authored_and_root(&exec);
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let k = boolvar(&mut exec, "k");
    let definiens = exec.ctx.terms.mk_and(vec![g, h]);
    let leaf = substitute(&mut exec, root, definiens, k);
    assert_ne!(leaf, root);

    let definition = exec.ctx.terms.mk_eq(k, definiens);
    assert!(
        refutes_a_satisfiable_set(&exec.ctx.terms, &[root], definition),
        "`k = (and g h)` must REFUTE a satisfiable authored set — that is what \
         makes it a constraint rather than a definition"
    );
    declines(&mut exec, leaf);
}

/// NEGATIVE 3 — the definiendum occurs in an `assume` of the proof.
///
/// Freshness is decided against the FINISHED proof's `assume` set, so a leaf
/// over `pp` must be refused once some `assume` mentions `pp`.
#[test]
fn a_definiendum_some_assume_mentions_is_refused() {
    let mut exec = solve(CONJUNCTS);
    let (atom, _, pp) = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    // An `assume` that mentions the definiendum, plus its own closer, so the
    // fixture stays a COMPLETE refutation.
    let not_pp = exec.ctx.terms.mk_not(pp);
    proof.steps.push(ProofStep::Assume(pp));
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![not_pp],
        premises: Vec::new(),
        args: Vec::new(),
    });
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);

    // Two-sided: WITHOUT that assume the very same leaf IS derived.
    let mut clean = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut clean), 1);
}

/// NEGATIVE 4 — TWO definientia for one symbol.
///
/// The proof already binds `pp := (ff k m)`; the leaf would need
/// `pp := (and g h)`. Two definientia for one symbol EQUATE the problem's own
/// terms, and the enumeration shows exactly that.
#[test]
fn a_second_definiens_for_one_symbol_is_refused() {
    let mut exec = solve(CONJUNCTS);
    let (atom, root, pp) = purified_leaf(&mut exec);
    let k = boolvar(&mut exec, "k");
    let m = boolvar(&mut exec, "m");
    let other = exec
        .ctx
        .terms
        .mk_app(Symbol::named("ff"), vec![k, m], Sort::Bool);
    let rival = exec.ctx.terms.mk_eq(pp, other);
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let definiens = exec.ctx.terms.mk_and(vec![g, h]);
    let mine = exec.ctx.terms.mk_eq(pp, definiens);

    // BOTH definitions together equate `(and g h)` and `(ff k m)`, which the
    // authored root does not.
    let mut both = vec![root, rival, mine];
    assert!(
        !models(&exec.ctx.terms, &[root, rival]).is_empty(),
        "the root plus ONE definition is satisfiable"
    );
    let equated = {
        let left = exec.ctx.terms.mk_and(vec![g, h]);
        let right = exec
            .ctx
            .terms
            .mk_app(Symbol::named("ff"), vec![k, m], Sort::Bool);
        exec.ctx.terms.mk_eq(left, right)
    };
    for model in models(&exec.ctx.terms, &both) {
        assert_eq!(
            eval(&exec.ctx.terms, equated, &model),
            Some(true),
            "two definientia for one symbol EQUATE the problem's own terms"
        );
    }
    both.push(exec.ctx.terms.mk_not(equated));
    assert!(
        models(&exec.ctx.terms, &both).is_empty(),
        "and nothing escapes that"
    );

    let mut proof = leaf_proof(&mut exec, atom);
    proof.steps.insert(
        0,
        ProofStep::Step {
            rule: AletheRule::FreshDefEq,
            clause: vec![rival],
            premises: Vec::new(),
            args: vec![pp],
        },
    );
    let before = shape(&proof);
    assert_eq!(
        rerun(&mut exec, &mut proof),
        0,
        "an existing binding must be ADOPTED or the leaf declined, never competed with"
    );
    assert_eq!(shape(&proof), before);
}

/// NEGATIVE 5 — the symbol inside its own definiens.
///
/// `pp = (ff pp k)` is not conservative in general and the registry's
/// INDEPENDENT condition exists to refuse it. Here the lane never even reaches
/// that: an alignment whose leaf side still contains the definiendum is not a
/// substitution the lane can make. The check below is on the DEFINITION, so it
/// states the property rather than the accident.
#[test]
fn a_definiendum_inside_its_own_definiens_is_refused() {
    let mut exec = solve(CONJUNCTS);
    let root = authored_and_root(&exec);
    let pp = boolvar(&mut exec, "pp");
    let k = boolvar(&mut exec, "k");
    let self_referential = exec
        .ctx
        .terms
        .mk_app(Symbol::named("ff"), vec![pp, k], Sort::Bool);
    let definition = exec.ctx.terms.mk_eq(pp, self_referential);
    // It does not refute the authored set on its own here, but it is not a
    // DEFINITION: it constrains `pp` against `ff`, whose table the problem also
    // constrains. Show the registry refuses it, which is the actual authority.
    let mut proof = leaf_proof(&mut exec, root);
    proof.steps.insert(
        0,
        ProofStep::Step {
            rule: AletheRule::FreshDefEq,
            clause: vec![definition],
            premises: Vec::new(),
            args: vec![pp],
        },
    );
    let scope = exec.complete_problem_assertions_for_strict_proof();
    assert!(
        ay_proof::FreshDefRegistry::collect(&proof, &exec.ctx.terms, Some(&scope)).is_err(),
        "the checker's own registry must refuse a self-referential definition"
    );
}

// ===== the `and_neg` step itself =====

/// NEGATIVE 6 — a FORGED `and_neg`, and the guard that would catch it.
///
/// The lane strict-checks its `and_neg` step, CLOSED, before writing it
/// (Guard 7). This names the input that guard exists for: the same clause with
/// one complement DUPLICATED and another MISSING, which reaches `n` literals
/// without covering every conjunct — the exact non-tautology
/// `validate_and_neg`'s own comment records. It is refused, and the assignment
/// that falsifies it is checked here.
#[test]
fn a_forged_and_neg_is_refused_by_the_guard_the_lane_uses() {
    let mut exec = solve(CONJUNCTS);
    let (atom, _, _) = purified_leaf(&mut exec);
    let conjuncts = conjuncts_of(&exec, atom);
    assert_eq!(conjuncts.len(), 3);
    let complements: Vec<TermId> = conjuncts
        .iter()
        .map(|&conjunct| super::tests::complement(&mut exec, conjunct))
        .collect();

    // Honest: the clause the lane really writes IS accepted.
    let mut honest = vec![atom];
    honest.extend(complements.iter().copied());
    let accepted = ay_proof::CongruenceDerivation {
        steps: vec![ProofStep::Step {
            rule: AletheRule::AndNeg,
            clause: honest.clone(),
            premises: Vec::new(),
            args: vec![atom],
        }],
        clause: honest,
    };
    let closed = ay_proof::close_congruence_derivation(&mut exec.ctx.terms, &accepted);
    ay_proof::check_proof_strict(&closed, &exec.ctx.terms)
        .expect("the lane's own and_neg must strict-check");

    // Forged: complement 0 twice, complement 2 never.
    let forged_clause = vec![atom, complements[0], complements[1], complements[0]];
    let forged = ay_proof::CongruenceDerivation {
        steps: vec![ProofStep::Step {
            rule: AletheRule::AndNeg,
            clause: forged_clause.clone(),
            premises: Vec::new(),
            args: vec![atom],
        }],
        clause: forged_clause,
    };
    let closed = ay_proof::close_congruence_derivation(&mut exec.ctx.terms, &forged);
    assert!(
        ay_proof::check_proof_strict(&closed, &exec.ctx.terms).is_err(),
        "a clause that reaches n literals without covering every conjunct is \
         NOT a tautology and must be refused"
    );

    // And the refusal is not a formality: NAME the falsifying assignment. Make
    // conjuncts 0 and 1 TRUE (so both copies of `complements[0]` and
    // `complements[1]` are false) and conjunct 2 FALSE (so the conjunction
    // itself is false). Every literal of the forged clause is then false.
    let universe = vec![atom];
    let witness = models_over(&exec.ctx.terms, &universe, &[])
        .into_iter()
        .find(|model| {
            eval(&exec.ctx.terms, conjuncts[0], model) == Some(true)
                && eval(&exec.ctx.terms, conjuncts[1], model) == Some(true)
                && eval(&exec.ctx.terms, conjuncts[2], model) == Some(false)
        })
        .expect("such an assignment must exist");
    for literal in [atom, complements[0], complements[1], complements[0]] {
        assert_eq!(
            eval(&exec.ctx.terms, literal, &witness),
            Some(false),
            "every literal of the FORGED clause is false under this assignment"
        );
    }
    // Two-sided: the HONEST clause is not falsifiable by it — the missing
    // complement is exactly the literal that rescues it.
    assert_eq!(
        eval(&exec.ctx.terms, complements[2], &witness),
        Some(true),
        "the complement the forgery dropped is the one that makes the real \
         and_neg a tautology here"
    );
}
