// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #closer-derived-leaf-head — the trust closer must not assert a head over
//! DERIVED leaves.
//!
//! `derive_empty_via_trust_lemma` has two leaf sources. Over the proof's
//! ASSUME-family leaves the head is the solve's own UNSAT verdict restated —
//! unproved, hence `Generic`, but not false. Over unit `TheoryLemma`
//! CONCLUSIONS it is neither: those are DERIVED facts the same proof asserts as
//! theory-valid, so their conjunction holds in every model and the head — their
//! joint negation — is FALSE in every model.
//!
//! Measured on `benchmarks/smt/QF_AX/write_write_overwrite.smt2` before the
//! fix — one closer invocation over derived leaves, head
//!
//! ```text
//! (cl (not (= (select (store a i v2) j) (select a j)))
//!     (not (= (select a j) (select (store a i v1) j))))
//! ```
//!
//! refuted by an independent bounded array model at `i = j`, `v1 = v2 = e`,
//! `a[j] = e`. The two leaves are `row2_unit_distinct_indices` instances the
//! AUFLIA array fixpoint records WITHOUT the `i != j` premise that licenses
//! them (`theories::euf::array_row::add_array_row_clauses_with_cap`), and the
//! authored `(assert (not (= i j)))` is not in the proof at all.
//!
//! What the closer records instead is a terminal empty-clause `trust` step: the
//! solve's own UNSAT claim, stated as an obligation, asserting nothing about
//! arrays. Corpus-wide over `benchmarks/**/*.smt2` this route fires 51 times in
//! 3 files; after the fix 49 of those refuse and 2 (`bug3_enum_card_ite_
//! distinct.smt2`) close through the strict-checkable `false` rule instead,
//! with ZERO verdict differences against two pristine control runs.
//!
//! The evaluator below re-derives the McCarthy semantics from the term
//! structure and shares no code with the closer, the checker, or `ay-proof`'s
//! array validators. The EUF congruence evaluators cannot serve: they read
//! `select`/`store` as uninterpreted, under which nothing here is decidable.

use ay_core::{
    AletheRule, ArraySort, Proof, ProofStep, Sort, Symbol, TermData, TermId, TermStore,
    TheoryLemmaKind,
};
use ay_proof::{check_proof_partial, check_proof_strict, export_alethe};

// ===== fixture helpers =====

fn index_sort() -> Sort {
    Sort::Uninterpreted("Index".to_string())
}

fn element_sort() -> Sort {
    Sort::Uninterpreted("Element".to_string())
}

fn array_sort() -> Sort {
    Sort::Array(Box::new(ArraySort::new(index_sort(), element_sort())))
}

/// A RAW `(store a i v)` / `(select a i)`: the folding builders would collapse
/// exactly the terms these fixtures are about.
fn store(terms: &mut TermStore, base: TermId, at: TermId, value: TermId) -> TermId {
    terms.mk_app(Symbol::named("store"), vec![base, at, value], array_sort())
}

fn select(terms: &mut TermStore, base: TermId, at: TermId) -> TermId {
    terms.mk_app(Symbol::named("select"), vec![base, at], element_sort())
}

fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

fn closer(terms: &mut TermStore, proof: &mut Proof) {
    crate::executor::proof_resolution::empty_clause::derive_empty_via_trust_lemma(terms, proof);
}

fn theory_lemma_heads(proof: &Proof) -> Vec<(TheoryLemmaKind, usize)> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma { kind, clause, .. } => Some((*kind, clause.len())),
            _ => None,
        })
        .collect()
}

fn derives_empty_clause(proof: &Proof) -> bool {
    proof
        .steps
        .iter()
        .rev()
        .find_map(|step| match step {
            ProofStep::Step { clause, .. } => Some(clause.is_empty()),
            ProofStep::TheoryLemma { clause, .. } => Some(clause.is_empty()),
            ProofStep::Assume(_) => None,
            _ => None,
        })
        .unwrap_or(false)
}

// ===== the INDEPENDENT bounded array model =====

/// A value over a two-index, two-element carrier. An array is any total map
/// from the index carrier to the element carrier.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Value {
    Index(usize),
    Element(usize),
    Array(Vec<usize>),
}

fn evaluate(terms: &TermStore, term: TermId, binding: &[(TermId, Value)]) -> Option<Value> {
    if let Some((_, value)) = binding.iter().find(|(id, _)| *id == term) {
        return Some(value.clone());
    }
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "select" && args.len() == 2 => {
            let Value::Array(cells) = evaluate(terms, args[0], binding)? else {
                return None;
            };
            let Value::Index(at) = evaluate(terms, args[1], binding)? else {
                return None;
            };
            cells.get(at).copied().map(Value::Element)
        }
        TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
            let Value::Array(mut cells) = evaluate(terms, args[0], binding)? else {
                return None;
            };
            let Value::Index(at) = evaluate(terms, args[1], binding)? else {
                return None;
            };
            let Value::Element(value) = evaluate(terms, args[2], binding)? else {
                return None;
            };
            *cells.get_mut(at)? = value;
            Some(Value::Array(cells))
        }
        _ => None,
    }
}

/// Whether `literal` HOLDS under `binding`; `None` when the model cannot decide
/// it, which is a failure to refute and never evidence of validity.
fn holds(terms: &TermStore, literal: TermId, binding: &[(TermId, Value)]) -> Option<bool> {
    match terms.get(literal) {
        TermData::Not(inner) => holds(terms, *inner, binding).map(|value| !value),
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some(evaluate(terms, args[0], binding)? == evaluate(terms, args[1], binding)?)
        }
        _ => None,
    }
}

// ===== the measured fixture =====

struct WriteWriteOverwrite {
    terms: TermStore,
    proof: Proof,
    /// The head the closer used to assert: the negation of both leaves.
    head: Vec<TermId>,
    a: TermId,
    i: TermId,
    j: TermId,
    v1: TermId,
    v2: TermId,
}

/// The exact proof the AUFLIA array fixpoint hands the closer on
/// `write_write_overwrite.smt2`: two unit `Generic` ROW2 lemmas, NO `Assume`.
fn write_write_overwrite() -> WriteWriteOverwrite {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", array_sort());
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let v1 = terms.mk_var("v1", element_sort());
    let v2 = terms.mk_var("v2", element_sort());

    let store_v2 = store(&mut terms, a, i, v2);
    let store_v1 = store(&mut terms, a, i, v1);
    let read_store_v2 = select(&mut terms, store_v2, j);
    let read_store_v1 = select(&mut terms, store_v1, j);
    let read_base = select(&mut terms, a, j);
    let leaf_one = eq(&mut terms, read_store_v2, read_base);
    let leaf_two = eq(&mut terms, read_base, read_store_v1);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("UNKNOWN", vec![leaf_one], TheoryLemmaKind::Generic);
    proof.add_theory_lemma_with_kind("UNKNOWN", vec![leaf_two], TheoryLemmaKind::Generic);

    let head = vec![terms.mk_not_raw(leaf_one), terms.mk_not_raw(leaf_two)];
    WriteWriteOverwrite {
        terms,
        proof,
        head,
        a,
        i,
        j,
        v1,
        v2,
    }
}

/// THE COMPLETE REFUTATION. `i = j = idx0`, `v1 = v2 = elt0`, `a = [elt0,
/// elt1]` so `a[j] = elt0`: BOTH head literals evaluate to false, so the clause
/// has no true literal and is not a theorem.
///
/// The base array is deliberately NON-CONSTANT, so the witness is a real
/// two-value model rather than the degenerate one-element carrier. The
/// load-bearing part of the assignment is `v1 = v2 = a[j]` — see the
/// sensitivity control below.
#[test]
fn the_write_write_overwrite_head_is_false_at_i_equals_j_with_v1_equals_v2() {
    let fixture = write_write_overwrite();
    let binding = vec![
        (fixture.a, Value::Array(vec![0, 1])),
        (fixture.i, Value::Index(0)),
        (fixture.j, Value::Index(0)),
        (fixture.v1, Value::Element(0)),
        (fixture.v2, Value::Element(0)),
    ];
    for (position, &literal) in fixture.head.iter().enumerate() {
        assert_eq!(
            holds(&fixture.terms, literal, &binding),
            Some(false),
            "head literal {position} must be FALSE at i = j, v1 = v2 = a[j]: {}",
            ay_proof::format_term_alethe(&fixture.terms, literal)
        );
    }
}

/// SENSITIVITY CONTROL: move ONE stored value off `a[j]` and the head acquires
/// a true literal, so the assignment above is about `v1 = v2 = a[j]` and not
/// about an accidentally degenerate carrier.
#[test]
fn the_write_write_overwrite_head_has_a_true_literal_once_v2_leaves_a_at_j() {
    let fixture = write_write_overwrite();
    let binding = vec![
        (fixture.a, Value::Array(vec![0, 1])),
        (fixture.i, Value::Index(0)),
        (fixture.j, Value::Index(0)),
        (fixture.v1, Value::Element(0)),
        (fixture.v2, Value::Element(1)),
    ];
    assert!(
        fixture
            .head
            .iter()
            .any(|&literal| holds(&fixture.terms, literal, &binding) == Some(true)),
        "the head must acquire a TRUE literal once v2 leaves a[j]"
    );
}

/// POSITIVE CONTROL for the evaluator above: it must NOT falsify a genuine
/// array validity, or its `false` verdicts would be worthless.
#[test]
fn the_bounded_array_model_upholds_a_genuine_row1_validity() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", array_sort());
    let i = terms.mk_var("i", index_sort());
    let v = terms.mk_var("v", element_sort());
    let stored = store(&mut terms, a, i, v);
    let read = select(&mut terms, stored, i);
    let row1 = eq(&mut terms, read, v);

    let mut refuted = false;
    for cell0 in 0..2 {
        for cell1 in 0..2 {
            for at in 0..2 {
                for value in 0..2 {
                    let binding = vec![
                        (a, Value::Array(vec![cell0, cell1])),
                        (i, Value::Index(at)),
                        (v, Value::Element(value)),
                    ];
                    let decided =
                        holds(&terms, row1, &binding).expect("the model must decide ROW1");
                    refuted |= !decided;
                }
            }
        }
    }
    assert!(
        !refuted,
        "the bounded array model falsified the ROW1 validity — the evaluator is broken \
         and every negative in this file would be vacuous"
    );
}

/// FAIL CLOSED. The closer must refuse the false head and record the honest
/// shape instead: one terminal empty-clause `trust` step, which asserts nothing
/// about arrays at all.
#[test]
fn closer_refuses_an_unvalidated_head_over_derived_leaves() {
    let mut fixture = write_write_overwrite();
    closer(&mut fixture.terms, &mut fixture.proof);

    assert_eq!(
        theory_lemma_heads(&fixture.proof),
        vec![(TheoryLemmaKind::Generic, 1), (TheoryLemmaKind::Generic, 1),],
        "no head may be recorded: only the two pre-existing unit leaves remain, got: {}",
        export_alethe(&fixture.proof, &fixture.terms)
    );
    // The refutable clause must not appear ANYWHERE in the artifact.
    for step in &fixture.proof.steps {
        let clause: &[TermId] = match step {
            ProofStep::TheoryLemma { clause, .. } | ProofStep::Step { clause, .. } => clause,
            _ => continue,
        };
        assert_ne!(
            clause,
            fixture.head.as_slice(),
            "the refuted head must not enter the proof under any rule"
        );
    }
    assert!(
        matches!(
            fixture.proof.steps.last(),
            Some(ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            }) if clause.is_empty() && premises.is_empty()
        ),
        "the honest closure is a terminal empty-clause trust step, got: {}",
        export_alethe(&fixture.proof, &fixture.terms)
    );
    assert!(
        check_proof_strict(&fixture.proof, &fixture.terms).is_err(),
        "the strict checker must still refuse this proof"
    );
    // And the deferred lane must see the empty clause as an OBLIGATION, not as
    // a derivation: `discharge_trust_clause` re-decides the authored problem
    // for it, so nothing is accepted on this proof's own say-so.
    let collected = ay_proof::check_proof_collecting_trust(&fixture.proof, &fixture.terms)
        .expect("every non-trust step of the honest closure must still validate");
    assert!(
        collected.iter().any(|(_, clause)| clause.is_empty()),
        "the terminal trust step must be collected as an empty-clause obligation"
    );
}

/// The refused head, printed exactly as the finding recorded it. Pins the
/// subject of this file against a term-builder or formatter drift.
#[test]
fn the_refused_head_prints_exactly_as_the_finding_recorded_it() {
    let fixture = write_write_overwrite();
    let rendered: Vec<String> = fixture
        .head
        .iter()
        .map(|&literal| ay_proof::format_term_alethe(&fixture.terms, literal))
        .collect();
    assert_eq!(
        format!("(cl {})", rendered.join(" ")),
        "(cl (not (= (select (store a i v2) j) (select a j))) \
         (not (= (select a j) (select (store a i v1) j))))"
    );
}

/// The escape hatch is real and still fires: a head over DERIVED leaves that
/// the CHECKER'S OWN recognizer re-derives from the clause alone is not a
/// trust claim, so it is emitted and the whole proof strict-checks.
#[test]
fn closer_still_emits_a_derived_leaf_head_the_checker_validates() {
    let mut terms = TermStore::new();
    let int_array = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_var("a", int_array.clone());
    let i0 = terms.mk_var("i0", Sort::Int);
    let i1 = terms.mk_var("i1", Sort::Int);
    let v0 = terms.mk_var("v0", Sort::Int);
    let v1 = terms.mk_var("v1", Sort::Int);
    let mk_store = |terms: &mut TermStore, base, index, value| {
        terms.mk_app(
            Symbol::named("store"),
            vec![base, index, value],
            int_array.clone(),
        )
    };
    let left_inner = mk_store(&mut terms, a, i0, v0);
    let left = mk_store(&mut terms, left_inner, i1, v1);
    let right_inner = mk_store(&mut terms, a, i1, v1);
    let right = mk_store(&mut terms, right_inner, i0, v0);
    let index_eq = terms.mk_app(Symbol::named("="), vec![i0, i1], Sort::Bool);
    let arrays_eq = terms.mk_app(Symbol::named("="), vec![left, right], Sort::Bool);
    let not_index_eq = terms.mk_not_raw(index_eq);
    let not_arrays_eq = terms.mk_not_raw(arrays_eq);

    // The SAME leaves the `storecomm` retag test uses, but recorded as unit
    // theory lemmas rather than assumptions, so the derived-leaf route runs.
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("UNKNOWN", vec![not_index_eq], TheoryLemmaKind::Generic);
    proof.add_theory_lemma_with_kind("UNKNOWN", vec![not_arrays_eq], TheoryLemmaKind::Generic);
    closer(&mut terms, &mut proof);

    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArrayStorePermutation,
                ..
            }
        )),
        "a head the array recognizer accepts must still be emitted, got: {}",
        export_alethe(&proof, &terms)
    );
    assert!(
        derives_empty_clause(&proof),
        "the validated derived-leaf head must still close on the empty clause"
    );
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                theory,
                kind: TheoryLemmaKind::Generic,
                clause,
                ..
            } if theory == "trust" && clause.len() == 2
        )),
        "the validated route must not ALSO record a trust head"
    );
}

/// A derived leaf that IS the constant `false` closes honestly: Alethe's own
/// `false` rule proves `(cl (not false))` and one resolution reaches the empty
/// clause. No head, no trust step added, every added step strict-checkable.
///
/// This is the `bug3_enum_card_ite_distinct.smt2` shape, and it is the ONE
/// verdict the bare refusal cost before this lane existed.
#[test]
fn a_false_derived_leaf_closes_by_the_alethe_false_rule() {
    let mut terms = TermStore::new();
    let enum_sort = Sort::Uninterpreted("Enum".to_string());
    let c0 = terms.mk_var("c0", enum_sort.clone());
    let fa = terms.mk_var("fa", enum_sort.clone());
    let disjunct = terms.mk_app(Symbol::named("="), vec![c0, fa], Sort::Bool);
    let false_term = terms.false_term();

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("UNKNOWN", vec![disjunct], TheoryLemmaKind::Generic);
    let false_leaf =
        proof.add_theory_lemma_with_kind("UNKNOWN", vec![false_term], TheoryLemmaKind::Generic);
    closer(&mut terms, &mut proof);

    assert_eq!(
        theory_lemma_heads(&proof),
        vec![(TheoryLemmaKind::Generic, 1), (TheoryLemmaKind::Generic, 1),],
        "closing through the `false` rule must add NO theory lemma of any kind"
    );
    let not_false = terms.mk_not_raw(false_term);
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::False,
                clause,
                premises,
                ..
            } if clause.as_slice() == [not_false] && premises.is_empty()
        )),
        "expected the Alethe `false` rule proving (cl (not false)), got: {}",
        export_alethe(&proof, &terms)
    );
    assert!(
        matches!(
            proof.steps.last(),
            Some(ProofStep::Step {
                rule: AletheRule::Resolution,
                clause,
                premises,
                ..
            }) if clause.is_empty() && premises.contains(&false_leaf)
        ),
        "the closure must be one resolution against the `false` leaf itself"
    );
    let (_summary, error) = check_proof_partial(&proof, &terms);
    assert!(
        error.is_none(),
        "the `false`-rule closure must be checker-valid, got {error:?}"
    );
    // Stronger: every NON-trust step must pass the STRICT boundary. The
    // collecting checker validates exactly that, so an `Ok` here means the
    // `false` axiom and the closing resolution are both strict-checkable and
    // only the two pre-existing `Generic` leaves are deferred.
    let collected = ay_proof::check_proof_collecting_trust(&proof, &terms)
        .expect("the `false` axiom and the closing resolution must be STRICT-valid");
    assert_eq!(
        collected.len(),
        2,
        "only the two pre-existing trust leaves may be deferred, got {collected:?}"
    );
    assert!(
        collected.iter().all(|(_, clause)| clause.len() == 1),
        "the closer must not add an obligation of its own on this route"
    );
}

/// PRINTER PIN on the honest closure's exact wire text for the measured
/// `write_write_overwrite` shape. `t0`/`t1` are the pre-existing trust leaves
/// and `t2` is the closer's entire contribution — an EMPTY clause that mentions
/// no array term at all. All three print as `:rule hole`, Alethe's spelling for
/// an unproved obligation, which is exactly what each of them is; before this
/// change `t2` was `(cl (not (= (select (store a i v2) j) (select a j))) (not (=
/// (select a j) (select (store a i v1) j))))`, a clause the array model refutes.
#[test]
fn the_refused_head_is_replaced_by_an_empty_clause_trust_step_on_the_wire() {
    let mut fixture = write_write_overwrite();
    closer(&mut fixture.terms, &mut fixture.proof);
    let wire = export_alethe(&fixture.proof, &fixture.terms);
    assert_eq!(
        wire.trim_end(),
        "(declare-fun a () (Array Index Element))\n\
         (declare-fun i () Index)\n\
         (declare-fun j () Index)\n\
         (declare-fun v1 () Element)\n\
         (declare-fun v2 () Element)\n\
         (step t0 (cl (= (select (store a i v2) j) (select a j))) :rule hole)\n\
         (step t1 (cl (= (select a j) (select (store a i v1) j))) :rule hole)\n\
         (step t2 (cl) :rule hole)",
        "the honest closure's wire text drifted"
    );
}

/// PRINTER PIN on the `false`-rule closure's exact wire text, so the honest
/// closure cannot silently become a trust step again.
#[test]
fn the_false_rule_closure_prints_the_expected_wire_text() {
    let mut terms = TermStore::new();
    let false_term = terms.false_term();
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("UNKNOWN", vec![false_term], TheoryLemmaKind::Generic);
    closer(&mut terms, &mut proof);

    // The whole artifact, byte for byte. `t0` is the PRE-EXISTING trust leaf,
    // which the printer already renders as an honest `hole`; `t1` and `t2` are
    // the closer's entire contribution and both are strict-checkable rules.
    let wire = export_alethe(&proof, &terms);
    assert_eq!(
        wire.trim_end(),
        "(step t0 (cl false) :rule hole)\n\
         (step t1 (cl (not false)) :rule false)\n\
         (step t2 (cl) :rule resolution :premises (t1 t0))",
        "the `false`-rule closure's wire text drifted"
    );
    let closer_steps: Vec<&str> = wire
        .lines()
        .filter(|line| line.starts_with("(step t1") || line.starts_with("(step t2"))
        .collect();
    assert_eq!(
        closer_steps.len(),
        2,
        "the closer must add exactly two steps"
    );
    for line in closer_steps {
        assert!(
            !line.contains(":rule trust") && !line.contains(":rule hole"),
            "the closer's own steps must be neither trust nor hole: {line}"
        );
    }
}

// ===== the SECOND measured shape: a RoundingMode enum head =====

/// A bespoke finite-carrier evaluator for the `RoundingMode` head. Five
/// distinct values, `=`/`and`/`or`/`not` — nothing else is needed, and nothing
/// here is shared with the closer or the checker.
fn enum_holds(terms: &TermStore, term: TermId, binding: &[(TermId, usize)]) -> Option<bool> {
    fn value(term: TermId, binding: &[(TermId, usize)]) -> Option<usize> {
        binding
            .iter()
            .find(|(id, _)| *id == term)
            .map(|(_, carrier)| *carrier)
    }
    match terms.get(term) {
        TermData::Not(inner) => enum_holds(terms, *inner, binding).map(|v| !v),
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some(value(args[0], binding)? == value(args[1], binding)?)
        }
        TermData::App(Symbol::Named(name), args) if name == "and" => {
            let mut all = true;
            for &arg in args {
                all &= enum_holds(terms, arg, binding)?;
            }
            Some(all)
        }
        TermData::App(Symbol::Named(name), args) if name == "or" => {
            let mut any = false;
            for &arg in args {
                any |= enum_holds(terms, arg, binding)?;
            }
            Some(any)
        }
        _ => None,
    }
}

/// The exact shape `executor::theories::fp::tests::
/// fp_symbolic_rounding_mode_free_rm_wrong_unsat_is_not_unsat` hands the closer
/// on an inner branch: two unit `Generic` lemmas, `RoundingMode` constructor
/// distinctness and the five-way exhaustiveness disjunction, and NO `Assume`.
/// Both are validities of that enum, so the head — their joint negation — is
/// false in every model, and the closer must refuse it.
fn rounding_mode_leaves() -> (TermStore, Proof, Vec<TermId>, Vec<(TermId, usize)>) {
    let mut terms = TermStore::new();
    let rm_sort = Sort::Uninterpreted("RoundingMode".to_string());
    let modes: Vec<TermId> = ["RNE", "RNA", "RTP", "RTN", "RTZ"]
        .iter()
        .map(|name| terms.mk_var(*name, rm_sort.clone()))
        .collect();
    let rm = terms.mk_var("rm", rm_sort);

    let mut distinct_pairs = Vec::new();
    for first in 0..modes.len() {
        for second in (first + 1)..modes.len() {
            let equal = terms.mk_app(
                Symbol::named("="),
                vec![modes[first], modes[second]],
                Sort::Bool,
            );
            distinct_pairs.push(terms.mk_not_raw(equal));
        }
    }
    let distinctness = terms.mk_app(Symbol::named("and"), distinct_pairs, Sort::Bool);
    let choices: Vec<TermId> = modes
        .iter()
        .map(|&mode| terms.mk_app(Symbol::named("="), vec![rm, mode], Sort::Bool))
        .collect();
    let exhaustive = terms.mk_app(Symbol::named("or"), choices, Sort::Bool);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("UNKNOWN", vec![distinctness], TheoryLemmaKind::Generic);
    proof.add_theory_lemma_with_kind("UNKNOWN", vec![exhaustive], TheoryLemmaKind::Generic);

    let head = vec![terms.mk_not_raw(distinctness), terms.mk_not_raw(exhaustive)];
    // RNE..RTZ are five distinct carrier values and `rm` is RNE.
    let mut binding: Vec<(TermId, usize)> = modes
        .iter()
        .enumerate()
        .map(|(value, &mode)| (mode, value))
        .collect();
    binding.push((rm, 0));
    (terms, proof, head, binding)
}

/// COMPLETE REFUTATION of the RoundingMode head: five distinct modes, `rm =
/// RNE`. Both leaves hold, so both head literals are false.
#[test]
fn the_rounding_mode_head_is_false_at_five_distinct_modes_with_rm_equal_rne() {
    let (terms, _proof, head, binding) = rounding_mode_leaves();
    for (position, &literal) in head.iter().enumerate() {
        assert_eq!(
            enum_holds(&terms, literal, &binding),
            Some(false),
            "RoundingMode head literal {position} must be FALSE when the five modes are              distinct and rm = RNE: {}",
            ay_proof::format_term_alethe(&terms, literal)
        );
    }
}

/// SENSITIVITY CONTROL: collapse two modes onto one carrier value and the
/// distinctness leaf fails, so the head acquires a true literal.
#[test]
fn the_rounding_mode_head_has_a_true_literal_once_two_modes_collide() {
    let (terms, _proof, head, mut binding) = rounding_mode_leaves();
    // RNA now shares RNE's value, so `(not (= RNE RNA))` fails.
    binding[1].1 = 0;
    assert!(
        head.iter()
            .any(|&literal| enum_holds(&terms, literal, &binding) == Some(true)),
        "the head must acquire a TRUE literal once two rounding modes collide"
    );
}

/// FAIL CLOSED on the RoundingMode shape too — the refusal is not array-specific.
#[test]
fn closer_refuses_the_rounding_mode_derived_leaf_head() {
    let (mut terms, mut proof, head, _binding) = rounding_mode_leaves();
    closer(&mut terms, &mut proof);
    assert_eq!(
        theory_lemma_heads(&proof),
        vec![(TheoryLemmaKind::Generic, 1), (TheoryLemmaKind::Generic, 1),],
        "no RoundingMode head may be recorded, got: {}",
        export_alethe(&proof, &terms)
    );
    for step in &proof.steps {
        let clause: &[TermId] = match step {
            ProofStep::TheoryLemma { clause, .. } | ProofStep::Step { clause, .. } => clause,
            _ => continue,
        };
        assert_ne!(
            clause,
            head.as_slice(),
            "the refuted head must not be recorded"
        );
    }
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Step {
            rule: AletheRule::Trust,
            clause,
            premises,
            ..
        }) if clause.is_empty() && premises.is_empty()
    ));
}

/// REGRESSION GUARD on the route that is NOT changed: an assume-anchored head
/// is still the honest `Generic` trust stub and still closes.
#[test]
fn an_assume_anchored_head_is_left_exactly_as_it_was() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_q = terms.mk_not(q);

    let mut proof = Proof::new();
    proof.add_assume(p, Some("h0".to_string()));
    proof.add_assume(not_q, Some("h1".to_string()));
    closer(&mut terms, &mut proof);

    assert_eq!(
        theory_lemma_heads(&proof),
        vec![(TheoryLemmaKind::Generic, 2)],
        "the assume-anchored route must still record its honest trust head"
    );
    assert!(
        derives_empty_clause(&proof),
        "the assume-anchored route must still close on the empty clause"
    );
    let (_summary, error) = check_proof_partial(&proof, &terms);
    assert!(
        error.is_none(),
        "the assume-anchored chain must remain checker-valid, got {error:?}"
    );
}

/// SCOPE GUARD on the `false`-rule lane: it is for DERIVED leaves only. An
/// `Assume(false)` is assume-family, already has a licensed head, and has its
/// own dedicated rebuild lane (`executor::proof`'s exact-authored-`false`
/// route), so this closer must leave it byte-identical.
#[test]
fn a_false_assume_still_takes_the_assume_family_head_route() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let false_term = terms.false_term();

    let mut proof = Proof::new();
    proof.add_assume(p, Some("h0".to_string()));
    proof.add_assume(false_term, Some("h1".to_string()));
    closer(&mut terms, &mut proof);

    assert_eq!(
        theory_lemma_heads(&proof),
        vec![(TheoryLemmaKind::Generic, 2)],
        "the assume-family route must still record its head even when a leaf is `false`"
    );
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::False,
                ..
            }
        )),
        "the `false`-rule lane must not fire on the assume-family route"
    );
    assert!(derives_empty_clause(&proof));
}

/// REGRESSION GUARD: a proof whose ONLY leaves are premiseless unit `trust`
/// steps is assume-family, not derived, and keeps its head. Those steps are
/// authored assumptions a demotion pass rewrote (`proof_rewrite_division::
/// demote_non_problem_assumptions`), which is why they are leaves at all.
/// Measured over `benchmarks/**/*.smt2`: 0 of 358 assume-route closer
/// invocations were anchored on one, so this pins a boundary rather than a
/// behaviour the corpus exercises.
#[test]
fn a_unit_trust_leaf_still_anchors_the_assume_family_route() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_q = terms.mk_not(q);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![p], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![not_q], Vec::new(), Vec::new());
    closer(&mut terms, &mut proof);

    assert_eq!(
        theory_lemma_heads(&proof),
        vec![(TheoryLemmaKind::Generic, 2)],
        "premiseless unit trust leaves are assume-family and still anchor a head"
    );
    assert!(derives_empty_clause(&proof));
}
