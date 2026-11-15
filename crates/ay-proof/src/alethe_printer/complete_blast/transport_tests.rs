// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests of the refutation transport: the monolithic refutation it
//! starts from, and its chain expansion.

use super::{expand_rup_step, ChainContext, ChainStep, PrintedClause};
use ay_core::kani_compat::DetHashMap;
use ay_sat::resolution_dag::RupStep;
use ay_sat::{Literal, Variable};

/// REGRESSION (external-codegen `Sub_Lsl_Shift_I64 k=1`; the retry in
/// `ay_sat::prove_unsat_resolution_dag`): the monolithic CDCL refutation of
/// the 8,399-clause blast of `base - src*2 == base - (src<<1)` at 64 bits.
/// AY's SAT engine refutes it, but its `backbone` pass materialized a unit as
/// a hint-less `TrustedTransform`, the in-memory LRAT proof failed closed, and
/// `ay_sat::prove_unsat_resolution_dag` answered `Unknown`. The complete blast
/// now sweeps a circuit this large before it tries the monolithic proof, so
/// its rendered document no longer shows the defect; the SAT entry point is
/// asked directly, as its other callers ask it, and as the monolithic
/// fallback asks it, inside its counted envelope (`transport/monolithic.rs`),
/// which the retry is charged against too. It is the heaviest monolithic
/// refutation known: an envelope of 9,000 conflicts, or of 60,000 decisions,
/// declines it.
#[test]
fn the_monolithic_refutation_of_a_subtracted_doubling_is_found() {
    use super::super::{AlethePrinter, Blaster};
    use ay_core::{ProofId, Sort, Symbol, TermStore};
    use num_bigint::BigInt;

    let mut terms = TermStore::new();
    let base = terms.mk_var("base", Sort::bitvec(64));
    let src = terms.mk_var("src", Sort::bitvec(64));
    let two = terms.mk_bitvec(BigInt::from(2), 64);
    let one = terms.mk_bitvec(BigInt::from(1), 64);
    let mut op =
        |name: &str, args: [_; 2]| terms.mk_app(Symbol::named(name), args, Sort::bitvec(64));
    let doubled = op("bvmul", [src, two]);
    let shifted = op("bvshl", [src, one]);
    let left = op("bvsub", [base, doubled]);
    let right = op("bvsub", [base, shifted]);
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let assertion = terms.mk_not_raw(equality);

    let printer = AlethePrinter::new(&terms);
    let mut blaster = Blaster::new(&printer, ProofId(1), "@ay_cbb_t_".into());
    let root = blaster.prepare(assertion).expect("the lemma blasts");
    let (cnf, _) = blaster.planned_cnf(root).expect("the CNF is planned");
    let variables = blaster.circuit.len();
    assert!(
        ay_sat::prove_unsat_resolution_dag(variables, &cnf).is_ok(),
        "the {}-clause blast is UNSAT and must be refuted",
        cnf.len()
    );
    crate::resolution_dag_memo::reset_resolution_dag_memo();
    assert!(
        blaster
            .monolithic_refutation_planned(variables, &cnf)
            .is_ok(),
        "the monolithic fallback's envelope must hold its refutation"
    );
}

/// A FALSE lemma past the sweep's threshold is declined by the direct lane's
/// own model: `(= (bvudiv x y) z)` over 32-bit words is satisfiable, and its
/// blast (a divider, thousands of gates) is planned as a large circuit. The
/// case split, the sweep and the monolithic search after the direct lane
/// could only spend their envelopes to say the same (measured on a fuzzed
/// 16-bit query: 15.9 CPU-s against 0.03 for the verdict ay already had).
#[test]
fn a_false_lemma_is_declined_by_the_direct_lanes_model() {
    use super::super::{AlethePrinter, Blaster};
    use super::{Directly, Target};
    use ay_core::{ProofId, Sort, Symbol, TermStore};

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(32));
    let y = terms.mk_var("y", Sort::bitvec(32));
    let z = terms.mk_var("z", Sort::bitvec(32));
    let quotient = terms.mk_app(Symbol::named("bvudiv"), [x, y], Sort::bitvec(32));
    let assertion = terms.mk_app(Symbol::named("="), [quotient, z], Sort::Bool);

    let printer = AlethePrinter::new(&terms);
    let mut blaster = Blaster::new(&printer, ProofId(1), "@ay_cbb_t_".into());
    let root = blaster.prepare(assertion).expect("the lemma blasts");
    let (cnf, root_clause_id) = blaster.planned_cnf(root).expect("the CNF is planned");
    let variables = blaster.circuit.len();
    assert!(
        variables >= super::sweep::SWEEP_FIRST_GATES,
        "the fixture must be a large circuit, got {variables} gates"
    );
    crate::resolution_dag_memo::reset_resolution_dag_memo();
    let target = Target {
        cnf: &cnf,
        root_clause_id,
        root,
        unit: "t1",
        final_clause: "(cl)",
    };
    assert!(matches!(
        blaster.directly(variables, &target),
        Directly::Satisfiable
    ));
    assert!(blaster
        .finish_planned(&cnf, root_clause_id, root, "t1", "(cl)")
        .is_none());
}

fn pos(var: u32) -> Literal {
    Literal::positive(Variable::new(var))
}

fn neg(var: u32) -> Literal {
    Literal::negative(Variable::new(var))
}

/// Variables of the fixture.
const A: u32 = 0;
const B: u32 = 1;
const ROOT: u32 = 2;

/// The engine's clause set, in LRAT id order: the assumed root unit `(r)`
/// (id 1), `(not r) a` (id 2) and `(not a)` (id 3).
fn engine_cnf() -> Vec<Vec<Literal>> {
    vec![vec![pos(ROOT)], vec![neg(ROOT), pos(A)], vec![neg(A)]]
}

/// The printed input clauses. The root unit is never printed as a premise.
fn printed_inputs() -> DetHashMap<u64, PrintedClause> {
    let mut printed = DetHashMap::default();
    printed.insert(
        2,
        PrintedClause {
            name: "t.c2".into(),
            lits: vec![neg(ROOT), pos(A)],
            count_safe: true,
        },
    );
    printed.insert(
        3,
        PrintedClause {
            name: "t.c3".into(),
            lits: vec![neg(A)],
            count_safe: true,
        },
    );
    printed
}

/// Expand one derived step over the fixture's clauses.
fn expand(step: &RupStep, force_binary: bool) -> (Option<PrintedClause>, Vec<ChainStep>) {
    let cnf = engine_cnf();
    let derived = vec![step.clone()];
    let mut position = DetHashMap::default();
    position.insert(step.id, 0_usize);
    let context = ChainContext {
        cnf: &cnf,
        derived: &derived,
        position: &position,
        original_count: cnf.len() as u64,
        root_clause_id: 1,
        root_negative: neg(ROOT),
    };
    let printed = printed_inputs();
    let mut next = 0_u64;
    let mut emitted = Vec::new();
    let result = expand_rup_step(
        "t",
        step,
        &context,
        &printed,
        &mut next,
        &mut emitted,
        force_binary,
        &mut Vec::new(),
        true,
    );
    (result, emitted)
}

/// REGRESSION (the transport half of the `weakening` extension): the
/// engine derived `(b)` from hints that are already conflicting without `b`,
/// so the chain lands on `(not r)`, a STRICT SUBSET of the derived clause plus
/// the carried assumption literal. The chain used to be refused (the lemma
/// kept its `hole`); it is now extended by ONE `weakening` step whose
/// conclusion begins with its premise's literals, in order, which is what the
/// consumer's `weakening` rule demands.
#[test]
fn a_chain_landing_on_a_strict_subset_is_weakened_to_the_derived_clause() {
    let step = RupStep {
        id: 10,
        clause: vec![pos(B)],
        rup_hints: vec![1, 2, 3],
    };
    let (result, emitted) = expand(&step, false);
    let result = result.expect("a strict-subset chain is weakened, not refused");

    assert_eq!(emitted.len(), 2, "one resolution, then one weakening");
    let (chain, weakening) = (&emitted[0], &emitted[1]);
    assert!(!chain.weakening);
    assert_eq!(chain.lits, vec![neg(ROOT)], "the chain lands on (not r)");
    assert_eq!(chain.premises, vec!["t.c3".to_owned(), "t.c2".to_owned()]);

    assert!(weakening.weakening);
    assert!(weakening.pivots.is_empty());
    assert_eq!(weakening.premises, vec![chain.name.clone()]);
    assert_eq!(
        weakening.lits,
        vec![neg(ROOT), pos(B)],
        "the premise's literals, in order, are the conclusion's prefix"
    );
    assert!(weakening.lits.starts_with(&chain.lits));

    assert_eq!(result.name, weakening.name);
    assert_eq!(result.lits, weakening.lits);
    assert!(result.count_safe);
}

/// The final step's clause is printed by the caller at the word level, so a
/// forced-binary step has no spelling a `weakening` could extend: it is still
/// refused rather than weakened.
#[test]
fn a_forced_binary_chain_is_not_weakened() {
    let step = RupStep {
        id: 10,
        clause: vec![pos(B)],
        rup_hints: vec![1, 2, 3],
    };
    let (result, emitted) = expand(&step, true);
    assert!(result.is_none());
    assert!(
        emitted.iter().all(|step| !step.weakening),
        "no weakening was emitted"
    );
}

/// A chain that lands exactly on the derived clause plus the carried literal
/// needs no weakening.
#[test]
fn a_chain_landing_on_the_derived_clause_is_not_weakened() {
    let step = RupStep {
        id: 10,
        clause: vec![],
        rup_hints: vec![1, 2, 3],
    };
    let (result, emitted) = expand(&step, false);
    let result = result.expect("the chain lands on the carried clause");
    assert_eq!(result.lits, vec![neg(ROOT)]);
    assert_eq!(emitted.len(), 1);
    assert!(!emitted[0].weakening);
}

/// REGRESSION (the premise half of the `weakening` extension): an input
/// clause that `normalize` re-derives is recorded with the literals its LAST
/// normalization step prints, in printed order, not with the planned CNF
/// clause. The planned clause `(not (not g)) h h` is re-spelled through
/// `not_not` and `contraction` to `g h`; the CNF still carries `g h h`, and a
/// `weakening` of the recorded clause must repeat `g h` as its prefix.
#[test]
fn a_normalized_input_clause_records_its_printed_literals() {
    use super::super::circuit::SRef;
    use super::super::{AlethePrinter, Blaster, ClauseEmit, PlannedClause};
    use ay_core::kani_compat::DetHashSet;
    use ay_core::{ProofId, Sort, Symbol, TermStore};

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(2));
    let y = terms.mk_var("y", Sort::bitvec(2));
    let equality = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let assertion = terms.mk_not_raw(equality);

    let printer = AlethePrinter::new(&terms);
    let mut blaster = Blaster::new(&printer, ProofId(1), "@ay_cbb_t_".into());
    let root = blaster.prepare(assertion).expect("the lemma blasts");
    let g = root.gate;
    let h = (0..blaster.circuit.len() as u32)
        .find(|gate| *gate != g)
        .expect("the circuit has a second gate");

    let index = blaster.planned.len();
    blaster.planned.push(PlannedClause {
        lits: vec![
            SRef { gate: g, nots: 2 },
            SRef { gate: h, nots: 0 },
            SRef { gate: h, nots: 0 },
        ],
        emit: ClauseEmit::Rule {
            rule: "fixture",
            args: None,
            premises: Vec::new(),
        },
    });
    let lit = |gate: u32| {
        Blaster::sat_literal(SRef { gate, nots: 0 }).expect("the gate has a SAT literal")
    };
    let mut cnf: Vec<Vec<Literal>> = vec![Vec::new(); index];
    cnf.push(vec![lit(g), lit(h), lit(h)]);
    let id = index as u64 + 1;
    let mut used = DetHashSet::default();
    used.insert(id);

    let mut body = String::new();
    let printed = blaster.print_used_originals(&cnf, &used, &mut body);
    let clause = printed.get(&id).expect("the used input clause is recorded");
    assert!(
        clause.name.ends_with(&format!(".cbbn{index}.c")),
        "the clause is named by its contraction step, got {}",
        clause.name
    );
    assert!(body.contains(":rule not_not"), "{body}");
    assert!(body.contains(":rule contraction"), "{body}");
    assert!(clause.count_safe);
    assert_eq!(
        clause.lits,
        vec![lit(g), lit(h)],
        "the recorded literals are the ones the contraction step prints, not the CNF clause"
    );
}

/// Every lane of the complete bit-blast declines at its entry once the
/// caller's stop has fired, before it plans, looks up or starts a
/// refutation: each pays unpolled work in the size of the circuit first (a
/// plan re-blasts, a sweep simulates, the monolithic solve loads every
/// clause). Measured on the twenty-product commuted sum at 64 bits, asked
/// until a 10 s stop: the monolithic fallback loaded every clause after the
/// stop had fired, and the question returned at 23.9 s. The twin: idle, the
/// same stop leaves every lane its answer.
#[test]
fn every_lane_declines_at_its_entry_once_the_stop_has_fired() {
    use super::super::circuit::SRef;
    use super::super::{AlethePrinter, Blaster, CompleteBlastAsk};
    use super::{CaseSplit, Directly, Target};
    use crate::resolution_dag_memo::{reset_resolution_dag_memo, resolution_dag_memo_counters};
    use crate::sat_sweep::split::Leaves;
    use ay_core::{ProofId, Sort, Symbol, TermStore};
    use std::cell::Cell;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    let ab = terms.mk_app(Symbol::named("bvmul"), [a, b], Sort::bitvec(4));
    let ba = terms.mk_app(Symbol::named("bvmul"), [b, a], Sort::bitvec(4));
    let equality = terms.mk_app(Symbol::named("="), [ab, ba], Sort::Bool);
    let assertion = terms.mk_not_raw(equality);
    let fired = Cell::new(false);
    let stop = || fired.get();
    let printer =
        AlethePrinter::new(&terms).asking_complete_blast(CompleteBlastAsk::AskedUntil(&stop));
    let orient = |_: &mut Blaster<'_, '_>, roots: &[SRef]| roots.first().copied();
    let plan = |fired_now: bool| {
        fired.set(fired_now);
        Blaster::plan_lemma(
            &printer,
            ProofId(1),
            "@ay_cbb_t_",
            &[assertion],
            &orient,
            true,
            None,
        )
        .is_some()
    };
    assert!(plan(false), "idle, the lemma is planned");
    assert!(!plan(true), "fired, no round re-blasts the circuit");

    fired.set(false);
    let mut blaster = Blaster::new(&printer, ProofId(1), "@ay_cbb_t_".into());
    let root = blaster.prepare(assertion).expect("the lemma blasts");
    let (cnf, root_clause_id) = blaster.planned_cnf(root).expect("the CNF is planned");
    let extension = blaster
        .case_split_cnf(&cnf)
        .expect("idle, the case split is planned");
    let variables = blaster.circuit.len();
    let target = Target {
        cnf: &cnf,
        root_clause_id,
        root,
        unit: "t1",
        final_clause: "(cl)",
    };

    fired.set(true);
    reset_resolution_dag_memo();
    assert!(matches!(
        blaster.directly(variables, &target),
        Directly::Declined
    ));
    assert!(blaster
        .retained_refutation(variables, &cnf, root_clause_id)
        .is_none());
    assert!(blaster.case_split_cnf(&cnf).is_none());
    assert!(matches!(
        blaster.cases_document(&extension, &target, Leaves::All),
        CaseSplit::Declined
    ));
    assert!(matches!(
        blaster.monolithic_refutation_planned(variables, &cnf),
        Err(false)
    ));
    assert_eq!(
        resolution_dag_memo_counters(),
        (0, 0),
        "no lane looked up a refutation"
    );

    fired.set(false);
    assert!(blaster
        .monolithic_refutation_planned(variables, &cnf)
        .is_ok());
    assert!(blaster
        .retained_refutation(variables, &cnf, root_clause_id)
        .is_some());
}
