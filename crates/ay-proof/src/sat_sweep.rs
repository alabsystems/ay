// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT SWEEPING: a refutation of a gate-structured CNF as a chain of small,
//! local lemmas, for the Alethe printer's complete bit-blast
//! (`alethe_printer/complete_blast/sweep.rs`), whose transport replays every
//! chain before printing it.
//!
//! The strict checker's bit-blast producer sweeps too, inside its counted
//! envelope and only for a clause over no array
//! (`bv_blast_solver/sweep.rs`), and both callers first try the case split
//! (`split`) for a root that leaves guarded facts open.
//!
//! ## Why this exists
//!
//! One monolithic CDCL refutation of a whole miter is correct but, on
//! arithmetic circuits, enormous. Measured 2026-09-28: `x * 4 = x << 2` at 64
//! bits and `x / 4 = x >> 2` at 32 bits each transported to about 80 MB of
//! resolution text, past the document budget, and even the 8-bit divider
//! printed 46 MB — 47,122 resolution steps whose learned clauses carry ~44
//! literals each. external-codegen's `Sub_Lsl_Shift`, `Add_Lsr_Shift`,
//! `StrengthReduce` and `UDIV/MUL ≡ shift` peepholes stayed holes on exactly
//! that, although every one of them is an equivalence between two circuits
//! whose internal signals line up.
//!
//! ## What it does
//!
//! Classic fraiging. The circuit is simulated on random patterns; gates with
//! equal (or complementary) simulation signatures are CANDIDATE equivalences,
//! and an all-constant signature is a candidate constant. In topological
//! order each candidate is proved by its own refutation: the lemma's negation
//! is assumed as unit clauses over the CONE of the two gates, where every gate
//! already proved equivalent to an earlier one stops the cone at that
//! representative. A refuted candidate (a model) becomes a new simulation
//! pattern. Once the candidates are exhausted, a final refutation over the
//! root's cone — now mostly lemmas — closes the proof.
//!
//! Before any candidate, a theory atom aliasing a later gate is merged into
//! it (`alias.rs`), every live gate's missing prime clauses are derived
//! (`prime.rs`), and, where the roots imply side conditions that only some
//! patterns meet, the sweep runs under them (`care.rs`).
//!
//! ## Why the result is a refutation of the SAME CNF
//!
//! A refutation of `F ∧ ¬l_1 ∧ … ∧ ¬l_k` becomes a derivation of the lemma
//! `l_1 ∨ … ∨ l_k` from `F` by adding the lemma's literals to every derived
//! clause and dropping the assumption units from the hints: each widened
//! clause is RUP from `F`, since negating it re-asserts exactly those units.
//! Every stitched step is replayed here as unit propagation over literal
//! sets (`replayed_hints`) and recorded as the resolvent its chain actually
//! derives, numbered into one LRAT id space above the original clauses; the
//! transport then replays the same chains again before printing. Nothing about the
//! search is trusted: a wrong candidate is refuted by a model, a lemma the
//! solver cannot decide within budget is simply not used, and a DAG that does
//! not validate is discarded for the monolithic lane.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_sat::{
    solve_resolution_dag_counted_local, Literal, ResolutionDag, ResolutionProofError,
    ResolutionProofLimits, ResolutionSolveOutcome, RupStep,
};
use std::time::{Duration, Instant};

mod alias;
mod care;
mod close;
mod prime;
mod proof;
mod scratch;
mod signature;
mod simulation;
mod solve;
pub(crate) mod split;
mod unit;
mod work;

pub(crate) use close::{refute_directly, Direct};
use proof::solver_clause;

/// Random simulation words (64 patterns each) before any counterexample.
const RANDOM_WORDS: usize = 4;
/// Simulation words at most, counterexample words included. Each costs one
/// simulation of the circuit; the signatures themselves do not grow
/// (`signature.rs`).
const MAX_WORDS: usize = 1_024;
/// Representatives one gate is tried against at most. A candidate class that
/// simulation has not yet split is mostly NOT equivalent, and each failed
/// candidate costs a refuted SAT call; the models it yields split the class
/// for the gates after it.
const MAX_CANDIDATES: usize = 4;
/// Conflicts allowed for one candidate lemma. Local lemmas need very few; a
/// candidate that needs more is left unmerged rather than paid for.
pub(crate) const LEMMA_CONFLICTS: u64 = 5_000;
/// Conflicts allowed for the closing refutation.
const FINAL_CONFLICTS: u64 = 2_000_000;
/// Candidate refutations attempted at most.
const MAX_LEMMA_CALLS: usize = 200_000;
/// ... or this many per gate of a larger circuit. A merge costs two calls and
/// a constant one; measured 2026-09-30 on external-codegen's 64-bit `SDIV`
/// definitional rows, 264,472 gates spent the flat 200,000 on the first
/// 150,459 of them (193,457 lemmas proved, 185,345 by unit propagation
/// alone). The wall clock and the conflict envelope still bound the sweep.
const LEMMA_CALLS_PER_GATE: usize = 2;
/// A cone this large is not local; the candidate is skipped.
const MAX_CONE_VARS: usize = 50_000;
/// Wall-clock bound for the whole sweep.
const SWEEP_WALL: Duration = Duration::from_secs(120);

/// What one sweep may spend. [`SweepLimits::standalone`] is the sweep's own
/// ceiling; a caller with a counted envelope — the strict checker's producer
/// (`bv_blast_solver/sweep.rs`) — narrows it to that envelope.
#[derive(Clone, Copy, Debug)]
pub(crate) struct SweepLimits {
    /// Conflicts one candidate lemma's refutation may spend.
    pub(crate) lemma_conflicts: u64,
    /// Conflicts all solver calls together may spend, each charged what it
    /// spent (`ay_sat::solve_resolution_dag_counted_local`).
    pub(crate) total_conflicts: u64,
    /// Literals all candidate attempts together may read (`work.rs`).
    pub(crate) total_work: u64,
    /// No solver call starts at or after this instant, and none runs past it.
    pub(crate) deadline: Instant,
}

impl SweepLimits {
    /// The sweep's own ceiling: `LEMMA_CONFLICTS` per lemma, `SWEEP_WALL`.
    ///
    /// So a sweep that cannot close declines at the wall, a decline no memo
    /// may keep across solves, and no count of its close ends it sooner
    /// without refusing sweeps that close today. Measured 2026-10-09 (X925
    /// cores), `bv_affine_source`'s affine identity at 16 bits refutes in its
    /// whole-CNF attempt after 614,284 conflicts, its failed cone attempt
    /// having spent 1,002,002 (a carcara-valid certificate, 104 s); at 64
    /// bits, which cannot close, its candidates take 67 s and the wall ends
    /// its cone attempt 0.84 to 0.93 million conflicts in.
    pub(crate) fn standalone() -> Self {
        Self {
            lemma_conflicts: LEMMA_CONFLICTS,
            total_conflicts: u64::MAX,
            total_work: u64::MAX,
            deadline: Instant::now() + SWEEP_WALL,
        }
    }
}

/// A gate's function, over SAT literals (`var == gate index`). Every
/// variable of the CNF has one; an `Input` is free.
pub(crate) enum Gate {
    Input,
    Const(bool),
    And(Vec<Literal>),
    Or(Vec<Literal>),
    /// The parity of all its operands.
    Xor(Vec<Literal>),
    Iff(Literal, Literal),
    Ite(Literal, Literal, Literal),
    /// At least two of the three: a full adder's carry.
    Majority(Literal, Literal, Literal),
    /// Equal to another literal (a theory atom tied to its definition).
    Alias(Literal),
    /// `ite(condition, then_bit, else_bit)` defined not by clauses of its own
    /// but by guarded ones — the printer's bit-vector `ite` bits
    /// (`alethe_printer/complete_blast/ite.rs`): `(cl (not c) E_then)` and
    /// `(cl c E_else)`, each `E` the conjunction of one bit equality per bit,
    /// this bit's being `links`. A cone takes the links and, UNEXPANDED, both
    /// `equalities`, so a lemma about this bit carries exactly the clauses
    /// that define it and not every other bit of the word.
    GuardedIte {
        condition: Literal,
        then_bit: Literal,
        else_bit: Literal,
        equalities: [usize; 2],
        links: [usize; 2],
    },
}

impl Gate {
    fn operands(&self) -> Vec<usize> {
        let var = |literal: &Literal| literal.variable().index();
        match self {
            Self::Input | Self::Const(_) => Vec::new(),
            Self::And(args) | Self::Or(args) | Self::Xor(args) => args.iter().map(var).collect(),
            Self::Iff(a, b) => vec![var(a), var(b)],
            Self::Ite(c, a, b) | Self::Majority(c, a, b) => vec![var(c), var(a), var(b)],
            Self::GuardedIte {
                condition,
                then_bit,
                else_bit,
                links,
                ..
            } => vec![
                var(condition),
                var(then_bit),
                var(else_bit),
                links[0],
                links[1],
            ],
            Self::Alias(target) => vec![var(target)],
        }
    }
}

/// How a swept gate was merged, and the derived ids of its lemma clauses.
enum Merge {
    Const(u64),
    Equiv(Literal, [u64; 2]),
}

enum Attempt {
    Proved(u64),
    Refuted(Vec<(usize, bool)>),
    Undecided,
}

pub(crate) fn literal(var: usize, negative: bool) -> Literal {
    Literal::from_index((var << 1) | usize::from(negative))
}

fn value_of(values: &[u64], lit: Literal) -> u64 {
    let value = values[lit.variable().index()];
    if lit.is_positive() {
        value
    } else {
        !value
    }
}

fn splitmix(seed: u64) -> u64 {
    let mut z = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// Sweep `cnf` — every variable's gate in `gates`, the clauses at `roots`
/// usable only by the closing refutation — into a refutation, or `None`.
///
/// With `transport_root`, `roots` is the one unit clause the printer's
/// transport carries as a literal: it never becomes a conflicting clause and
/// the final chain always resolves something.
pub(crate) fn refute(
    gates: Vec<Gate>,
    cnf: &[Vec<Literal>],
    roots: &[usize],
    transport_root: bool,
    limits: SweepLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Option<ResolutionDag> {
    refute_counted(gates, cnf, roots, transport_root, limits, keep_going).0
}

/// [`refute`], with what its solver calls and candidates spent.
pub(crate) fn refute_counted(
    gates: Vec<Gate>,
    cnf: &[Vec<Literal>],
    roots: &[usize],
    transport_root: bool,
    limits: SweepLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> (Option<ResolutionDag>, work::Spent) {
    let Some(mut sweep) = Sweep::new(gates, cnf, roots, transport_root, limits, keep_going) else {
        return (None, work::Spent::default());
    };
    sweep.sweep();
    sweep.close_counted(limits)
}

struct Sweep<'c, 'k> {
    nodes: Vec<Gate>,
    cnf: &'c [Vec<Literal>],
    /// Clauses only the closing refutation may use.
    roots: Vec<usize>,
    /// Whether each CNF clause is one of `roots`, by index (`proof/local.rs`).
    is_root: Vec<bool>,
    transport_root: bool,
    /// Each clause's index (the roots excluded) under its OWNER, the
    /// largest variable it mentions (`sat_sweep/proof.rs`, `Sweep::local`).
    by_owner: Vec<Vec<usize>>,
    /// Every gate's simulation signature (`signature.rs`).
    signatures: signature::Signatures,
    /// Whether a gate is in the roots' fan-in (`simulation::live_gates`): no other gate
    /// is swept or stands for another.
    live: Vec<bool>,
    merged: Vec<Option<Merge>>,
    derived: Vec<RupStep>,
    derived_at: DetHashMap<u64, usize>,
    next_id: u64,
    pending: Vec<Vec<(usize, bool)>>,
    lemma_calls: usize,
    /// Candidate refutations this sweep may attempt.
    max_lemma_calls: usize,
    deadline: Instant,
    /// Reused per-lemma membership marks (`scratch.rs`).
    scratch: std::cell::RefCell<scratch::Scratch>,
    lemma_conflicts: u64,
    /// Conflicts not yet spent (`SweepLimits`).
    conflicts_left: u64,
    /// Literals candidates may read (`SweepLimits::total_work`), and have.
    work_cap: u64,
    work_read: u64,
    keep_going: &'k mut dyn FnMut() -> bool,
    /// The caller refused further work: nothing more is attempted.
    stopped: bool,
    /// Every derived clause by its sorted literals, when stitching should
    /// reuse an equal clause instead of deriving it again (`split`).
    known_clauses: Option<DetHashMap<Vec<Literal>, u64>>,
    /// The roots' hypotheses, when the sweep is under them (`care.rs`).
    care: Option<care::Care>,
    /// The order gates are simulated in (`alias.rs`), `None` when their
    /// reads have a cycle ...
    order: Option<Vec<usize>>,
    /// ... and then every variable, in index order.
    index_order: Vec<usize>,
    /// Each gate's derived prime clauses, by id (`prime.rs`).
    prime: Vec<Vec<u64>>,
    /// The largest leaf core a split refutes where it meets it
    /// (`split::Leaves`), and whether one larger ended it.
    largest_leaf: usize,
    deferred_leaf: bool,
    /// The closing solve over every clause found a model (`close.rs`).
    satisfiable: bool,
    /// Binary LRAT one solver call may retain (`refute_directly` narrows it).
    proof_output_bytes: usize,
}

impl<'c, 'k> Sweep<'c, 'k> {
    fn new(
        nodes: Vec<Gate>,
        cnf: &'c [Vec<Literal>],
        roots: &[usize],
        transport_root: bool,
        limits: SweepLimits,
        keep_going: &'k mut dyn FnMut() -> bool,
    ) -> Option<Self> {
        let count = nodes.len();
        if roots.is_empty()
            || roots.iter().any(|&root| root >= cnf.len())
            || (transport_root && roots.len() != 1)
        {
            return None;
        }
        let mut is_root = vec![false; cnf.len()];
        for &root in roots {
            is_root[root] = true;
        }
        let mut by_owner: Vec<Vec<usize>> = vec![Vec::new(); count];
        for (index, clause) in cnf.iter().enumerate() {
            if is_root[index] {
                continue;
            }
            let owner = clause.iter().map(|lit| lit.variable().index()).max();
            if let Some(owner) = owner {
                by_owner.get_mut(owner)?.push(index);
            }
        }
        let mut nodes = nodes;
        alias::fix_unit_inputs(&mut nodes, cnf, roots);
        let live = simulation::live_gates(&nodes, cnf, roots);
        let order = alias::simulation_order(&nodes);
        let mut sweep = Self {
            nodes,
            cnf,
            roots: roots.to_vec(),
            is_root,
            transport_root,
            by_owner,
            signatures: signature::Signatures::new(count),
            live,
            merged: (0..count).map(|_| None).collect(),
            derived: Vec::new(),
            derived_at: DetHashMap::default(),
            next_id: u64::try_from(cnf.len()).ok()?.checked_add(1)?,
            pending: Vec::new(),
            lemma_calls: 0,
            max_lemma_calls: MAX_LEMMA_CALLS.max(count.saturating_mul(LEMMA_CALLS_PER_GATE)),
            deadline: limits.deadline,
            scratch: std::cell::RefCell::new(scratch::Scratch::new(count)),
            lemma_conflicts: limits.lemma_conflicts,
            conflicts_left: limits.total_conflicts,
            work_cap: limits.total_work,
            work_read: 0,
            keep_going,
            stopped: false,
            known_clauses: None,
            care: None,
            index_order: if order.is_some() {
                Vec::new()
            } else {
                (0..count).collect()
            },
            order,
            prime: vec![Vec::new(); count],
            largest_leaf: usize::MAX,
            deferred_leaf: false,
            satisfiable: false,
            proof_output_bytes: ResolutionProofLimits::default().max_proof_output_bytes,
        };
        sweep.merge_forward_aliases();
        sweep.derive_prime_clauses();
        sweep.take_care();
        let words = if sweep.care.is_some() {
            care::CARE_WORDS
        } else {
            RANDOM_WORDS
        };
        for word in 0..words {
            let salt = sweep.random_salt(word);
            let values = sweep.simulate(&mut |var| splitmix(salt ^ var as u64));
            sweep.absorb(&values);
        }
        Some(sweep)
    }

    fn sweep(&mut self) {
        let mut classes = self.classes(0);
        for var in 0..self.nodes.len() {
            if self.out_of_budget() {
                return;
            }
            if !self.live[var] || self.merged[var].is_some() {
                continue;
            }
            match self.nodes[var] {
                Gate::Const(_) => continue,
                Gate::Input => {
                    classes.entry(self.signature(var).0).or_default().push(var);
                    continue;
                }
                _ => {}
            }
            let (key, phase, constant) = self.signature(var);
            if !self.try_merge(var, key, phase, constant, &classes) {
                classes.entry(key).or_default().push(var);
            }
            if self.pending.len() >= 64 {
                self.flush_patterns();
                classes = self.classes(var + 1);
            }
        }
    }

    /// Prove `var` constant or equal to an earlier representative.
    fn try_merge(
        &mut self,
        var: usize,
        key: u64,
        phase: bool,
        constant: bool,
        classes: &DetHashMap<u64, Vec<usize>>,
    ) -> bool {
        if constant {
            // Constantly `phase`: the lemma is the unit that says so.
            match self.prove(&[literal(var, !phase)]) {
                Attempt::Proved(id) => {
                    self.merged[var] = Some(Merge::Const(id));
                    return true;
                }
                Attempt::Refuted(pattern) => self.pending.push(pattern),
                Attempt::Undecided => {}
            }
            return false;
        }
        let Some(candidates) = classes.get(&key) else {
            return false;
        };
        for &representative in candidates.iter().take(MAX_CANDIDATES) {
            if self.out_of_budget() {
                return false;
            }
            let (_, representative_phase, _) = self.signature(representative);
            let to = literal(representative, phase != representative_phase);
            let [forward, backward] = [
                [literal(var, true), to],
                [literal(var, false), to.negated()],
            ];
            let first = match self.prove(&forward) {
                Attempt::Proved(id) => id,
                Attempt::Refuted(pattern) => {
                    self.pending.push(pattern);
                    continue;
                }
                Attempt::Undecided => continue,
            };
            match self.prove(&backward) {
                Attempt::Proved(second) => {
                    self.merged[var] = Some(Merge::Equiv(to, [first, second]));
                    return true;
                }
                Attempt::Refuted(pattern) => self.pending.push(pattern),
                Attempt::Undecided => {}
            }
        }
        false
    }
}
