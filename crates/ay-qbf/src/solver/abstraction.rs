// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clausal-abstraction QBF search (the public verdict engine).
//!
//! Algorithm: Rabe & Tentrup, "CAQE: A Certifying QBF Solver" (FMCAD 2015),
//! and Janota & Marques-Silva, "Solving QBF by Clause Selection" (IJCAI 2015).
//! Each quantifier level owns an incremental SAT solver (`cdcl.rs`) over its own
//! variables plus one selector per clause it has reasoned about. The levels
//! play the two-player game outermost first; a level that loses learns a
//! refinement clause, and a level whose solver becomes unsatisfiable under
//! the outer context returns its assumption core to the level above.
//!
//! ## Why a verdict is right
//!
//! Write `V_i(T)` for the value of the game that starts at level `i` when the
//! clause set `T` is already satisfied by the outer levels. `V_i` is monotone
//! in `T`. Every fact the engine keeps is a statement about `V_i` for every
//! reachable `T` (a set of clauses that some outer assignment satisfies), not
//! about the current context only:
//!
//! - `Loss(R)` from level `i`: `V_i(T)` is false for every reachable `T` with
//!   `T ∩ R = ∅`, and `R` contains no clause of the level's input set.
//! - `Win(W)` from level `i`: `V_i(T)` is true for every reachable `T ⊇ W`,
//!   and `W` is a subset of the level's input set.
//!
//! An existential level `i` keeps, per clause `C`, a selector `b_C` with
//! `b_C → o_C ∨ C|level i` (`o_C`: "satisfied further out"), and for each
//! `Loss(R)` of level `i+1` the refinement `∨_{C∈R} b_C`. Under the
//! assumptions `¬o_C` for the clauses the context leaves unsatisfied, an
//! unsatisfiable query has a core `{¬o_C : C ∈ R'}`; any reachable `T`
//! disjoint from `R'` that `∃` could win would give a model (set `o_C` to
//! `C ∈ T`, `b_C` to "`C` satisfied after level `i`"), so `Loss(R')` holds.
//! A universal level is the dual: selectors `n_C → ¬o_C ∧ ¬l` for each
//! level-`i` literal `l` of `C`, refinements `∨_{C∈W} n_C` from each
//! `Win(W)` below, assumptions `o_C` for the clauses the context satisfies,
//! and an unsatisfiable core `{o_C : C ∈ W'}` proves `Win(W')`.
//!
//! The innermost level (always existential after universal reduction) holds
//! every clause; its `Win` is confirmed by counting satisfied clauses from
//! the actual assignment, not by trusting the SAT model. Only an UNSAT core
//! of the underlying SAT solver is taken on trust (its tests check every core
//! by brute force), and each core literal is checked to be one of the query's
//! assumptions.

use std::collections::HashMap;
use std::time::Instant;

use ay_sat::{Literal, Variable};

use super::cdcl::{Cdcl, CdclResult};
use crate::formula::{QbfFormula, Quantifier};

/// No clause owns this SAT variable / the clause is not yet satisfied.
const NONE: u32 = u32::MAX;

/// Clauses handled between two clock reads while the engine is built.
const CLOCK_STRIDE: usize = 4096;

fn expired(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|d| Instant::now() >= d)
}

/// Verdict of the abstraction engine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AbstractionVerdict {
    /// The formula is true.
    True,
    /// The formula is false.
    False,
    /// The deadline passed, or the SAT back end gave up or broke an
    /// invariant; no verdict.
    Unknown,
}

/// Outcome a level reports to the level above it (see the module comment).
enum Outcome {
    /// The existential player wins whenever all these clauses are satisfied.
    Win(Vec<u32>),
    /// The universal player wins whenever none of these clauses is satisfied.
    Loss(Vec<u32>),
}

/// One quantifier level of the game.
struct Level {
    quantifier: Quantifier,
    /// Original (1-based) variable ids of this level.
    vars: Vec<u32>,
    /// SAT variable for each entry of `vars`.
    sat_vars: Vec<Variable>,
    sat: Cdcl,
    /// Per clause: the refinement literal (`b_C` or `n_C`), or `None` when it
    /// is a constant (false for `∃`, true for `∀`).
    selectors: HashMap<u32, Option<Literal>>,
    /// Per clause: the context literal `o_C` (positive literal).
    outer_of: HashMap<u32, Literal>,
    /// `(clause, o_C)` in creation order, for building assumptions.
    outer: Vec<(u32, Literal)>,
    /// Clause owning each `o_C` SAT variable, indexed by SAT variable index.
    owner: Vec<u32>,
    /// Clauses this level's current assignment satisfied first.
    satisfied: Vec<u32>,
    /// The level learned an empty refinement: it loses in every context.
    dead: bool,
}

impl Level {
    fn new(quantifier: Quantifier, vars: Vec<u32>) -> Self {
        let mut sat = Cdcl::new();
        let mut owner = Vec::new();
        let sat_vars = vars
            .iter()
            .map(|_| {
                owner.push(NONE);
                sat.new_var()
            })
            .collect();
        Self {
            quantifier,
            vars,
            sat_vars,
            sat,
            selectors: HashMap::new(),
            outer_of: HashMap::new(),
            outer: Vec::new(),
            owner,
            satisfied: Vec::new(),
            dead: false,
        }
    }

    fn fresh(&mut self, owner: u32) -> Literal {
        let var = self.sat.new_var();
        let index = var.index();
        if self.owner.len() <= index {
            self.owner.resize(index + 1, NONE);
        }
        self.owner[index] = owner;
        Literal::positive(var)
    }
}

/// The clausal-abstraction engine over a preprocessed formula.
pub(crate) struct Abstraction {
    levels: Vec<Level>,
    /// Matrix after universal reduction, each clause sorted by level.
    clauses: Vec<Vec<Literal>>,
    /// Level of each original variable (`NONE` if it does not occur).
    var_level: Vec<u32>,
    /// Index of each original variable inside its level.
    var_local: Vec<u32>,
    /// Occurrence lists in CSR form, indexed by `literal_slot`.
    occ_start: Vec<u32>,
    occ: Vec<u32>,
    /// First level whose assignment satisfies each clause (`NONE`: none yet).
    sat_level: Vec<u32>,
    satisfied_count: usize,
    /// Current value of each original variable (`true` literal polarity),
    /// meaningful only while its level's assignment is applied.
    value: Vec<bool>,
}

/// Result of preprocessing: either a decided formula or an engine.
pub(crate) enum Prepared {
    Decided(AbstractionVerdict),
    Engine(Abstraction),
}

fn literal_slot(literal: Literal) -> usize {
    literal.index()
}

impl Abstraction {
    /// Build the engine. The formula must be `input_valid` (every matrix
    /// variable in `1..=num_vars`). The clock is read every
    /// [`CLOCK_STRIDE`] clauses of the two passes over the matrix (universal
    /// reduction and loading the innermost SAT solver); once `deadline` has
    /// passed, the result is `Decided(Unknown)`.
    pub(crate) fn prepare(formula: &QbfFormula, deadline: Option<Instant>) -> Prepared {
        let num_vars = formula.num_vars();

        // Raw block index per variable: 0 for free (implicitly outermost
        // existential) variables, `k + 1` for prefix block `k`.
        let mut block_of = vec![0u32; num_vars + 1];
        let mut block_quantifier = vec![Quantifier::Exists];
        for (k, block) in formula.prefix().iter().enumerate() {
            let index = u32::try_from(k + 1).unwrap_or(u32::MAX);
            block_quantifier.push(block.quantifier);
            for &var in &block.variables {
                if let Some(slot) = block_of.get_mut(var as usize) {
                    *slot = index;
                }
            }
        }
        let quantifier_of = |var: u32| block_quantifier[block_of[var as usize] as usize];

        // Universal reduction over the raw blocks (tautologies were removed
        // by `QbfFormula::new`). A clause reduced to nothing is falsified by
        // the universal player: the formula is false.
        let mut clauses = Vec::with_capacity(formula.clauses().len());
        for (index, clause) in formula.clauses().iter().enumerate() {
            if index % CLOCK_STRIDE == 0 && expired(deadline) {
                return Prepared::Decided(AbstractionVerdict::Unknown);
            }
            let max_exist = clause
                .iter()
                .filter(|l| quantifier_of(l.variable().id()) == Quantifier::Exists)
                .map(|l| block_of[l.variable().index()])
                .max();
            let Some(max_exist) = max_exist else {
                return Prepared::Decided(AbstractionVerdict::False);
            };
            let reduced: Vec<Literal> = clause
                .iter()
                .copied()
                .filter(|l| {
                    quantifier_of(l.variable().id()) == Quantifier::Exists
                        || block_of[l.variable().index()] < max_exist
                })
                .collect();
            clauses.push(reduced);
        }
        if clauses.is_empty() {
            return Prepared::Decided(AbstractionVerdict::True);
        }

        // Keep only occurring variables, then merge adjacent blocks of the
        // same quantifier into levels (this preserves every ∃/∀ order and so
        // the reduction above).
        let mut occurs = vec![false; num_vars + 1];
        for literal in clauses.iter().flatten() {
            occurs[literal.variable().index()] = true;
        }
        let mut block_vars: Vec<Vec<u32>> = vec![Vec::new(); block_quantifier.len()];
        for (var, _) in occurs.iter().enumerate().skip(1).filter(|(_, o)| **o) {
            let var = u32::try_from(var).unwrap_or(u32::MAX);
            block_vars[block_of[var as usize] as usize].push(var);
        }
        let mut var_level = vec![NONE; num_vars + 1];
        let mut var_local = vec![NONE; num_vars + 1];
        let mut levels: Vec<Level> = Vec::new();
        let mut pending: Option<(Quantifier, Vec<u32>)> = None;
        for (quantifier, vars) in block_quantifier.iter().copied().zip(block_vars) {
            if vars.is_empty() {
                continue;
            }
            match &mut pending {
                Some((q, acc)) if *q == quantifier => acc.extend(vars),
                _ => {
                    if let Some((q, acc)) = pending.take() {
                        levels.push(Level::new(q, acc));
                    }
                    pending = Some((quantifier, vars));
                }
            }
        }
        if let Some((q, acc)) = pending.take() {
            levels.push(Level::new(q, acc));
        }
        for (index, level) in levels.iter().enumerate() {
            for (local, &var) in level.vars.iter().enumerate() {
                var_level[var as usize] = u32::try_from(index).unwrap_or(NONE);
                var_local[var as usize] = u32::try_from(local).unwrap_or(NONE);
            }
        }
        for clause in &mut clauses {
            clause.sort_by_key(|l| var_level[l.variable().index()]);
        }

        // Occurrence lists.
        let slots = 2 * (num_vars + 1);
        let mut counts = vec![0u32; slots + 1];
        for literal in clauses.iter().flatten() {
            counts[literal_slot(*literal) + 1] += 1;
        }
        for i in 1..counts.len() {
            counts[i] += counts[i - 1];
        }
        let occ_start = counts.clone();
        let mut occ = vec![0u32; counts[slots] as usize];
        let mut cursor = counts;
        for (c, clause) in clauses.iter().enumerate() {
            for literal in clause {
                let slot = literal_slot(*literal);
                occ[cursor[slot] as usize] = c as u32;
                cursor[slot] += 1;
            }
        }

        let num_clauses = clauses.len();
        let mut engine = Self {
            levels,
            clauses,
            var_level,
            var_local,
            occ_start,
            occ,
            sat_level: vec![NONE; num_clauses],
            satisfied_count: 0,
            value: vec![false; num_vars + 1],
        };
        if !engine.load_innermost(deadline) {
            return Prepared::Decided(AbstractionVerdict::Unknown);
        }
        Prepared::Engine(engine)
    }

    /// Give the innermost level every clause: `C|inner ∨ o_C`. Returns false
    /// when `deadline` passed first.
    fn load_innermost(&mut self, deadline: Option<Instant>) -> bool {
        let last = self.levels.len() - 1;
        for c in 0..self.clauses.len() {
            if c % CLOCK_STRIDE == 0 && expired(deadline) {
                return false;
            }
            let c = c as u32;
            let (outer, here) = self.split(c, last);
            let mut sat_clause: Vec<Literal> = here;
            if outer {
                sat_clause.push(self.outer_literal(last, c));
            }
            let level = &mut self.levels[last];
            if sat_clause.is_empty() {
                level.dead = true;
            } else {
                level.sat.add_clause(sat_clause);
            }
        }
        true
    }

    /// Whether clause `c` has a literal outside level `i`, and its level-`i`
    /// literals translated to level `i`'s SAT variables.
    fn split(&self, c: u32, i: usize) -> (bool, Vec<Literal>) {
        let clause = &self.clauses[c as usize];
        let i32_level = u32::try_from(i).unwrap_or(NONE);
        let outer = clause
            .first()
            .is_some_and(|l| self.var_level[l.variable().index()] < i32_level);
        let level = &self.levels[i];
        let here = clause
            .iter()
            .filter(|l| self.var_level[l.variable().index()] == i32_level)
            .map(|l| {
                let var = level.sat_vars[self.var_local[l.variable().index()] as usize];
                if l.is_positive() {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                }
            })
            .collect();
        (outer, here)
    }

    fn outer_literal(&mut self, i: usize, c: u32) -> Literal {
        let level = &mut self.levels[i];
        if let Some(&o) = level.outer_of.get(&c) {
            return o;
        }
        let o = level.fresh(c);
        level.outer_of.insert(c, o);
        level.outer.push((c, o));
        o
    }

    /// Refinement literal of clause `c` at level `i` (created on demand).
    fn selector(&mut self, i: usize, c: u32) -> Option<Literal> {
        if let Some(&s) = self.levels[i].selectors.get(&c) {
            return s;
        }
        let (outer, here) = self.split(c, i);
        let o = outer.then(|| self.outer_literal(i, c));
        let level = &mut self.levels[i];
        let selector = match level.quantifier {
            Quantifier::Exists => {
                if here.is_empty() {
                    o
                } else {
                    let b = level.fresh(NONE);
                    let mut clause = Vec::with_capacity(here.len() + 2);
                    clause.push(b.negated());
                    clause.extend(here);
                    clause.extend(o);
                    level.sat.add_clause(clause);
                    Some(b)
                }
            }
            Quantifier::Forall => {
                if here.is_empty() {
                    o.map(Literal::negated)
                } else {
                    let n = level.fresh(NONE);
                    for l in here {
                        level.sat.add_clause(vec![n.negated(), l.negated()]);
                    }
                    if let Some(o) = o {
                        level.sat.add_clause(vec![n.negated(), o.negated()]);
                    }
                    Some(n)
                }
            }
        };
        level.selectors.insert(c, selector);
        selector
    }

    /// Learn at level `i` from the outcome of level `i + 1`.
    fn refine(&mut self, i: usize, clauses: &[u32]) {
        let mut refinement = Vec::with_capacity(clauses.len());
        for &c in clauses {
            match (self.selector(i, c), self.levels[i].quantifier) {
                (Some(l), _) => refinement.push(l),
                (None, Quantifier::Exists) => {}
                // A constant-true literal: the refinement holds already.
                (None, Quantifier::Forall) => return,
            }
        }
        let level = &mut self.levels[i];
        if refinement.is_empty() {
            level.dead = true;
        } else {
            level.sat.add_clause(refinement);
        }
    }

    /// Query level `i` under the current context.
    fn query(&mut self, i: usize, deadline: Option<Instant>) -> Query {
        let sat_level = &self.sat_level;
        let level = &mut self.levels[i];
        if level.dead {
            return Query::Core(Vec::new());
        }
        let assumptions: Vec<Literal> = match level.quantifier {
            Quantifier::Exists => level
                .outer
                .iter()
                .filter(|(c, _)| sat_level[*c as usize] == NONE)
                .map(|(_, o)| o.negated())
                .collect(),
            Quantifier::Forall => level
                .outer
                .iter()
                .filter(|(c, _)| sat_level[*c as usize] != NONE)
                .map(|(_, o)| *o)
                .collect(),
        };
        let stop = || deadline.is_some_and(|d| Instant::now() >= d);
        match level.sat.solve(&assumptions, &stop) {
            CdclResult::Sat(model) => {
                let mut values = Vec::with_capacity(level.sat_vars.len());
                for var in &level.sat_vars {
                    let Some(&value) = model.get(var.index()) else {
                        return Query::Unknown;
                    };
                    values.push(value);
                }
                Query::Model(values)
            }
            CdclResult::Unsat(core) => {
                let wanted = match level.quantifier {
                    Quantifier::Exists => false,
                    Quantifier::Forall => true,
                };
                let mut clauses = Vec::with_capacity(core.len());
                for literal in core {
                    // Fail closed on a core literal that is not one of this
                    // query's assumptions.
                    let owner = level
                        .owner
                        .get(literal.variable().index())
                        .copied()
                        .unwrap_or(NONE);
                    if owner == NONE || literal.is_positive() != wanted {
                        return Query::Unknown;
                    }
                    let satisfied_outside = sat_level[owner as usize] != NONE;
                    if satisfied_outside != wanted {
                        return Query::Unknown;
                    }
                    clauses.push(owner);
                }
                Query::Core(clauses)
            }
            CdclResult::Unknown => Query::Unknown,
        }
    }

    /// Apply level `i`'s assignment.
    fn apply(&mut self, i: usize, values: &[bool]) {
        let level_id = u32::try_from(i).unwrap_or(NONE);
        let mut newly = std::mem::take(&mut self.levels[i].satisfied);
        for (local, &value) in values.iter().enumerate() {
            let var = Variable::new(self.levels[i].vars[local]);
            self.value[var.index()] = value;
            let literal = if value {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            };
            let slot = literal_slot(literal);
            let (start, end) = (self.occ_start[slot], self.occ_start[slot + 1]);
            for &c in &self.occ[start as usize..end as usize] {
                let entry = &mut self.sat_level[c as usize];
                if *entry == NONE {
                    *entry = level_id;
                    newly.push(c);
                }
            }
        }
        self.satisfied_count += newly.len();
        self.levels[i].satisfied = newly;
    }

    /// Whether level `i`'s applied assignment satisfies clause `c`.
    fn satisfied_at(&self, c: u32, i: usize) -> bool {
        let level_id = u32::try_from(i).unwrap_or(NONE);
        self.clauses[c as usize].iter().any(|l| {
            let v = l.variable().index();
            self.var_level[v] == level_id && self.value[v] == l.is_positive()
        })
    }

    fn undo(&mut self, i: usize) {
        let satisfied = std::mem::take(&mut self.levels[i].satisfied);
        self.satisfied_count -= satisfied.len();
        for &c in &satisfied {
            self.sat_level[c as usize] = NONE;
        }
        let mut satisfied = satisfied;
        satisfied.clear();
        self.levels[i].satisfied = satisfied;
    }

    /// Play the game until a verdict or the deadline.
    pub(crate) fn solve(&mut self, deadline: Option<Instant>) -> AbstractionVerdict {
        let last = self.levels.len() - 1;
        let mut i = 0usize;
        let mut inner: Option<Outcome> = None;
        loop {
            let outcome = match inner.take() {
                None => {
                    if deadline.is_some_and(|d| Instant::now() >= d) {
                        return AbstractionVerdict::Unknown;
                    }
                    match self.query(i, deadline) {
                        Query::Unknown => return AbstractionVerdict::Unknown,
                        Query::Core(core) => match self.levels[i].quantifier {
                            Quantifier::Exists => Outcome::Loss(core),
                            Quantifier::Forall => Outcome::Win(core),
                        },
                        Query::Model(values) => {
                            self.apply(i, &values);
                            if i < last {
                                i += 1;
                                continue;
                            }
                            // Innermost (existential) level: confirm from the
                            // assignment itself that every clause holds.
                            if self.satisfied_count != self.clauses.len() {
                                return AbstractionVerdict::Unknown;
                            }
                            // The clauses this level's assignment leaves to
                            // the outer levels (all satisfied there).
                            let win: Vec<u32> = self.levels[i]
                                .outer
                                .iter()
                                .map(|(c, _)| *c)
                                .filter(|&c| !self.satisfied_at(c, i))
                                .collect();
                            self.undo(i);
                            Outcome::Win(win)
                        }
                    }
                }
                Some(outcome) => {
                    // Level `i` has its assignment applied; `outcome` came
                    // from level `i + 1`.
                    match (self.levels[i].quantifier, outcome) {
                        (Quantifier::Exists, Outcome::Win(w)) => {
                            // Drop what this level's assignment satisfies
                            // itself: the outer levels need not.
                            let w = w
                                .into_iter()
                                .filter(|&c| !self.satisfied_at(c, i))
                                .collect();
                            self.undo(i);
                            Outcome::Win(w)
                        }
                        (Quantifier::Forall, Outcome::Loss(r)) => {
                            self.undo(i);
                            Outcome::Loss(r)
                        }
                        (Quantifier::Exists, Outcome::Loss(r))
                        | (Quantifier::Forall, Outcome::Win(r)) => {
                            self.undo(i);
                            self.refine(i, &r);
                            continue;
                        }
                    }
                }
            };
            if i == 0 {
                return match outcome {
                    Outcome::Win(_) => AbstractionVerdict::True,
                    Outcome::Loss(_) => AbstractionVerdict::False,
                };
            }
            i -= 1;
            inner = Some(outcome);
        }
    }
}

enum Query {
    Model(Vec<bool>),
    Core(Vec<u32>),
    Unknown,
}
