// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! In-memory CNF builder for the finite-domain datatype lane.
//!
//! Literals are DIMACS-style `i32`s; variable 1 is the constant TRUE (a unit
//! clause pins it), so `TRUE = 1` and `FALSE = -1` fold through every gate.
//! Gates are Tseitin definitions (schema 7 of the module doc): each fresh gate
//! variable is fully defined by its inputs, so it can be given the truth value
//! of its defining formula in any model. AND gates are structurally hashed.

use ay_core::kani_compat::DetHashMap as HashMap;

use super::memory::encode_memory_exceeded;

/// A DIMACS literal: `v` or `-v` for variable `v >= 1`.
pub(super) type Lit = i32;
/// The constant-true literal (variable 1, pinned by a unit clause).
pub(super) const TRUE: Lit = 1;
/// The constant-false literal.
pub(super) const FALSE: Lit = -1;

/// One-hot rows longer than this use a sequential (Sinz) at-most-one.
const PAIRWISE_AMO_MAX: usize = 8;

/// Clauses between two memory polls (one poll costs about a microsecond).
const MEMORY_POLL_CLAUSES: usize = 1 << 16;

/// Clause store plus gate memo. Clauses are kept flat (0-terminated).
pub(super) struct Cnf {
    num_vars: u32,
    lits: Vec<i32>,
    clauses: usize,
    max_clauses: usize,
    overflow: bool,
    /// The overflow came from the memory poll, not the clause budget.
    memory_out: bool,
    and_memo: HashMap<Vec<Lit>, Lit>,
}

impl Cnf {
    /// A builder that stops storing clauses (and reports overflow) once more
    /// than `max_clauses` clauses were requested.
    pub(super) fn new(max_clauses: usize) -> Self {
        // The unit clause pinning variable 1 (TRUE) is stored directly: `add`
        // folds every clause containing TRUE away.
        Self {
            num_vars: 1,
            lits: vec![TRUE, 0],
            clauses: 1,
            max_clauses,
            overflow: false,
            memory_out: false,
            and_memo: HashMap::default(),
        }
    }

    /// Whether the encoding stopped on the memory poll.
    pub(super) fn memory_out(&self) -> bool {
        self.memory_out
    }

    /// Stop the encoding because the process is short of memory.
    pub(super) fn set_memory_out(&mut self) {
        self.overflow = true;
        self.memory_out = true;
    }

    /// Drop the clause store and the gate memo once the solver owns a copy
    /// of the clauses (decoding needs neither).
    pub(super) fn release_clauses(&mut self) {
        self.lits = Vec::new();
        self.and_memo = HashMap::default();
    }

    pub(super) fn num_vars(&self) -> u32 {
        self.num_vars
    }

    pub(super) fn num_clauses(&self) -> usize {
        self.clauses
    }

    pub(super) fn overflowed(&self) -> bool {
        self.overflow
    }

    /// Flat 0-terminated clause literals.
    pub(super) fn flat_literals(&self) -> &[i32] {
        &self.lits
    }

    pub(super) fn new_var(&mut self) -> Lit {
        self.num_vars += 1;
        self.num_vars as Lit
    }

    /// Add a clause; constant literals are folded (a TRUE literal drops the
    /// clause, FALSE literals are removed).
    pub(super) fn add(&mut self, clause: &[Lit]) {
        if clause.contains(&TRUE) {
            return;
        }
        if self.clauses >= self.max_clauses || self.overflow {
            self.overflow = true;
            return;
        }
        if self.clauses % MEMORY_POLL_CLAUSES == 0 && encode_memory_exceeded() {
            self.set_memory_out();
            return;
        }
        self.clauses += 1;
        for &l in clause {
            if l != FALSE {
                self.lits.push(l);
            }
        }
        self.lits.push(0);
    }

    /// Tseitin AND (structurally hashed).
    pub(super) fn and(&mut self, inputs: &[Lit]) -> Lit {
        let mut ls: Vec<Lit> = inputs.iter().copied().filter(|&l| l != TRUE).collect();
        if ls.contains(&FALSE) {
            return FALSE;
        }
        ls.sort_unstable();
        ls.dedup();
        if ls.windows(2).any(|w| w[0] == -w[1]) {
            return FALSE;
        }
        match ls.len() {
            0 => return TRUE,
            1 => return ls[0],
            _ => {}
        }
        if let Some(&g) = self.and_memo.get(&ls) {
            return g;
        }
        let g = self.new_var();
        let mut back = Vec::with_capacity(ls.len() + 1);
        back.push(g);
        for &l in &ls {
            self.add(&[-g, l]);
            back.push(-l);
        }
        self.add(&back);
        self.and_memo.insert(ls, g);
        g
    }

    /// Tseitin OR, as a negated AND.
    pub(super) fn or(&mut self, inputs: &[Lit]) -> Lit {
        let neg: Vec<Lit> = inputs.iter().map(|&l| -l).collect();
        -self.and(&neg)
    }

    /// Tseitin biconditional.
    pub(super) fn iff(&mut self, a: Lit, b: Lit) -> Lit {
        if a == b {
            return TRUE;
        }
        if a == -b {
            return FALSE;
        }
        match (a, b) {
            (TRUE, x) | (x, TRUE) => return x,
            (FALSE, x) | (x, FALSE) => return -x,
            _ => {}
        }
        // a <-> b  ==  (a & b) | (!a & !b)
        let both = self.and(&[a, b]);
        let neither = self.and(&[-a, -b]);
        self.or(&[both, neither])
    }

    /// Tseitin if-then-else on literals.
    pub(super) fn ite(&mut self, c: Lit, a: Lit, b: Lit) -> Lit {
        if c == TRUE || a == b {
            return a;
        }
        if c == FALSE {
            return b;
        }
        let then_part = self.and(&[c, a]);
        let else_part = self.and(&[-c, b]);
        self.or(&[then_part, else_part])
    }

    /// `guard -> exactly-one(row)` (unguarded when `guard == TRUE`).
    pub(super) fn exactly_one(&mut self, row: &[Lit], guard: Lit) {
        let mut alo = Vec::with_capacity(row.len() + 1);
        alo.push(-guard);
        alo.extend_from_slice(row);
        self.add(&alo);
        self.at_most_one(row);
    }

    /// At-most-one over `row` (valid unconditionally for one-hot rows whose
    /// absent form is all-false).
    pub(super) fn at_most_one(&mut self, row: &[Lit]) {
        if row.len() <= PAIRWISE_AMO_MAX {
            for i in 0..row.len() {
                for j in (i + 1)..row.len() {
                    self.add(&[-row[i], -row[j]]);
                }
            }
            return;
        }
        // Sequential counter: p_i := "some row[j], j <= i, is true".
        let mut prev: Option<Lit> = None;
        for (i, &l) in row.iter().enumerate() {
            if let Some(p) = prev {
                self.add(&[-l, -p]);
            }
            if i + 1 == row.len() {
                break;
            }
            let p_i = self.new_var();
            self.add(&[-l, p_i]);
            if let Some(p) = prev {
                self.add(&[-p, p_i]);
            }
            prev = Some(p_i);
        }
    }
}
