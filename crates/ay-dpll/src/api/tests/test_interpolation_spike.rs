// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! KEYSTONE SPIKE (campaign rank 4): proof-producing interpolation end-to-end
//! on real CHC-derived UNSAT QF_LIA queries.
//!
//! Goal: determine feasibility + size of proof-based Craig interpolation in
//! AY's internal SMT core. The slice implemented here:
//!
//! 1. Solve with `set_produce_proofs(true)` so the SAT core records the
//!    clause trace (resolution hints) and `build_unsat_proof` reconstructs an
//!    `ay_core::Proof` resolution DAG.
//! 2. Color every proof atom A/B/AB from the assertion partition
//!    (occurrence-based, OpenSMT-style "partition tags").
//! 3. Traverse the proof bottom-up with McMillan labeling:
//!    - input-clause leaves: A-clause -> disjunction of shared literals,
//!      B-clause -> true (clausification tautologies handled per source);
//!    - resolution nodes: A-local pivot -> I1 OR I2, B/shared pivot -> I1 AND I2;
//!    - theory lemmas WITH Farkas certificates (#rank-4 increment 2): the
//!      certificate support's A/B equality systems projected onto the shared
//!      variables (the TermId-level `combine_a_constraints` equivalent),
//!      still validated against the node contract before use;
//!    - uncertified theory lemmas and Trust holes: per-node *validated
//!      stub* — candidate partial interpolants checked against the node
//!      contract (1) A AND not(C|A) |= I, (2) B AND not(C|B) AND I unsat.
//! 4. Verify the final I is a genuine Craig interpolant: (a) A AND (not I)
//!    unsat, (b) I AND B unsat (both checked internally here, plus artifacts
//!    written under the Cargo target root for external z3 + ay verification),
//!    (c) vars(I) within shared(A, B) checked structurally.
//!
//! Two query instances:
//! - `evals/repros/diag_syn2_indstep_k1_MIN.smt2` (the SYNAPSE conservation
//!   core, 51 asserts) with the mandated A = first 40 / B = last 11 split and
//!   a fallback B = {(not v35_1)} split.
//! - a minimal same-class instance (Bool-guarded conservation step) where the
//!   reconstructed proof is expected to be closer to hole-free.
//!
//! Requires the `:ay-proof-no-varsubst` option (set per-solver by the tests;
//! `AY_PROOF_NO_VARSUBST=1` is the process-wide env equivalent): without it
//! the preprocessing variable substitution detaches proof leaves from the
//! original assertions and everything collapses to Trust steps.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{ProofStep, Sort, TermId};

use crate::api::types::{Logic, Term};
use crate::api::Solver;

const BENCH: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../evals/repros/diag_syn2_indstep_k1_MIN.smt2"
));

/// Minimal same-class instance: a Bool-guarded conservation step.
/// Either branch of the guard conserves x + y + z, so the negated
/// conservation goal is UNSAT. This is the shape of one lustre/ctigar
/// induction-step query reduced to a single transition cluster.
const MINI: &str = "\
(set-logic QF_LIA)
(declare-const g Bool)
(declare-const h Bool)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const x1 Int)
(declare-const y1 Int)
(declare-const z1 Int)
(declare-const x2 Int)
(declare-const y2 Int)
(declare-const z2 Int)
(assert (or (not g) (= x1 (+ x 1))))
(assert (or (not g) (= y1 (+ y (- 1)))))
(assert (or g (= x1 x)))
(assert (or g (= y1 y)))
(assert (= z1 z))
(assert (or (not h) (= y2 (+ y1 1))))
(assert (or (not h) (= z2 (+ z1 (- 1)))))
(assert (or h (= y2 y1)))
(assert (or h (= z2 z1)))
(assert (= x2 x1))
(assert (not (= (+ x2 y2 z2) (+ x y z))))
(check-sat)
";

// ============================================================================
// Script helpers (text-level, used for per-node contract validation and for
// the final external verification artifacts)
// ============================================================================

fn assert_lines(src: &str) -> Vec<String> {
    src.lines()
        .filter(|l| l.trim_start().starts_with("(assert"))
        .map(str::to_string)
        .collect()
}

fn decl_lines(src: &str) -> Vec<String> {
    src.lines()
        .filter(|l| {
            let t = l.trim_start();
            t.starts_with("(set-logic") || t.starts_with("(declare-const")
        })
        .map(str::to_string)
        .collect()
}

fn build_script(decls: &[String], asserts: &[String], extra_bodies: &[String]) -> String {
    let mut s = String::new();
    for d in decls {
        s.push_str(d);
        s.push('\n');
    }
    for a in asserts {
        s.push_str(a);
        s.push('\n');
    }
    for body in extra_bodies {
        s.push_str("(assert ");
        s.push_str(body);
        s.push_str(")\n");
    }
    s.push_str("(check-sat)\n");
    s
}

// Check a script with a fresh internal solver; returns "sat"/"unsat"/other.
// (Regular comment: rustdoc ignores doc comments on macro invocations.)
thread_local! {
    /// Set when an interpolant VERIFICATION leg (A&!I / I&B) could not
    /// complete (resource-limited unknown from the process-wide
    /// memory-pressure gate under parallel test loads). Distinguishes
    /// "could not confirm" from "refuted": mandates are skipped on the
    /// former and still fail hard on the latter. Thread-local: libtest
    /// runs each test on its own thread, so tests cannot cross-signal.
    static VERIFY_RESOURCE_LIMITED: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

fn check_script(script: &str) -> String {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
    solver
        .parse_smtlib2(script)
        .expect("verification script parses");
    let r = solver.check_sat();
    if r.is_sat() {
        "sat".to_string()
    } else if r.is_unsat() {
        "unsat".to_string()
    } else {
        // Every test-side verification solve funnels through here; an
        // incomplete answer (resource-limited unknown under parallel test
        // load) must not be read as a refuted contract downstream.
        VERIFY_RESOURCE_LIMITED.with(|f| f.set(true));
        format!("{r:?}")
    }
}

// ============================================================================
// Term analysis
// ============================================================================

fn collect_var_ids(solver: &Solver, tid: TermId, out: &mut HashSet<TermId>) {
    let mut stack = vec![tid];
    let mut seen: HashSet<TermId> = Default::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match solver.terms().get(t) {
            TermData::Var(_, _) => {
                out.insert(t);
            }
            TermData::Const(_) => {}
            _ => {
                for child in solver.terms().children(t) {
                    stack.push(child);
                }
            }
        }
    }
}

/// Collect atomic Boolean leaves: descends through and/or/not/=>/xor,
/// Bool-sorted `=` (iff) and Bool-sorted ite.
fn collect_atoms(solver: &Solver, tid: TermId, out: &mut HashSet<TermId>) {
    let terms = solver.terms();
    match terms.get(tid) {
        TermData::Not(inner) => collect_atoms(solver, *inner, out),
        TermData::App(sym, args) => {
            let name = sym.name();
            let descend = matches!(name, "and" | "or" | "=>" | "xor")
                || (name == "=" && args.first().is_some_and(|a| terms.sort(*a) == &Sort::Bool));
            if descend {
                for &a in args.iter() {
                    collect_atoms(solver, a, out);
                }
            } else {
                out.insert(tid);
            }
        }
        TermData::Ite(c, t, e) if terms.sort(tid) == &Sort::Bool => {
            collect_atoms(solver, *c, out);
            collect_atoms(solver, *t, out);
            collect_atoms(solver, *e, out);
        }
        _ => {
            out.insert(tid);
        }
    }
}

fn atom_of(solver: &Solver, lit: TermId) -> (TermId, bool) {
    match solver.terms().get(lit) {
        TermData::Not(inner) => (*inner, true),
        _ => (lit, false),
    }
}

// ============================================================================
// Partition (the A/B coloring)
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Class {
    A,
    B,
    Ab,
    Unknown,
}

struct Partition {
    a_ids: HashSet<TermId>,
    b_ids: HashSet<TermId>,
    a_atoms: HashSet<TermId>,
    b_atoms: HashSet<TermId>,
    a_vars: HashSet<TermId>,
    b_vars: HashSet<TermId>,
    shared_vars: HashSet<TermId>,
    decls: Vec<String>,
    a_lines: Vec<String>,
    b_lines: Vec<String>,
    /// Negations of unit B-asserts whose vars are all shared — candidate
    /// disjuncts for stub partial interpolants ("the B side rules this out").
    b_unit_negs: Vec<(String, Vec<TermId>)>,
}

impl Partition {
    fn new(solver: &Solver, src: &str, asserts: &[Term], a_count: usize) -> Self {
        let (a_terms, b_terms) = asserts.split_at(a_count);
        let mut a_ids: HashSet<TermId> = Default::default();
        let mut b_ids: HashSet<TermId> = Default::default();
        let mut a_atoms: HashSet<TermId> = Default::default();
        let mut b_atoms: HashSet<TermId> = Default::default();
        let mut a_vars: HashSet<TermId> = Default::default();
        let mut b_vars: HashSet<TermId> = Default::default();
        for t in a_terms {
            a_ids.insert(t.0);
            collect_atoms(solver, t.0, &mut a_atoms);
            collect_var_ids(solver, t.0, &mut a_vars);
        }
        for t in b_terms {
            b_ids.insert(t.0);
            collect_atoms(solver, t.0, &mut b_atoms);
            collect_var_ids(solver, t.0, &mut b_vars);
        }
        let shared_vars: HashSet<TermId> = a_vars.intersection(&b_vars).copied().collect();

        let mut b_unit_negs = Vec::new();
        for t in b_terms {
            let (atom, negated) = atom_of(solver, t.0);
            // Unit B-assert (a literal at the top level).
            if b_atoms.contains(&atom) {
                let mut vars: HashSet<TermId> = Default::default();
                collect_var_ids(solver, atom, &mut vars);
                if !vars.is_empty() && vars.iter().all(|v| shared_vars.contains(v)) {
                    let neg_text = if negated {
                        solver.format_term(Term(atom))
                    } else {
                        format!("(not {})", solver.format_term(Term(atom)))
                    };
                    b_unit_negs.push((neg_text, vars.into_iter().collect()));
                }
            }
        }

        let all_lines = assert_lines(src);
        assert_eq!(all_lines.len(), asserts.len(), "assert text/term mismatch");
        Self {
            a_ids,
            b_ids,
            a_atoms,
            b_atoms,
            a_vars,
            b_vars,
            shared_vars,
            decls: decl_lines(src),
            a_lines: all_lines[..a_count].to_vec(),
            b_lines: all_lines[a_count..].to_vec(),
            b_unit_negs,
        }
    }

    fn class_of_atom(&self, solver: &Solver, atom: TermId) -> Class {
        match (self.a_atoms.contains(&atom), self.b_atoms.contains(&atom)) {
            (true, true) => Class::Ab,
            (true, false) => Class::A,
            (false, true) => Class::B,
            (false, false) => {
                // Synthetic atom (e.g. a clausification or-term): color by
                // assertion membership, then by variable occurrence.
                if self.a_ids.contains(&atom) {
                    return Class::A;
                }
                if self.b_ids.contains(&atom) {
                    return Class::B;
                }
                let mut vars: HashSet<TermId> = Default::default();
                collect_var_ids(solver, atom, &mut vars);
                if vars.is_empty() {
                    return Class::Ab;
                }
                if vars.iter().all(|v| self.shared_vars.contains(v)) {
                    Class::Ab
                } else if vars.iter().all(|v| self.a_vars.contains(v)) {
                    Class::A
                } else if vars.iter().all(|v| self.b_vars.contains(v)) {
                    Class::B
                } else {
                    Class::Unknown
                }
            }
        }
    }
}

// ============================================================================
// Partial interpolants
// ============================================================================

#[derive(Clone, Debug)]
enum Itp {
    Tru,
    Fls,
    /// A proof literal (kept by TermId so vars can be collected structurally).
    Lit(TermId),
    /// A raw SMT-LIB body with its variable set (for B-unit negations).
    Raw(String, Vec<TermId>),
    Or(Vec<Itp>),
    And(Vec<Itp>),
}

impl Itp {
    fn or2(a: Itp, b: Itp) -> Itp {
        match (a, b) {
            (Itp::Tru, _) | (_, Itp::Tru) => Itp::Tru,
            (Itp::Fls, x) | (x, Itp::Fls) => x,
            (Itp::Or(mut xs), Itp::Or(ys)) => {
                xs.extend(ys);
                Itp::Or(xs)
            }
            (Itp::Or(mut xs), y) | (y, Itp::Or(mut xs)) => {
                xs.push(y);
                Itp::Or(xs)
            }
            (x, y) => Itp::Or(vec![x, y]),
        }
    }

    fn and2(a: Itp, b: Itp) -> Itp {
        match (a, b) {
            (Itp::Fls, _) | (_, Itp::Fls) => Itp::Fls,
            (Itp::Tru, x) | (x, Itp::Tru) => x,
            (Itp::And(mut xs), Itp::And(ys)) => {
                xs.extend(ys);
                Itp::And(xs)
            }
            (Itp::And(mut xs), y) | (y, Itp::And(mut xs)) => {
                xs.push(y);
                Itp::And(xs)
            }
            (x, y) => Itp::And(vec![x, y]),
        }
    }

    fn or_all(items: Vec<Itp>) -> Itp {
        items.into_iter().fold(Itp::Fls, Itp::or2)
    }

    fn text(&self, solver: &Solver) -> String {
        match self {
            Itp::Tru => "true".to_string(),
            Itp::Fls => "false".to_string(),
            Itp::Lit(t) => solver.format_term(Term(*t)),
            Itp::Raw(s, _) => s.clone(),
            Itp::Or(xs) => {
                let parts: Vec<String> = xs.iter().map(|x| x.text(solver)).collect();
                format!("(or {})", parts.join(" "))
            }
            Itp::And(xs) => {
                let parts: Vec<String> = xs.iter().map(|x| x.text(solver)).collect();
                format!("(and {})", parts.join(" "))
            }
        }
    }

    fn vars(&self, solver: &Solver, out: &mut HashSet<TermId>) {
        match self {
            Itp::Tru | Itp::Fls => {}
            Itp::Lit(t) => collect_var_ids(solver, *t, out),
            Itp::Raw(_, vs) => out.extend(vs.iter().copied()),
            Itp::Or(xs) | Itp::And(xs) => {
                for x in xs {
                    x.vars(solver, out);
                }
            }
        }
    }

    fn is_const(&self) -> bool {
        matches!(self, Itp::Tru | Itp::Fls)
    }
}

// ============================================================================
// The validated-leaf McMillan traversal
// ============================================================================

/// A linear equation `sum c_i*x_i = k` over Int variables.
type LinRow = (HashMap<TermId, i128>, i128);

struct SpikeStats {
    stub_nodes: usize,
    stub_solves: usize,
    /// Theory-lemma leaves interpolated from their Farkas certificate
    /// (#rank-4 increment 2) — the certificate support's A/B projection,
    /// validated against the node contract before use.
    cert_nodes: usize,
    cert_solves: usize,
    leaf_nodes: usize,
    resolution_nodes: usize,
}

struct Interpolator<'a> {
    solver: &'a Solver,
    part: &'a Partition,
    stats: SpikeStats,
    /// Cache stub results by clause text key (Trust + Or step pairs repeat).
    stub_cache: HashMap<String, Option<Itp>>,
    /// Cache certificate-leaf results by clause text key.
    cert_cache: HashMap<String, Option<Itp>>,
    verbose: bool,
}

impl<'a> Interpolator<'a> {
    fn new(solver: &'a Solver, part: &'a Partition, verbose: bool) -> Self {
        Self {
            solver,
            part,
            stats: SpikeStats {
                stub_nodes: 0,
                stub_solves: 0,
                cert_nodes: 0,
                cert_solves: 0,
                leaf_nodes: 0,
                resolution_nodes: 0,
            },
            stub_cache: Default::default(),
            cert_cache: Default::default(),
            verbose,
        }
    }

    fn lit_class(&self, lit: TermId) -> Class {
        let (atom, _) = atom_of(self.solver, lit);
        self.part.class_of_atom(self.solver, atom)
    }

    /// McMillan A-clause leaf rule: disjunction of B/AB-colored literals
    /// whose variables are all shared.
    fn a_leaf_itp(&self, clause: &[TermId]) -> Itp {
        let mut parts = Vec::new();
        for &lit in clause {
            if matches!(self.lit_class(lit), Class::B | Class::Ab) {
                let mut vars: HashSet<TermId> = Default::default();
                collect_var_ids(self.solver, lit, &mut vars);
                if vars.iter().all(|v| self.part.shared_vars.contains(v)) {
                    parts.push(Itp::Lit(lit));
                }
            }
        }
        Itp::or_all(parts)
    }

    /// Determine the source partition of an input-shaped clause:
    /// the clause is an assert itself, contains an assert's or-term as a
    /// literal (clausification tautology), or is a single asserted literal.
    fn source_side(&self, step: &ProofStep, clause: &[TermId]) -> Option<Class> {
        if let ProofStep::Assume(lit) = step {
            if self.part.a_ids.contains(lit) {
                return Some(Class::A);
            }
            if self.part.b_ids.contains(lit) {
                return Some(Class::B);
            }
        }
        let mut found = None;
        for &lit in clause {
            let (atom, _) = atom_of(self.solver, lit);
            let side = if self.part.a_ids.contains(&atom) {
                Some(Class::A)
            } else if self.part.b_ids.contains(&atom) {
                Some(Class::B)
            } else {
                None
            };
            if let Some(s) = side {
                match found {
                    None => found = Some(s),
                    Some(prev) if prev == s => {}
                    Some(_) => return None, // mixed sources: not input-shaped
                }
            }
        }
        found
    }

    /// Parse an Int term as a linear form: var-coefficient map + constant.
    /// Supports Var, Const(Int), +, binary/unary -, and Const*Var products.
    fn linear_of(
        &self,
        tid: TermId,
        sign: i64,
        coeffs: &mut HashMap<TermId, i64>,
        constant: &mut i64,
    ) -> bool {
        use ay_core::term::Constant;
        match self.solver.terms().get(tid) {
            TermData::Var(_, _) => {
                *coeffs.entry(tid).or_insert(0) += sign;
                true
            }
            TermData::Const(Constant::Int(c)) => {
                let Ok(c64) = i64::try_from(c.clone()) else {
                    return false;
                };
                *constant += sign * c64;
                true
            }
            TermData::App(sym, args) => match sym.name() {
                "+" => args
                    .iter()
                    .all(|&a| self.linear_of(a, sign, coeffs, constant)),
                "-" if args.len() == 1 => self.linear_of(args[0], -sign, coeffs, constant),
                "-" if !args.is_empty() => {
                    if !self.linear_of(args[0], sign, coeffs, constant) {
                        return false;
                    }
                    args[1..]
                        .iter()
                        .all(|&a| self.linear_of(a, -sign, coeffs, constant))
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// Implied shared-variable equality candidates from the A-side equality
    /// literals of a theory-lemma clause (#rank-4 increment 1).
    ///
    /// The Bool-guarded equality-network conflicts of the lustre class are
    /// linear equality systems (difference chains plus conservation rows).
    /// Their Craig interpolants across a cut are the A-side rows with the
    /// A-local variables eliminated — exactly the Farkas A-projection for an
    /// equality system. This runs a small fraction-free Gaussian elimination
    /// over the A-side equations of the clause, eliminating every non-shared
    /// variable, and emits the surviving shared-only equations as candidates;
    /// every candidate is still verified against the node contract before
    /// use (validated-stub discipline).
    fn parse_equality(&self, eq_atom: TermId) -> Option<LinRow> {
        let TermData::App(sym, args) = self.solver.terms().get(eq_atom) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        if self.solver.terms().sort(args[0]) != &Sort::Int {
            return None;
        }
        let mut coeffs: HashMap<TermId, i64> = Default::default();
        let mut constant = 0i64;
        if !self.linear_of(args[0], 1, &mut coeffs, &mut constant)
            || !self.linear_of(args[1], -1, &mut coeffs, &mut constant)
        {
            return None;
        }
        // lhs - rhs = 0  =>  sum c_i*x_i = -constant
        let row: HashMap<TermId, i128> = coeffs
            .into_iter()
            .filter(|(_, c)| *c != 0)
            .map(|(v, c)| (v, i128::from(c)))
            .collect();
        (!row.is_empty()).then_some((row, -i128::from(constant)))
    }

    /// Equations asserted by `not(C|side)`: the side's negated equality
    /// literals become asserted equalities. For the A side, the
    /// unconditional unit equality assertions of partition A are added
    /// (A entails them, so node contract (1) still holds for anything the
    /// combined system implies).
    fn side_rows(&self, clause: &[TermId], a_side: bool) -> Vec<LinRow> {
        let mut rows: Vec<LinRow> = Vec::new();
        for &lit in clause {
            let class = self.lit_class(lit);
            let on_side = if a_side {
                matches!(class, Class::A | Class::Unknown)
            } else {
                matches!(class, Class::B | Class::Ab)
            };
            if !on_side {
                continue;
            }
            let (atom, negated) = atom_of(self.solver, lit);
            if !negated {
                continue; // only negated equalities assert equations
            }
            if let Some(row) = self.parse_equality(atom) {
                rows.push(row);
            }
        }
        if a_side && !rows.is_empty() {
            for &aid in self.part.a_ids.iter() {
                if let Some(row) = self.parse_equality(aid) {
                    rows.push(row);
                }
            }
        }
        rows
    }

    /// Fraction-free Gaussian elimination of every non-shared variable;
    /// returns the surviving shared-only equations.
    fn eliminate_local_vars(&self, mut rows: Vec<LinRow>) -> Vec<LinRow> {
        fn gcd(a: i128, b: i128) -> i128 {
            let (mut a, mut b) = (a.abs(), b.abs());
            while b != 0 {
                (a, b) = (b, a % b);
            }
            a
        }
        fn normalize(row: &mut LinRow) {
            row.0.retain(|_, c| *c != 0);
            let mut g = row.1.abs();
            for &c in row.0.values() {
                g = gcd(g, c);
            }
            if g > 1 {
                for c in row.0.values_mut() {
                    *c /= g;
                }
                row.1 /= g;
            }
        }

        let local_vars: Vec<TermId> = {
            let mut vs: Vec<TermId> = rows
                .iter()
                .flat_map(|(m, _)| m.keys().copied())
                .filter(|v| !self.part.shared_vars.contains(v))
                .collect();
            vs.sort_unstable();
            vs.dedup();
            vs
        };
        for v in local_vars {
            let Some(pivot_idx) = rows.iter().position(|(m, _)| m.contains_key(&v)) else {
                continue;
            };
            let pivot = rows.remove(pivot_idx);
            let pc = pivot.0[&v];
            for row in rows.iter_mut() {
                let Some(&rc) = row.0.get(&v) else { continue };
                // row := row*pc - pivot*rc
                for c in row.0.values_mut() {
                    *c *= pc;
                }
                row.1 *= pc;
                for (&pv, &pcoef) in pivot.0.iter() {
                    *row.0.entry(pv).or_insert(0) -= pcoef * rc;
                }
                row.1 -= pivot.1 * rc;
                normalize(row);
            }
        }
        rows.retain(|(m, _)| !m.is_empty());
        rows
    }

    /// Render a shared-only equation row as SMT-LIB text plus its variables.
    fn row_text(&self, row: &LinRow) -> (String, Vec<TermId>) {
        let (m, k) = row;
        let mut terms: Vec<(TermId, i128)> = m.iter().map(|(&v, &c)| (v, c)).collect();
        terms.sort_unstable_by_key(|(v, _)| *v);
        let int_text = |i: i128| {
            if i < 0 {
                format!("(- {})", -i)
            } else {
                i.to_string()
            }
        };
        let parts: Vec<String> = terms
            .iter()
            .map(|&(v, c)| {
                let name = self.solver.format_term(Term(v));
                if c == 1 {
                    name
                } else {
                    format!("(* {} {})", int_text(c), name)
                }
            })
            .collect();
        let sum = if parts.len() == 1 {
            parts[0].clone()
        } else {
            format!("(+ {})", parts.join(" "))
        };
        (
            format!("(= {sum} {})", int_text(*k)),
            terms.iter().map(|&(v, _)| v).collect(),
        )
    }

    /// Candidate partial interpolants from the equality structure of a
    /// theory-lemma clause:
    /// - the A-side shared projection rows (each entailed by A ∧ not(C|A)),
    /// - the negated conjunction of the B-side shared projection rows
    ///   (contradicted by not(C|B), entailment from A verified by solving).
    fn eq_chain_candidates(&self, clause: &[TermId]) -> (Vec<Itp>, Option<Itp>) {
        let a_rows = self.eliminate_local_vars(self.side_rows(clause, true));
        let mut a_cands = Vec::new();
        let mut seen: HashSet<String> = Default::default();
        for row in &a_rows {
            let (text, vars) = self.row_text(row);
            if seen.insert(text.clone()) {
                a_cands.push(Itp::Raw(text, vars));
            }
            if a_cands.len() >= 24 {
                break;
            }
        }

        let b_rows = self.eliminate_local_vars(self.side_rows(clause, false));
        let b_neg = if b_rows.is_empty() {
            None
        } else {
            let rendered: Vec<(String, Vec<TermId>)> =
                b_rows.iter().take(24).map(|r| self.row_text(r)).collect();
            let vars: Vec<TermId> = rendered.iter().flat_map(|(_, vs)| vs.clone()).collect();
            let text = if rendered.len() == 1 {
                format!("(not {})", rendered[0].0)
            } else {
                let parts: Vec<&str> = rendered.iter().map(|(t, _)| t.as_str()).collect();
                format!("(not (and {}))", parts.join(" "))
            };
            Some(Itp::Raw(text, vars))
        };

        (a_cands, b_neg)
    }

    /// Canonical cache key for a clause (sorted literal texts).
    fn clause_key(&self, clause: &[TermId]) -> String {
        let mut lits: Vec<String> = clause
            .iter()
            .map(|&l| self.solver.format_term(Term(l)))
            .collect();
        lits.sort();
        lits.join("|")
    }

    /// `not(C|A)` and `not(C|B)` assertion bodies for the node contract.
    fn side_negations(&self, clause: &[TermId]) -> (Vec<String>, Vec<String>) {
        let mut neg_a_side = Vec::new();
        let mut neg_b_side = Vec::new();
        for &lit in clause {
            let text = format!("(not {})", self.solver.format_term(Term(lit)));
            match self.lit_class(lit) {
                Class::A | Class::Unknown => neg_a_side.push(text),
                Class::B | Class::Ab => neg_b_side.push(text),
            }
        }
        (neg_a_side, neg_b_side)
    }

    /// Node contract for clause C with partial interpolant I (McMillan,
    /// shared literals on the B side):
    ///   (1) A AND not(C|A) |= I        (C|A = A-colored literals)
    ///   (2) B AND not(C|B) AND I unsat (C|B = B/AB-colored literals)
    /// Any I over shared variables satisfying (1)+(2) is a sound partial
    /// interpolant regardless of how the clause was derived.
    fn candidate_meets_contract(
        &mut self,
        cand: &Itp,
        neg_a_side: &[String],
        neg_b_side: &[String],
        cert: bool,
    ) -> bool {
        let cand_text = cand.text(self.solver);
        let count = |stats: &mut SpikeStats| {
            if cert {
                stats.cert_solves += 1;
            } else {
                stats.stub_solves += 1;
            }
        };
        // (1) A AND not(C|A) AND not(I) must be UNSAT.
        let ok1 = if matches!(cand, Itp::Tru) {
            true
        } else {
            let mut extra = neg_a_side.to_vec();
            extra.push(format!("(not {cand_text})"));
            count(&mut self.stats);
            check_script(&build_script(&self.part.decls, &self.part.a_lines, &extra)) == "unsat"
        };
        if !ok1 {
            return false;
        }
        // (2) B AND not(C|B) AND I must be UNSAT.
        if matches!(cand, Itp::Fls) {
            return true;
        }
        let mut extra = neg_b_side.to_vec();
        extra.push(cand_text);
        count(&mut self.stats);
        check_script(&build_script(&self.part.decls, &self.part.b_lines, &extra)) == "unsat"
    }

    /// Certificate-based partial interpolant for a Farkas-annotated theory
    /// lemma (#rank-4 increment 2) — the TermId-level equivalent of ay-chc's
    /// `combine_a_constraints`: restrict to the certificate's support
    /// (nonzero coefficients), split the asserted constraints A/B, and
    /// project each side's equality system onto the shared variables
    /// (fraction-free elimination plays the role of the consumer's equality
    /// orientation search; the certificate fixes WHICH constraints
    /// participate). Candidates still verify against the node contract
    /// before use.
    fn cert_itp(&mut self, clause: &[TermId], farkas: &ay_core::FarkasAnnotation) -> Option<Itp> {
        if farkas.coefficients.len() != clause.len() {
            return None;
        }
        let cache_key = self.clause_key(clause);
        if let Some(cached) = self.cert_cache.get(&cache_key) {
            return cached.clone();
        }

        let zero = num_rational::Rational64::from(0);
        let mut a_rows: Vec<LinRow> = Vec::new();
        let mut b_rows: Vec<LinRow> = Vec::new();
        let mut support_in_a = 0usize;
        let mut support_in_b = 0usize;
        let mut parsed_ok = true;
        for (&lit, coef) in clause.iter().zip(farkas.coefficients.iter()) {
            if *coef == zero {
                continue;
            }
            let side_a = matches!(self.lit_class(lit), Class::A | Class::Unknown);
            if side_a {
                support_in_a += 1;
            } else {
                support_in_b += 1;
            }
            let (atom, negated) = atom_of(self.solver, lit);
            if !negated {
                // The conflict asserts the NEGATION of this positive clause
                // literal — a disequality. It contributes no equality row;
                // the other side's projection carries the certificate.
                continue;
            }
            let Some(row) = self.parse_equality(atom) else {
                parsed_ok = false;
                break;
            };
            if side_a {
                a_rows.push(row);
            } else {
                b_rows.push(row);
            }
        }
        if !parsed_ok {
            self.cert_cache.insert(cache_key, None);
            return None;
        }

        // Shared projections of each side's support.
        let a_shared = self.eliminate_local_vars(a_rows.clone());
        let b_shared = self.eliminate_local_vars(b_rows.clone());
        let a_conj = if a_rows.is_empty() {
            Some(Itp::Fls)
        } else if a_shared.is_empty() {
            None
        } else {
            let rows: Vec<Itp> = a_shared
                .iter()
                .map(|r| {
                    let (text, vars) = self.row_text(r);
                    Itp::Raw(text, vars)
                })
                .collect();
            Some(if rows.len() == 1 {
                rows.into_iter().next().expect("len checked")
            } else {
                Itp::And(rows)
            })
        };
        let b_neg = if b_shared.is_empty() {
            None
        } else {
            let rendered: Vec<(String, Vec<TermId>)> =
                b_shared.iter().map(|r| self.row_text(r)).collect();
            let vars: Vec<TermId> = rendered.iter().flat_map(|(_, vs)| vs.clone()).collect();
            let text = if rendered.len() == 1 {
                format!("(not {})", rendered[0].0)
            } else {
                let parts: Vec<&str> = rendered.iter().map(|(t, _)| t.as_str()).collect();
                format!("(not (and {}))", parts.join(" "))
            };
            Some(Itp::Raw(text, vars))
        };

        let mut candidates: Vec<Itp> = Vec::new();
        if support_in_b == 0 && support_in_a > 0 {
            // The entire certificate support is A-colored: the conflict is
            // refuted inside A ∧ ¬(C|A), so FALSE is the certificate's
            // partial interpolant (strongest first).
            candidates.push(Itp::Fls);
        }
        if let Some(a) = &a_conj {
            candidates.push(a.clone());
        }
        if let Some(b) = &b_neg {
            candidates.push(b.clone());
        }
        if let (Some(a), Some(b)) = (&a_conj, &b_neg) {
            candidates.push(Itp::or2(a.clone(), b.clone()));
        }
        if support_in_a == 0 && support_in_b > 0 {
            // The entire support is B-colored: TRUE is the certificate's
            // partial interpolant (the refutation lives in B ∧ ¬(C|B)).
            candidates.push(Itp::Tru);
        }
        candidates.dedup_by_key(|c| c.text(self.solver));

        let (neg_a_side, neg_b_side) = self.side_negations(clause);
        for cand in candidates {
            if self.candidate_meets_contract(&cand, &neg_a_side, &neg_b_side, true) {
                if self.verbose {
                    eprintln!("[cert] |C|={} -> {}", clause.len(), cand.text(self.solver));
                }
                self.stats.cert_nodes += 1;
                self.cert_cache.insert(cache_key, Some(cand.clone()));
                return Some(cand);
            }
        }
        if self.verbose {
            eprintln!(
                "[cert] FAILED for |C|={} (falling back to stub)",
                clause.len()
            );
        }
        self.cert_cache.insert(cache_key, None);
        None
    }

    /// Validated stub for theory lemmas and Trust holes (see
    /// `candidate_meets_contract` for the node contract).
    fn stub_itp(&mut self, clause: &[TermId]) -> Option<Itp> {
        let cache_key = self.clause_key(clause);
        if let Some(cached) = self.stub_cache.get(&cache_key) {
            return cached.clone();
        }
        self.stats.stub_nodes += 1;

        let (neg_a_side, neg_b_side) = self.side_negations(clause);

        // Candidate partial interpolants, strongest first.
        let d = self.a_leaf_itp(clause);
        let d_with_units = {
            let unit_disjuncts: Vec<Itp> = self
                .part
                .b_unit_negs
                .iter()
                .map(|(text, vars)| Itp::Raw(text.clone(), vars.clone()))
                .collect();
            Itp::or2(d.clone(), Itp::or_all(unit_disjuncts))
        };
        // Implied shared equalities from the lemma's equality structure
        // (#rank-4 increment 1): the genuine theory interpolants for the
        // lustre-class equality-network lemmas (A-side shared projections
        // and the negated B-side shared projection).
        let (chain, b_neg) = self.eq_chain_candidates(clause);
        let mut candidates = vec![Itp::Fls, d.clone()];
        if chain.len() >= 2 {
            candidates.push(Itp::And(chain.clone()));
        }
        candidates.extend(chain.iter().cloned());
        if let Some(bn) = &b_neg {
            candidates.push(bn.clone());
            candidates.push(Itp::or2(d.clone(), bn.clone()));
            // Weakened with the B-unit disjuncts: needed when the Trust leaf
            // is not a self-contained theory fact (guarded-equality lemmas)
            // and its entailment from A flows through a shared guard literal.
            candidates.push(Itp::or2(d_with_units.clone(), bn.clone()));
        }
        for c in &chain {
            candidates.push(Itp::or2(d.clone(), c.clone()));
        }
        if chain.len() >= 2 {
            candidates.push(Itp::or2(d_with_units.clone(), Itp::And(chain.clone())));
        }
        candidates.push(d_with_units);
        candidates.push(Itp::Tru);
        candidates.dedup_by_key(|c| c.text(self.solver));

        for cand in candidates {
            if self.candidate_meets_contract(&cand, &neg_a_side, &neg_b_side, false) {
                if self.verbose {
                    eprintln!("[stub] |C|={} -> {}", clause.len(), cand.text(self.solver));
                }
                self.stub_cache.insert(cache_key, Some(cand.clone()));
                return Some(cand);
            }
        }
        if self.verbose {
            let lits: Vec<String> = clause
                .iter()
                .map(|&l| {
                    format!(
                        "{:?}:{}",
                        self.lit_class(l),
                        self.solver.format_term(Term(l))
                    )
                })
                .collect();
            eprintln!("[stub] FAILED for clause {lits:?}");
        }
        self.stub_cache.insert(cache_key, None);
        None
    }

    fn interpolate(&mut self, proof: &ay_core::Proof) -> Option<Itp> {
        let mut partial: Vec<Option<Itp>> = Vec::with_capacity(proof.steps.len());
        for step in proof.steps.iter() {
            let itp = match step {
                ProofStep::Resolution {
                    pivot,
                    clause1,
                    clause2,
                    ..
                } => {
                    self.stats.resolution_nodes += 1;
                    let i1 = partial.get(clause1.0 as usize).and_then(Clone::clone);
                    let i2 = partial.get(clause2.0 as usize).and_then(Clone::clone);
                    match (i1, i2) {
                        (Some(i1), Some(i2)) => {
                            let (atom, _) = atom_of(self.solver, *pivot);
                            match self.part.class_of_atom(self.solver, atom) {
                                Class::A => Some(Itp::or2(i1, i2)),
                                // McMillan: shared pivots resolve on the B side.
                                Class::B | Class::Ab => Some(Itp::and2(i1, i2)),
                                Class::Unknown => {
                                    if self.verbose {
                                        eprintln!(
                                            "[itp] unknown pivot class: {}",
                                            self.solver.format_term(Term(*pivot))
                                        );
                                    }
                                    None
                                }
                            }
                        }
                        _ => None,
                    }
                }
                ProofStep::Assume(lit) => {
                    self.stats.leaf_nodes += 1;
                    let clause = [*lit];
                    match self.source_side(step, &clause) {
                        Some(Class::A) => Some(self.a_leaf_itp(&clause)),
                        Some(Class::B) => Some(Itp::Tru),
                        _ => self.stub_itp(&clause),
                    }
                }
                ProofStep::TheoryLemma { clause, farkas, .. } => {
                    // Certificate-based leaf first (#rank-4 increment 2);
                    // validated-stub fallback for uncertified lemmas.
                    let cert = farkas.as_ref().and_then(|f| {
                        let f = f.clone();
                        self.cert_itp(clause, &f)
                    });
                    match cert {
                        Some(itp) => Some(itp),
                        None => self.stub_itp(clause),
                    }
                }
                ProofStep::Step { clause, .. } => {
                    // Input-shaped clauses (clausification tautologies carrying
                    // an assert's or-term) get the leaf rule; everything else
                    // (Trust holes, theory conflict clauses, expanded lemma
                    // clauses) goes through the validated stub.
                    match self.source_side(step, clause) {
                        Some(Class::A) => {
                            self.stats.leaf_nodes += 1;
                            Some(self.a_leaf_itp(clause))
                        }
                        Some(Class::B) => {
                            self.stats.leaf_nodes += 1;
                            Some(Itp::Tru)
                        }
                        _ => self.stub_itp(clause),
                    }
                }
                _ => None,
            };
            // A hole we cannot interpolate: bail honestly.
            partial.push(Some(itp?));
        }
        partial.last().and_then(Clone::clone)
    }
}

// ============================================================================
// Shared spike driver
// ============================================================================

struct SpikeOutcome {
    itp_text: String,
    itp_is_const: bool,
    shared_var_names: Vec<String>,
    check_a_script: String,
    check_b_script: String,
}

/// Proof-shape statistics from the reconstructed UNSAT proof.
struct ProofShape {
    /// Trust steps with premises: failed hint-replay fallbacks (the rank-4
    /// increment 1 target — must be zero after RUP replay).
    trusts_with_premises: usize,
    /// Premiseless Trust leaves. Increment 1 left ~18 of these on the
    /// captured solve (theory conflict clauses whose level-0-minimized SAT
    /// form no longer matched the recorded lemma); the increment-2
    /// minimized-lemma bridge resolves them against the level-0 units, so
    /// this must now be zero on the captured instances.
    trust_leaves: usize,
    /// `TheoryLemma` leaves carrying a Farkas certificate (the increment-2
    /// LIA affine certificates).
    theory_lemmas_with_farkas: usize,
    /// `TheoryLemma` leaves without a certificate (stub-bridged).
    theory_lemmas_uncertified: usize,
    resolutions: usize,
    /// The empty clause is derived by a genuine step (Resolution or a
    /// non-Trust rule), not a Trust hole.
    empty_clause_genuine: bool,
    /// Traversal: leaves interpolated from their Farkas certificate.
    cert_leaves: usize,
    /// Traversal: leaves that needed a solver-validated stub.
    stub_leaves: usize,
    /// PRODUCTION path (rank-4 inc-4): `get_interpolant_with_strength`
    /// (Strongest/McMillan) produced an interpolant that passed the same
    /// A&!I / I&B / shared-vars verification as the test-side traversal.
    prod_verified: bool,
    /// PRODUCTION path: certificate leaves served by
    /// `interpolant_farkas::certificate_lemma_interpolant` in that call.
    prod_cert_served: usize,
}

/// Run the full slice on `src` with the first `a_count` asserts as A.
/// Returns the proof shape plus Some on a *verified* Craig interpolant.
fn run_spike(label: &str, src: &str, a_count: usize) -> (ProofShape, Option<SpikeOutcome>) {
    VERIFY_RESOURCE_LIMITED.with(|f| f.set(false));
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
    solver.set_produce_proofs(true);
    // The preprocessing variable substitution must be off for proof-based
    // interpolation (see module docs). Solver-local option (with the
    // AY_PROOF_NO_VARSUBST env var as the process-wide equivalent); only
    // affects solves with produce_proofs enabled.
    solver.set_option(":ay-proof-no-varsubst", "true");
    let asserts: Vec<Term> = solver.parse_smtlib2(src).expect("benchmark parses");
    assert!(
        a_count > 0 && a_count < asserts.len(),
        "split is degenerate"
    );

    let t0 = ay_core::time::Instant::now();
    let result = solver.check_sat();
    let solve_time = t0.elapsed();
    assert!(result.is_unsat(), "{label}: expected UNSAT, got {result:?}");

    let proof = solver.last_proof().expect("proof produced").clone();
    let mut resolutions = 0usize;
    let mut trusts_with_premises = 0usize;
    let mut trust_leaves = 0usize;
    let mut theory_lemmas = 0usize;
    let mut theory_lemmas_with_farkas = 0usize;
    let mut empty_clause_genuine = false;
    for step in proof.steps.iter() {
        match step {
            ProofStep::Resolution { clause, .. } => {
                resolutions += 1;
                if clause.is_empty() {
                    empty_clause_genuine = true;
                }
            }
            ProofStep::TheoryLemma { farkas, .. } => {
                theory_lemmas += 1;
                if farkas.is_some() {
                    theory_lemmas_with_farkas += 1;
                }
            }
            ProofStep::Step {
                rule,
                clause,
                premises,
                ..
            } => {
                if format!("{rule:?}") == "Trust" {
                    if premises.is_empty() {
                        trust_leaves += 1;
                    } else {
                        trusts_with_premises += 1;
                    }
                } else if clause.is_empty() && !premises.is_empty() {
                    empty_clause_genuine = true;
                }
            }
            _ => {}
        }
    }
    eprintln!(
        "[spike:{label}] solve={solve_time:?} proof: steps={} resolutions={resolutions} \
         trust_with_premises={trusts_with_premises} trust_leaves={trust_leaves} \
         theory_lemmas={theory_lemmas} (with_farkas={theory_lemmas_with_farkas}) \
         empty_genuine={empty_clause_genuine}",
        proof.steps.len()
    );
    if std::env::var("AY_SPIKE_DUMP").is_ok() {
        for (i, step) in proof.steps.iter().enumerate() {
            let desc = match step {
                ProofStep::Assume(t) => format!("Assume {}", solver.format_term(Term(*t))),
                ProofStep::Resolution { .. } => continue,
                ProofStep::TheoryLemma {
                    kind,
                    farkas,
                    clause,
                    ..
                } => format!(
                    "TheoryLemma kind={kind:?} farkas={} |C|={} {:?}",
                    farkas.is_some(),
                    clause.len(),
                    clause
                        .iter()
                        .map(|&l| solver.format_term(Term(l)))
                        .collect::<Vec<_>>()
                ),
                ProofStep::Step {
                    rule,
                    premises,
                    clause,
                    ..
                } => {
                    if !matches!(rule, ay_core::AletheRule::Trust) {
                        continue;
                    }
                    format!(
                        "Step rule={rule:?} premises={} |C|={} {:?}",
                        premises.len(),
                        clause.len(),
                        clause
                            .iter()
                            .map(|&l| solver.format_term(Term(l)))
                            .collect::<Vec<_>>()
                    )
                }
                _ => continue,
            };
            eprintln!("[dump:{label}] step {i}: {desc}");
        }
    }
    let mut shape = ProofShape {
        trusts_with_premises,
        trust_leaves,
        theory_lemmas_with_farkas,
        theory_lemmas_uncertified: theory_lemmas - theory_lemmas_with_farkas,
        resolutions,
        empty_clause_genuine,
        cert_leaves: 0,
        stub_leaves: 0,
        prod_verified: false,
        prod_cert_served: 0,
    };

    let part = Partition::new(&solver, src, &asserts, a_count);
    assert!(!part.shared_vars.is_empty(), "A and B must share variables");

    // Non-degenerate split sanity: A alone and B alone must be SAT, so
    // trivial interpolants cannot verify.
    assert_eq!(
        check_script(&build_script(&part.decls, &part.a_lines, &[])),
        "sat",
        "{label}: A side must be SAT alone"
    );
    assert_eq!(
        check_script(&build_script(&part.decls, &part.b_lines, &[])),
        "sat",
        "{label}: B side must be SAT alone"
    );

    let verbose = std::env::var("AY_SPIKE_VERBOSE").is_ok();
    let mut interp = Interpolator::new(&solver, &part, verbose);
    let t1 = ay_core::time::Instant::now();
    let itp = interp.interpolate(&proof);
    let itp_time = t1.elapsed();
    shape.cert_leaves = interp.stats.cert_nodes;
    shape.stub_leaves = interp.stats.stub_nodes;
    let outcome = (|| {
        eprintln!(
            "[spike:{label}] traversal: {:?} leaf={} res={} cert={} cert_solves={} \
             stub={} stub_solves={} -> {}",
            itp_time,
            interp.stats.leaf_nodes,
            interp.stats.resolution_nodes,
            interp.stats.cert_nodes,
            interp.stats.cert_solves,
            interp.stats.stub_nodes,
            interp.stats.stub_solves,
            itp.as_ref().map_or("FAILED".to_string(), |i| {
                let t = i.text(&solver);
                if t.len() > 200 {
                    format!("{}... ({} chars)", &t[..200], t.len())
                } else {
                    t
                }
            })
        );
        let itp = itp?;

        // (c) structural: vars(I) within shared(A, B).
        let mut itp_vars: HashSet<TermId> = Default::default();
        itp.vars(&solver, &mut itp_vars);
        let non_shared: Vec<String> = itp_vars
            .difference(&part.shared_vars)
            .map(|v| solver.format_term(Term(*v)))
            .collect();
        if !non_shared.is_empty() {
            eprintln!("[spike:{label}] REJECT: non-shared vars {non_shared:?}");
            return None;
        }

        // (a) A AND not(I) unsat, (b) I AND B unsat — internal verification.
        let itp_text = itp.text(&solver);
        let check_a_script =
            build_script(&part.decls, &part.a_lines, &[format!("(not {itp_text})")]);
        let check_b_script =
            build_script(&part.decls, &part.b_lines, std::slice::from_ref(&itp_text));
        let ra = check_script(&check_a_script);
        let rb = check_script(&check_b_script);
        eprintln!("[spike:{label}] verify: A&!I={ra} I&B={rb}");
        if ra != "unsat" || rb != "unsat" {
            // A leg answering neither sat nor unsat could not COMPLETE
            // (resource-limited); record that so mandates can skip instead
            // of reading an unconfirmable interpolant as a regression.
            let completed = |v: &str| v == "sat" || v == "unsat";
            if !completed(&ra) || !completed(&rb) {
                VERIFY_RESOURCE_LIMITED.with(|f| f.set(true));
            }
            return None;
        }

        let mut shared_var_names: Vec<String> = part
            .shared_vars
            .iter()
            .map(|v| solver.format_term(Term(*v)))
            .collect();
        shared_var_names.sort();

        Some(SpikeOutcome {
            itp_is_const: itp.is_const(),
            itp_text,
            shared_var_names,
            check_a_script,
            check_b_script,
        })
    })();

    // PRODUCTION PATH (rank-4 inc-4): the farkas-leaf interpolation now lives
    // in the production traversal (`interpolant_farkas::
    // certificate_lemma_interpolant` called by `get_interpolant`). Run the
    // production `get_interpolant_with_strength` (Strongest = McMillan, the
    // system this spike validates) on the same solver/proof and verify the
    // result with the SAME scripts; the test-side traversal above remains as
    // a cross-check.
    {
        let a_terms: Vec<Term> = asserts[..a_count].to_vec();
        let b_terms: Vec<Term> = asserts[a_count..].to_vec();
        let result = solver.get_interpolant_with_strength(
            &a_terms,
            &b_terms,
            crate::api::types::InterpolantStrength::Strongest,
        );
        let cert_stats = crate::api::solving::interpolant_farkas::last_cert_leaf_stats();
        shape.prod_cert_served = cert_stats.served;
        match result {
            None => {
                eprintln!(
                    "[spike:{label}] production: get_interpolant=None \
                     cert(attempted={} verified={} served={})",
                    cert_stats.attempted, cert_stats.verified, cert_stats.served
                );
            }
            Some(res) => {
                let tid = res.interpolant().0;
                let mut vars: HashSet<TermId> = Default::default();
                collect_var_ids(&solver, tid, &mut vars);
                let non_shared = vars.difference(&part.shared_vars).count();
                let i_text = solver.format_term(Term(tid));
                let ra = check_script(&build_script(
                    &part.decls,
                    &part.a_lines,
                    &[format!("(not {i_text})")],
                ));
                let rb = check_script(&build_script(
                    &part.decls,
                    &part.b_lines,
                    std::slice::from_ref(&i_text),
                ));
                shape.prod_verified = non_shared == 0 && ra == "unsat" && rb == "unsat";
                eprintln!(
                    "[spike:{label}] production: A&!I={ra} I&B={rb} non_shared_vars={non_shared} \
                     cert(attempted={} verified={} served={}) itp_chars={}",
                    cert_stats.attempted,
                    cert_stats.verified,
                    cert_stats.served,
                    i_text.len()
                );
            }
        }
    }

    (shape, outcome)
}

fn interpolation_spike_artifact_dir() -> std::path::PathBuf {
    let workspace = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("crate should live under repo/crates/ay-dpll")
        .to_path_buf();
    ay_test_support::cargo_target_root(&workspace)
        .join("dpll-preflight-artifacts")
        .join("interpolation-spike")
}

fn write_artifacts(name: &str, label: &str, a_count: usize, total: usize, out: &SpikeOutcome) {
    let artifact_dir = interpolation_spike_artifact_dir();
    std::fs::create_dir_all(&artifact_dir).expect("create artifact dir");
    std::fs::write(
        artifact_dir.join(format!("{name}_interpolant.txt")),
        format!(
            "; Craig interpolant ({label})\n\
             ; A = asserts 1-{a_count}, B = asserts {}-{total}\n\
             ; shared vars: {:?}\n\
             ; verify: check_a_implies_i.smt2 (A & !I) and check_i_and_b.smt2 (I & B) must both be unsat\n\
             {}\n",
            a_count + 1,
            out.shared_var_names,
            out.itp_text
        ),
    )
    .expect("write interpolant artifact");
    std::fs::write(
        artifact_dir.join(format!("{name}_check_a_implies_i.smt2")),
        &out.check_a_script,
    )
    .expect("write A&!I artifact");
    std::fs::write(
        artifact_dir.join(format!("{name}_check_i_and_b.smt2")),
        &out.check_b_script,
    )
    .expect("write I&B artifact");
    eprintln!(
        "[spike:{label}] artifacts written to {}/{name}_*",
        artifact_dir.display()
    );
}

// ============================================================================
// Tests
// ============================================================================

/// Minimal same-class instance: the proof should be (near) hole-free, the
/// traversal genuinely resolution-driven, and the interpolant non-trivial.
#[test]
fn test_interpolation_spike_mini_conservation() {
    let mini_asserts = assert_lines(MINI).len();
    // A = the guarded transition (all but the goal), B = negated conservation.
    let (shape, out) = run_spike("mini", MINI, mini_asserts - 1);
    let out = out.expect("mini conservation instance must produce a verified interpolant");
    assert!(
        !out.itp_is_const,
        "mini interpolant must be non-trivial, got {}",
        out.itp_text
    );
    assert_eq!(
        shape.trusts_with_premises, 0,
        "no learned-clause derivation may fall back to Trust with RUP hint replay \
         (#rank-4 increment 1); remaining Trust leaves are uncertified theory lemmas"
    );
    assert_eq!(
        shape.trust_leaves, 0,
        "theory conflict clauses must reach the proof as TheoryLemma leaves \
         (#rank-4 increment 2 minimized-lemma bridge), not demoted Trust assumes"
    );
    assert!(
        shape.empty_clause_genuine,
        "the empty clause must be derived by a genuine step, not a Trust hole"
    );
    write_artifacts(
        "mini",
        "mini-conservation",
        mini_asserts - 1,
        mini_asserts,
        &out,
    );
}

/// Always-on replay of the minimized interpolation capture through every
/// production strength.  Each returned candidate is independently checked for
/// A=>I, I∧B unsatisfiability, and shared-symbol purity.
///
/// This replaces the former env/file-only diagnostic: the regression now
/// exercises real interpolation behavior in every test run.
#[test]
fn test_interpolation_builtin_repro_all_strengths_verify() {
    let src = MINI;
    let a_count = assert_lines(src)
        .len()
        .checked_sub(1)
        .expect("mini repro must contain an A and B partition");

    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
    solver.set_produce_proofs(true);
    solver.set_option(":ay-proof-no-varsubst", "true");
    let asserts: Vec<Term> = solver.parse_smtlib2(src).expect("repro parses");
    assert!(a_count > 0 && a_count < asserts.len(), "split degenerate");
    let result = solver.check_sat();
    assert!(result.is_unsat(), "repro must be UNSAT, got {result:?}");

    let part = Partition::new(&solver, src, &asserts, a_count);
    let a_terms: Vec<Term> = asserts[..a_count].to_vec();
    let b_terms: Vec<Term> = asserts[a_count..].to_vec();

    let mut verified_any = false;
    for (name, strength) in [
        ("pudlak", crate::api::types::InterpolantStrength::Default),
        (
            "mcmillan",
            crate::api::types::InterpolantStrength::Strongest,
        ),
        ("mcmillan'", crate::api::types::InterpolantStrength::Weakest),
    ] {
        let res = solver.get_interpolant_with_strength(&a_terms, &b_terms, strength);
        let cert_stats = crate::api::solving::interpolant_farkas::last_cert_leaf_stats();
        match res {
            None => eprintln!(
                "[repro:{name}] get_interpolant=None cert(attempted={} verified={} served={})",
                cert_stats.attempted, cert_stats.verified, cert_stats.served
            ),
            Some(res) => {
                let tid = res.interpolant().0;
                let mut vars: HashSet<TermId> = Default::default();
                collect_var_ids(&solver, tid, &mut vars);
                let non_shared = vars.difference(&part.shared_vars).count();
                let i_text = solver.format_term(Term(tid));
                let ra = check_script(&build_script(
                    &part.decls,
                    &part.a_lines,
                    &[format!("(not {i_text})")],
                ));
                let rb = check_script(&build_script(
                    &part.decls,
                    &part.b_lines,
                    std::slice::from_ref(&i_text),
                ));
                let ok = non_shared == 0 && ra == "unsat" && rb == "unsat";
                verified_any |= ok;
                assert!(
                    ok,
                    "{name} returned a non-Craig candidate: A&!I={ra}, I&B={rb}, \
                     non_shared_vars={non_shared}, I={i_text}"
                );
                eprintln!(
                    "[repro:{name}] A&!I={ra} I&B={rb} non_shared_vars={non_shared} \
                     verified={ok} cert(attempted={} verified={} served={}) itp_chars={}",
                    cert_stats.attempted,
                    cert_stats.verified,
                    cert_stats.served,
                    i_text.len()
                );
            }
        }
    }
    assert!(
        verified_any,
        "no strength produced a verified Craig interpolant on the captured query"
    );
}

/// The committed SYNAPSE conservation core with the mandated A/B split
/// (A = first 40 asserts, B = last 11) and the goal-only split.
///
/// KEYSTONE gate for rank-4 increment 1: before RUP-style hint replay, the
/// reconstructed proof for this instance had ~10/87 learned-clause Trust
/// fallbacks INCLUDING the empty-clause closure — which blocked the 40/11
/// split. Both splits must now verify; all learned clauses (and the empty
/// clause) must derive via genuine resolution.
///
/// KEYSTONE gate for rank-4 increment 2 (real Farkas certificates): the
/// increment-1 proof bridged ~39 leaves per split with solver-validated
/// stubs (18 premiseless Trust leaves from level-0-minimized theory
/// conflicts + 21 theory-lemma clauses without usable certificates). With
/// the LIA affine Gaussian-multiplier certificates and the minimized-lemma
/// bridge: zero Trust leaves, every theory lemma on this solve carries a
/// Farkas certificate, and the traversal interpolates those leaves from the
/// certificates (validated against the node contract — still
/// verify-before-use), leaving at most a handful of stub-bridged nodes
/// (measured: 1 per split, was 39).
#[test]
fn test_interpolation_spike_synapse_conservation_core() {
    let (shape, mandated) = run_spike("synapse-40/11", BENCH, 40);
    assert_eq!(
        shape.trusts_with_premises, 0,
        "learned-clause derivations must not fall back to Trust \
         (was ~10/87 incl. the empty-clause closure before RUP replay)"
    );
    assert_eq!(
        shape.trust_leaves, 0,
        "level-0-minimized theory conflicts must bridge back to their \
         recorded certified lemmas (was 18 premiseless Trust leaves)"
    );
    assert!(
        shape.empty_clause_genuine,
        "the empty clause must be derived by genuine resolution, not a Trust hole"
    );
    assert!(
        shape.resolutions > 0,
        "the reconstructed proof must contain genuine resolution steps"
    );
    assert!(
        shape.theory_lemmas_with_farkas >= 10,
        "the affine LIA conflicts on this solve must carry Farkas \
         certificates (measured 21, got {})",
        shape.theory_lemmas_with_farkas
    );
    assert_eq!(
        shape.theory_lemmas_uncertified, 0,
        "every theory-lemma leaf on the captured solve must be certified \
         (demote_uncertified_arithmetic_lemmas_to_trust stays as fallback only)"
    );
    assert!(
        shape.cert_leaves >= 10,
        "theory-lemma leaves must interpolate from their certificates \
         (measured 21, got {})",
        shape.cert_leaves
    );
    assert!(
        shape.stub_leaves <= 7,
        "stub-bridged leaves must drop >=80% from the ~39 increment-1 \
         baseline (measured 1, got {})",
        shape.stub_leaves
    );
    if mandated.is_none() && VERIFY_RESOURCE_LIMITED.with(|f| f.get()) {
        eprintln!(
            "[spike:synapse-40/11] SKIP mandate: interpolant verification \
             could not complete under resource pressure (honest unknown)"
        );
        return;
    }
    let mandated =
        mandated.expect("the mandated 40/11 split must yield a verified Craig interpolant");
    write_artifacts("synapse_40_11", "synapse-40/11", 40, 51, &mandated);

    // PRODUCTION gate (rank-4 inc-4): `get_interpolant_with_strength` must
    // now interpolate the farkas leaves from their certificates IN PRODUCTION
    // (interpolant_farkas) and produce a verified Craig interpolant on this
    // split; the traversal above remains the test-side cross-check.
    assert!(
        shape.prod_cert_served >= 10,
        "production traversal must interpolate the certified theory lemmas \
         from their certificates (measured 21, got {})",
        shape.prod_cert_served
    );
    assert!(
        shape.prod_verified,
        "the production get_interpolant result must verify (A&!I unsat, I&B \
         unsat, shared vars) on the 40/11 split"
    );

    // Goal-only split: B = the negated goal. The interpolant is forced to be
    // over the goal literal; exercises coloring, traversal, certificate
    // leaves, stub validation, and verification on a different cut of the
    // same proof.
    let (goal_shape, fallback) = run_spike("synapse-goal", BENCH, 50);
    assert_eq!(
        goal_shape.trusts_with_premises, 0,
        "goal-split proof must have no hint-replay Trust fallbacks"
    );
    assert_eq!(
        goal_shape.trust_leaves, 0,
        "goal-split proof must have no premiseless Trust leaves"
    );
    assert!(
        goal_shape.cert_leaves >= 10,
        "goal split must interpolate theory lemmas from certificates \
         (measured 21, got {})",
        goal_shape.cert_leaves
    );
    assert!(
        goal_shape.stub_leaves <= 7,
        "goal-split stub leaves must drop >=80% from the ~39 baseline \
         (measured 1, got {})",
        goal_shape.stub_leaves
    );
    let fallback = fallback.expect("the goal split must yield a verified Craig interpolant");
    write_artifacts("synapse_goal", "synapse-goal", 50, 51, &fallback);

    // PRODUCTION gate (rank-4 inc-4) on the goal split.
    assert!(
        goal_shape.prod_cert_served >= 10,
        "production traversal must interpolate the certified theory lemmas \
         on the goal split (measured 21, got {})",
        goal_shape.prod_cert_served
    );
    assert!(
        goal_shape.prod_verified,
        "the production get_interpolant result must verify on the goal split"
    );
}
