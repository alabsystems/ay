// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clausal local search for QF_NIA (`#nia-clausal-sls`) — **SAT-only**.
//!
//! ## Provenance
//!
//! This is a transliteration of z3 5.0.0's `src/ast/sls/sls_arith_clausal.cpp`
//! (MIT-licensed, "Theory plugin for arithmetic local search based on clausal
//! search as used in HybridSMT (nia_ls)", N. Bjorner 2025-01-16) together with
//! the move-generation and update machinery it calls in `sls_arith_base.cpp`
//! and the weight-transfer scheme of `sat_ddfw.cpp`. Correspondence:
//!
//! | z3                                          | here                          |
//! |---------------------------------------------|-------------------------------|
//! | `arith_clausal::search`                     | [`Search::run`]               |
//! | `arith_clausal::move_arith_variable`        | [`Search::move_arith_variable`]|
//! | `arith_clausal::add_lookahead_on_unsat_vars`| [`Search::lookahead_unsat`]   |
//! | `arith_clausal::add_lookahead_on_false_literals` | [`Search::lookahead_false_lits`] |
//! | `arith_clausal::critical_move_on_updates`   | [`Search::critical_move_on_updates`] |
//! | `arith_clausal::lookahead`                  | [`Search::lookahead_one`]     |
//! | `arith_clausal::critical_move`              | [`Search::critical_move`]     |
//! | `arith_clausal::get_score`                  | [`Search::score_of`]          |
//! | `arith_clausal::check_restart`              | [`Search::check_restart`]     |
//! | `arith_base::find_linear_moves`             | [`Search::find_linear_moves`] |
//! | `arith_base::find_quadratic_moves`          | [`Search::find_quadratic_moves`] |
//! | `arith_base::is_linear` / `is_quadratic`    | [`Search::is_linear`] / [`Search::is_quadratic`] |
//! | `arith_base::is_permitted_update` / `add_update` | [`Search::add_update`]   |
//! | `arith_base::can_update_num`                | [`Search::can_update`]        |
//! | `ddfw::shift_weights` / `transfer_weight`   | [`Search::shift_weights`]     |
//!
//! **Deliberate specialization.** z3's loop alternates a Boolean mode (a `ddfw`
//! flip over genuine Boolean variables) with an arithmetic mode. QF_NIA
//! benchmarks of the target shape (VeryMax/AProVE termination VCs) have *no*
//! Boolean variables — every literal is an arithmetic atom — so z3's own
//! `bool_in_unsat == 0` branch would put it in arithmetic mode permanently.
//! This port implements the arithmetic mode plus the `ddfw` weight transfer and
//! declines (returns `None`) on any formula whose clausification would need
//! genuine Boolean variables. The Boolean mode is therefore *absent*, not
//! *approximated*.
//!
//! ## Soundness
//!
//! Local search **cannot refute**. This module never returns `Unsat` and never
//! records a conflict — the only two outcomes are `Some(TheoryResult::Sat)`
//! (with an exactly-verified witness) and `None` (no claim). Concretely:
//!
//! 1. Every candidate assignment that drives the clause set to zero unsatisfied
//!    clauses is re-verified from scratch by [`NiaSolver::eval_formula_exact`],
//!    an exact `BigInt` evaluator over the **original assertion formulas** —
//!    not over the local-search encoding, and not over the linearized
//!    relaxation. It is fail-closed: any construct it cannot evaluate yields
//!    `None` and the witness is discarded.
//! 2. Only after that does the witness reach `record_bounded_enum_model`, whose
//!    output the executor still puts through `finalize_sat_model_validation`
//!    (the strict independent model gate) before any `sat` is printed.
//! 3. Every internal arithmetic operation that can feed a witness is checked
//!    (`checked_*` on `i128`); overflow sets `self.overflow` and aborts the search
//!    rather than producing a value. Note `[profile.release]` sets
//!    `overflow-checks = true`, so an *unchecked* op here would PANIC rather than
//!    wrap — a crash, not a wrong answer, but still a hard failure on adversarial
//!    input, which is why the monomial-delta subtraction and the tie-break
//!    magnitude below are folded into the checked path too. The one deliberate
//!    exception is that tie-break, which saturates to `i128::MAX` instead of
//!    aborting: it only ORDERS candidate moves and can never reach a witness.
//!
//! A bug anywhere in the search heuristics can therefore cost completeness
//! (a missed `sat`) or time, but cannot produce a wrong verdict.

use num_bigint::BigInt;
use num_traits::{One, ToPrimitive};
use std::collections::BTreeMap;

use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::{Sort, TheoryResult};

use super::{HashMap, NiaSolver};

// ---------------------------------------------------------------------------
// Budgets — every one of these is a completeness-only knob (#nia-clausal-sls).
// ---------------------------------------------------------------------------

/// Maximum clauses produced by the (distributive) clausification.
const MAX_CLAUSES: usize = 600_000;
/// Maximum clauses a single `or` may distribute into.
const MAX_OR_PRODUCT: usize = 250_000;
/// Maximum distinct arithmetic atoms.
const MAX_ATOMS: usize = 40_000;
/// Maximum monomials in one atom's polynomial (guards polynomial blow-up).
const MAX_MONOMIALS: usize = 512;
/// Maximum integer variables the search will handle.
const MAX_VARS: usize = 4_000;
/// Search step budget per invocation. Effectively unbounded — the wall budget
/// (see `BUDGET_FRACTION`) is what actually stops the search; this only bounds
/// a pathological deadline-free call.
const MAX_STEPS: u64 = 50_000_000;
/// Steps without a new best cost before a restart (z3 uses 500_000 against an
/// unbounded wall; our lane runs inside a shared per-file budget).
const RESTART_AFTER: u64 = 20_000;
/// `var_info::in_range` half-width. z3 starts at 1e8 and grows adaptively; we
/// keep it fixed so every reachable value stays exactly `i64`-representable
/// (`check_assignment` and `record_bounded_enum_model` take `i64`).
const VALUE_RANGE: i128 = 100_000_000;
/// ddfw initial clause weight (`sat_ddfw.h: m_init_weight = 2`).
const INIT_WEIGHT: f64 = 2.0;
/// Atom-set size above which `add_lookahead_on_false_literals` samples instead
/// of scanning (z3: `bool is_big = sz > 45u`).
const BIG_ATOM_SET: usize = 45;
/// Poll the wall deadline every this many steps.
const DEADLINE_POLL_STEPS: u64 = 64;
/// Fallback fraction of the REMAINING wall the lane may consume when no shared
/// cutoff was installed (see `NiaSolver::set_local_search_deadline`). The lane
/// is a last resort, but the caller still has to finish, print and (for `sat`)
/// re-validate the model through the independent gate, so it must never eat the
/// whole deadline.
const BUDGET_FRACTION: u32 = 60;

// ---------------------------------------------------------------------------
// Polynomial / atom representation (z3: `arith_base::ineq`)
// ---------------------------------------------------------------------------

type VarIdx = u32;

/// One monomial `coeff * prod(var^power)`. An empty `vars` is the constant.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Mono {
    coeff: i128,
    /// Sorted by `VarIdx`, powers >= 1.
    vars: Vec<(VarIdx, u32)>,
}

/// `sum(monos) OP 0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Op {
    /// `sum <= 0`
    Le,
    /// `sum < 0`
    Lt,
    /// `sum == 0`
    Eq,
}

/// One occurrence of a variable inside an atom (z3: `nonlinear_coeff`).
#[derive(Debug, Clone, Copy)]
struct NlCoeff {
    /// Index into `Atom::monos`.
    mono: u32,
    /// Coefficient of that monomial in the atom.
    coeff: i128,
    /// Power of the variable inside that monomial.
    power: u32,
}

#[derive(Debug)]
struct Atom {
    monos: Vec<Mono>,
    op: Op,
    /// Cached value of each monomial under the current assignment.
    mono_val: Vec<i128>,
    /// Cached `sum(mono_val)`.
    value: i128,
    /// Cached truth of `value OP 0`.
    truth: bool,
    /// z3's `ineq::m_nonlinear`: per-variable summary of its occurrences.
    occ: Vec<(VarIdx, Vec<NlCoeff>)>,
    /// Clauses this atom occurs in, with the literal sign.
    lit_occ: Vec<(u32, bool)>,
}

impl Atom {
    fn eval_truth(value: i128, op: Op) -> bool {
        match op {
            Op::Le => value <= 0,
            Op::Lt => value < 0,
            Op::Eq => value == 0,
        }
    }
}

/// A clause literal: `negated == true` means the atom must be FALSE.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Lit {
    atom: u32,
    negated: bool,
}

#[derive(Debug)]
struct Clause {
    lits: Vec<Lit>,
    weight: f64,
    num_true: u32,
}

#[derive(Debug, Default, Clone)]
struct VarInfo {
    value: i128,
    lo: Option<i128>,
    hi: Option<i128>,
    /// `(atom, mono)` pairs to refresh when this variable changes.
    mono_occ: Vec<(u32, u32)>,
    /// Distinct atoms mentioning this variable.
    atoms: Vec<u32>,
    /// Distinct clauses mentioning this variable (z3: `m_clauses_of`).
    clauses: Vec<u32>,
    /// z3 `var_info::m_tabu_pos` / `m_tabu_neg`.
    tabu_pos: u64,
    tabu_neg: u64,
    /// z3 `var_info::m_last_pos` / `m_last_neg`.
    last_pos: u64,
    last_neg: u64,
}

impl VarInfo {
    fn is_tabu(&self, step: u64, delta: i128) -> bool {
        if delta > 0 {
            self.tabu_pos > step
        } else {
            self.tabu_neg > step
        }
    }
    fn last_step(&self, delta: i128) -> u64 {
        if delta > 0 {
            self.last_pos
        } else {
            self.last_neg
        }
    }
    fn set_step(&mut self, step: u64, tabu_step: u64, delta: i128) {
        if delta > 0 {
            self.tabu_pos = tabu_step;
            self.last_pos = step;
        } else {
            self.tabu_neg = tabu_step;
            self.last_neg = step;
        }
    }
    fn is_fixed(&self) -> bool {
        matches!((self.lo, self.hi), (Some(l), Some(h)) if l == h)
    }
}

/// Deterministic xorshift64* — the search must be reproducible run to run.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next() % n as u64) as usize
        }
    }
}

// ---------------------------------------------------------------------------
// Clausification
// ---------------------------------------------------------------------------

/// Builder that turns the original assertion formulas into
/// (atoms, clauses, variables). Declines (`None`) on anything outside the
/// supported fragment — a completeness-only restriction.
struct Builder<'t> {
    terms: &'t ay_core::term::TermStore,
    var_of: HashMap<TermId, VarIdx>,
    var_term: Vec<TermId>,
    atom_of: HashMap<(Vec<(i128, Vec<(VarIdx, u32)>)>, Op), u32>,
    atoms: Vec<Atom>,
    /// First reason clausification declined, for the debug channel only.
    decline: Option<String>,
}

type Poly = Vec<Mono>;

impl<'t> Builder<'t> {
    fn new(terms: &'t ay_core::term::TermStore) -> Self {
        Self {
            terms,
            var_of: HashMap::default(),
            var_term: Vec::new(),
            atom_of: HashMap::default(),
            atoms: Vec::new(),
            decline: None,
        }
    }

    fn decline(&mut self, why: impl FnOnce() -> String) -> Option<Lit> {
        if self.decline.is_none() {
            self.decline = Some(why());
        }
        None
    }

    fn var(&mut self, t: TermId) -> Option<VarIdx> {
        if let Some(&v) = self.var_of.get(&t) {
            return Some(v);
        }
        if self.var_term.len() >= MAX_VARS {
            return None;
        }
        let v = self.var_term.len() as VarIdx;
        self.var_of.insert(t, v);
        self.var_term.push(t);
        Some(v)
    }

    /// Exact polynomial of an integer term. `None` on any unsupported operator,
    /// non-integer constant, or size blow-up.
    fn poly(&mut self, t: TermId) -> Option<Poly> {
        match self.terms.get(t) {
            TermData::Var(_, _) if matches!(self.terms.sort(t), Sort::Int) => {
                let v = self.var(t)?;
                Some(vec![Mono {
                    coeff: 1,
                    vars: vec![(v, 1)],
                }])
            }
            TermData::Const(Constant::Int(n)) => {
                let c = n.to_i128()?;
                Some(if c == 0 {
                    Vec::new()
                } else {
                    vec![Mono {
                        coeff: c,
                        vars: Vec::new(),
                    }]
                })
            }
            TermData::Const(Constant::Rational(r)) if r.0.denom().is_one() => {
                let c = r.0.numer().to_i128()?;
                Some(if c == 0 {
                    Vec::new()
                } else {
                    vec![Mono {
                        coeff: c,
                        vars: Vec::new(),
                    }]
                })
            }
            TermData::App(Symbol::Named(name), args) => {
                let args = args.clone();
                match name.as_str() {
                    "+" => {
                        let mut acc: Poly = Vec::new();
                        for a in args {
                            let p = self.poly(a)?;
                            acc = add_poly(acc, p)?;
                        }
                        Some(acc)
                    }
                    "-" if args.len() == 1 => {
                        let p = self.poly(args[0])?;
                        Some(neg_poly(p))
                    }
                    "-" if args.len() >= 2 => {
                        let mut acc = self.poly(args[0])?;
                        for a in &args[1..] {
                            let p = self.poly(*a)?;
                            acc = add_poly(acc, neg_poly(p))?;
                        }
                        Some(acc)
                    }
                    "*" => {
                        let mut acc: Poly = vec![Mono {
                            coeff: 1,
                            vars: Vec::new(),
                        }];
                        for a in args {
                            let p = self.poly(a)?;
                            acc = mul_poly(&acc, &p)?;
                        }
                        Some(acc)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Intern the atom `poly OP 0`. Returns its index.
    fn intern_atom(&mut self, poly: Poly, op: Op) -> Option<u32> {
        let key: Vec<(i128, Vec<(VarIdx, u32)>)> =
            poly.iter().map(|m| (m.coeff, m.vars.clone())).collect();
        if let Some(&a) = self.atom_of.get(&(key.clone(), op)) {
            return Some(a);
        }
        if self.atoms.len() >= MAX_ATOMS {
            return None;
        }
        let idx = self.atoms.len() as u32;
        // z3 `ineq::m_nonlinear`: group the variable occurrences.
        let mut occ_map: BTreeMap<VarIdx, Vec<NlCoeff>> = BTreeMap::new();
        for (mi, m) in poly.iter().enumerate() {
            for &(v, p) in &m.vars {
                occ_map.entry(v).or_default().push(NlCoeff {
                    mono: mi as u32,
                    coeff: m.coeff,
                    power: p,
                });
            }
        }
        // z3 sorts each occurrence list by power (`nl.p < nl.p`).
        let occ: Vec<(VarIdx, Vec<NlCoeff>)> = occ_map
            .into_iter()
            .map(|(v, mut l)| {
                l.sort_by_key(|c| c.power);
                (v, l)
            })
            .collect();
        let n = poly.len();
        self.atoms.push(Atom {
            monos: poly,
            op,
            mono_val: vec![0; n],
            value: 0,
            truth: false,
            occ,
            lit_occ: Vec::new(),
        });
        self.atom_of.insert((key, op), idx);
        Some(idx)
    }

    /// Clausify an atom application into a single literal.
    fn atom_lit(&mut self, t: TermId, positive: bool) -> Option<Lit> {
        let TermData::App(Symbol::Named(name), args) = self.terms.get(t) else {
            return self.decline(|| format!("non-application atom {t:?}"));
        };
        if args.len() != 2 {
            let n = args.len();
            let name = name.clone();
            return self.decline(|| format!("{name}/{n} is not a binary relation"));
        }
        let (a, b) = (args[0], args[1]);
        if !matches!(self.terms.sort(a), Sort::Int) || !matches!(self.terms.sort(b), Sort::Int) {
            let name = name.clone();
            let sa = format!("{:?}", self.terms.sort(a));
            let sb = format!("{:?}", self.terms.sort(b));
            return self.decline(|| format!("({name} {sa} {sb}) is not an Int relation"));
        }
        let name = name.clone();
        let Some(pa) = self.poly(a) else {
            return self.decline(|| format!("lhs of ({name} ..) is not a polynomial"));
        };
        let Some(pb) = self.poly(b) else {
            return self.decline(|| format!("rhs of ({name} ..) is not a polynomial"));
        };
        let Some(diff) = add_poly(pa, neg_poly(pb)) else {
            return self.decline(|| format!("({name} ..) polynomial too large"));
        }; // a - b
           // Each SMT relation becomes `p OP 0`; `positive == false` flips the
           // literal sign, never the atom (mirrors z3, where the Boolean variable
           // always tracks `ineq::is_true()` and the clause literal carries sign).
           //
           // Strict integer inequalities are normalized away (`p < 0` <=> `p+1 <= 0`)
           // so `Op::Lt` never arises for Int atoms — matching z3, whose quadratic
           // move generator asserts `!is_int(x)` on every `LT` branch.
        let one = vec![Mono {
            coeff: 1,
            vars: Vec::new(),
        }];
        let (poly, op, neg) = match name.as_str() {
            "<=" => (diff, Op::Le, !positive),
            "<" => match add_poly(diff, one) {
                Some(p) => (p, Op::Le, !positive),
                None => return self.decline(|| "polynomial too large".to_string()),
            },
            ">=" => (neg_poly(diff), Op::Le, !positive),
            ">" => match add_poly(neg_poly(diff), one) {
                Some(p) => (p, Op::Le, !positive),
                None => return self.decline(|| "polynomial too large".to_string()),
            },
            "=" => (diff, Op::Eq, !positive),
            "distinct" => (diff, Op::Eq, positive),
            _ => return self.decline(|| format!("relation `{name}` unsupported")),
        };
        let Some(atom) = self.intern_atom(poly, op) else {
            return self.decline(|| "atom budget exhausted".to_string());
        };
        Some(Lit { atom, negated: neg })
    }

    /// CNF of `term` under `positive` polarity, as a list of clauses.
    fn cnf(&mut self, t: TermId, positive: bool, depth: u32) -> Option<Vec<Vec<Lit>>> {
        if depth > 64 {
            self.decline(|| "formula nesting deeper than 64".to_string());
            return None;
        }
        match self.terms.get(t) {
            TermData::Not(inner) => {
                let inner = *inner;
                self.cnf(inner, !positive, depth + 1)
            }
            TermData::Const(Constant::Bool(b)) => {
                // `true` is the empty CONJUNCTION (no clauses); `false` is the
                // singleton empty CLAUSE. Distribution then handles
                // `A or false == A` for free, and a surviving empty clause at
                // the top level means the assertion set is refutable outright —
                // which this lane declines to claim (see `try_clausal_local_search`).
                if *b == positive {
                    Some(Vec::new())
                } else {
                    Some(vec![Vec::new()])
                }
            }
            TermData::App(Symbol::Named(name), args) => {
                let name = name.clone();
                let args = args.clone();
                match name.as_str() {
                    "and" | "or" => {
                        // De Morgan: `not (and ..)` behaves as `or` of negations.
                        let conjunctive = (name == "and") == positive;
                        if conjunctive {
                            let mut out = Vec::new();
                            for a in args {
                                out.extend(self.cnf(a, positive, depth + 1)?);
                                if out.len() > MAX_CLAUSES {
                                    self.decline(|| "clause budget exhausted".to_string());
                                    return None;
                                }
                            }
                            Some(out)
                        } else {
                            let mut parts = Vec::with_capacity(args.len());
                            for a in args {
                                parts.push(self.cnf(a, positive, depth + 1)?);
                            }
                            let sizes: Vec<usize> = parts.iter().map(Vec::len).collect();
                            let out = distribute(parts);
                            if out.is_none() {
                                self.decline(move || {
                                    format!(
                                        "`or` distribution exceeds the clause budget                                          (part sizes {sizes:?})"
                                    )
                                });
                            }
                            out
                        }
                    }
                    "not" if args.len() == 1 => self.cnf(args[0], !positive, depth + 1),
                    "=>" if args.len() >= 2 => {
                        // (=> a b c) == (or (not a) (not b) c)
                        let n = args.len();
                        let mut parts = Vec::with_capacity(n);
                        for (i, a) in args.iter().enumerate() {
                            let pol = if i + 1 == n { positive } else { !positive };
                            parts.push(self.cnf(*a, pol, depth + 1)?);
                        }
                        if positive {
                            distribute(parts)
                        } else {
                            // not (=> ...) is a conjunction of the negated parts.
                            let mut out = Vec::new();
                            for p in parts {
                                out.extend(p);
                            }
                            Some(out)
                        }
                    }
                    _ => {
                        let lit = self.atom_lit(t, positive)?;
                        Some(vec![vec![lit]])
                    }
                }
            }
            other => {
                let d = format!("{:?}", std::mem::discriminant(other));
                self.decline(|| format!("unsupported formula node {d}"));
                None
            }
        }
    }
}

fn neg_poly(mut p: Poly) -> Poly {
    for m in &mut p {
        m.coeff = -m.coeff;
    }
    p
}

fn add_poly(mut a: Poly, b: Poly) -> Option<Poly> {
    for m in b {
        if let Some(e) = a.iter_mut().find(|e| e.vars == m.vars) {
            e.coeff = e.coeff.checked_add(m.coeff)?;
        } else {
            a.push(m);
            if a.len() > MAX_MONOMIALS {
                return None;
            }
        }
    }
    a.retain(|m| m.coeff != 0);
    Some(a)
}

fn mul_poly(a: &Poly, b: &Poly) -> Option<Poly> {
    let mut out: Poly = Vec::new();
    for x in a {
        for y in b {
            let coeff = x.coeff.checked_mul(y.coeff)?;
            if coeff == 0 {
                continue;
            }
            let mut vars = x.vars.clone();
            for &(v, p) in &y.vars {
                match vars.iter_mut().find(|e| e.0 == v) {
                    Some(e) => e.1 = e.1.checked_add(p)?,
                    None => vars.push((v, p)),
                }
            }
            vars.sort_unstable();
            match out.iter_mut().find(|e| e.vars == vars) {
                Some(e) => e.coeff = e.coeff.checked_add(coeff)?,
                None => {
                    out.push(Mono { coeff, vars });
                    if out.len() > MAX_MONOMIALS {
                        return None;
                    }
                }
            }
        }
    }
    out.retain(|m| m.coeff != 0);
    Some(out)
}

/// Distributive `or` over already-CNF'd parts.
fn distribute(parts: Vec<Vec<Vec<Lit>>>) -> Option<Vec<Vec<Lit>>> {
    let mut acc: Vec<Vec<Lit>> = vec![Vec::new()];
    for part in parts {
        if part.is_empty() {
            // A part that is trivially TRUE satisfies the whole disjunction.
            return Some(Vec::new());
        }
        if acc.len().checked_mul(part.len())? > MAX_OR_PRODUCT {
            return None;
        }
        let mut next = Vec::with_capacity(acc.len() * part.len());
        for a in &acc {
            for c in &part {
                let mut merged = a.clone();
                merged.extend_from_slice(c);
                merged.sort_unstable();
                merged.dedup();
                next.push(merged);
            }
        }
        acc = next;
    }
    if acc.len() > MAX_CLAUSES {
        return None;
    }
    Some(acc)
}

// ---------------------------------------------------------------------------
// The search
// ---------------------------------------------------------------------------

/// One candidate variable move (z3: `arith_base::var_change`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Update {
    var: VarIdx,
    delta: i128,
}

struct Search {
    atoms: Vec<Atom>,
    clauses: Vec<Clause>,
    vars: Vec<VarInfo>,
    /// Indices of clauses with `num_true == 0`, plus a position index.
    unsat: Vec<u32>,
    unsat_pos: Vec<Option<u32>>,
    unsat_weight: f64,
    /// Literal -> clauses, for the ddfw weight transfer (`use_list`).
    use_list: HashMap<Lit, Vec<u32>>,
    updates: Vec<Update>,
    /// Stamp buffer for de-duplicating atoms across a lookahead pass.
    stamp: Vec<u64>,
    stamp_gen: u64,
    /// Scan cursor for the sampled false-literal pass.
    atom_cursor: usize,
    step: u64,
    rng: Rng,
    use_tabu: bool,
    /// z3 `arith_base::m_last_var` / `m_last_delta`: the last APPLIED move,
    /// used by `is_permitted_update` to reject an immediate flip back.
    last_var: Option<VarIdx>,
    last_delta: i128,
    /// z3 `arith_clausal::m_last_var` / `m_last_delta`: the last PROBED move,
    /// used only to avoid scoring the same `(var, delta)` twice in a pass.
    probe_var: Option<VarIdx>,
    probe_delta: i128,
    best_score: f64,
    best_var: Option<VarIdx>,
    best_delta: i128,
    best_abs_value: i128,
    best_last_step: u64,
    /// Overflow anywhere aborts the search rather than yielding a wrong value.
    overflow: bool,
    /// z3 `save_best_values`: best (lowest-cost) assignment seen so far, used
    /// to seed perturbed restarts.
    best_values: Vec<i128>,
    best_cost: usize,
}

impl Search {
    fn new(b: Builder<'_>, clauses: Vec<Vec<Lit>>, nvars: usize) -> Self {
        let mut atoms = b.atoms;
        let mut cls: Vec<Clause> = Vec::with_capacity(clauses.len());
        let mut use_list: HashMap<Lit, Vec<u32>> = HashMap::default();
        for (ci, lits) in clauses.into_iter().enumerate() {
            for l in &lits {
                atoms[l.atom as usize].lit_occ.push((ci as u32, l.negated));
                use_list.entry(*l).or_default().push(ci as u32);
            }
            cls.push(Clause {
                lits,
                weight: INIT_WEIGHT,
                num_true: 0,
            });
        }
        let mut vars = vec![VarInfo::default(); nvars];
        for (ai, a) in atoms.iter().enumerate() {
            for (mi, m) in a.monos.iter().enumerate() {
                for &(v, _) in &m.vars {
                    vars[v as usize].mono_occ.push((ai as u32, mi as u32));
                }
            }
            for (v, _) in &a.occ {
                vars[*v as usize].atoms.push(ai as u32);
            }
        }
        for (ci, c) in cls.iter().enumerate() {
            for l in &c.lits {
                for (v, _) in &atoms[l.atom as usize].occ {
                    vars[*v as usize].clauses.push(ci as u32);
                }
            }
        }
        for v in &mut vars {
            v.atoms.sort_unstable();
            v.atoms.dedup();
            v.clauses.sort_unstable();
            v.clauses.dedup();
        }
        let natoms = atoms.len();
        Search {
            atoms,
            clauses: cls,
            vars,
            unsat: Vec::new(),
            unsat_pos: Vec::new(),
            unsat_weight: 0.0,
            use_list,
            updates: Vec::new(),
            stamp: vec![0; natoms],
            stamp_gen: 0,
            atom_cursor: 0,
            step: 0,
            // Seed derived from the query itself (see `Search::reseed`), so the
            // verdict is reproducible for a given input while consecutive
            // invocations within one solve explore different trajectories.
            rng: Rng(0x9E37_79B9_7F4A_7C15),
            use_tabu: true,
            last_var: None,
            last_delta: 0,
            probe_var: None,
            probe_delta: 0,
            best_score: 1.0,
            best_var: None,
            best_delta: 0,
            best_abs_value: -1,
            best_last_step: u64::MAX,
            overflow: false,
            best_values: Vec::new(),
            best_cost: usize::MAX,
        }
    }

    /// Mix a deterministic, query-derived value into the RNG seed.
    ///
    /// The lane is re-entered once per split-loop iteration (the executor
    /// rebuilds the theory solver each time), and with a single fixed seed
    /// every re-entry replayed the identical trajectory and re-burned wall
    /// budget for nothing. `salt` is computed from the solver's own state, so
    /// the seed is a pure function of the query — reproducible run to run —
    /// while still differing between consecutive re-entries.
    fn reseed(&mut self, salt: u64) {
        let mut x = 0x9E37_79B9_7F4A_7C15u64 ^ salt.wrapping_mul(0xA24B_AED4_963E_E407);
        x ^= (self.clauses.len() as u64).wrapping_mul(0x9E37_79B1);
        x ^= (self.atoms.len() as u64).wrapping_mul(0x85EB_CA6B);
        x ^= (self.vars.len() as u64).wrapping_mul(0xC2B2_AE35);
        self.rng = Rng(x | 1);
    }

    // -- bounds ------------------------------------------------------------

    /// z3 `initialize_unit`: read variable bounds off unit clauses.
    fn extract_bounds(&mut self) {
        for ci in 0..self.clauses.len() {
            if self.clauses[ci].lits.len() != 1 {
                continue;
            }
            let lit = self.clauses[ci].lits[0];
            let a = &self.atoms[lit.atom as usize];
            // `c*x + k OP 0` only.
            let mut coeff = 0i128;
            let mut konst = 0i128;
            let mut var = None;
            let mut ok = true;
            for m in &a.monos {
                match m.vars.len() {
                    0 => match konst.checked_add(m.coeff) {
                        Some(k) => konst = k,
                        None => {
                            ok = false;
                            break;
                        }
                    },
                    1 if m.vars[0].1 == 1 && var.is_none() => {
                        var = Some(m.vars[0].0);
                        coeff = m.coeff;
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            let (Some(v), true) = (var, ok) else { continue };
            if coeff == 0 {
                continue;
            }
            // Bounds are a search-space restriction only (the witness is
            // re-verified independently), so any arithmetic edge case simply
            // skips the bound rather than risking a wrapped value.
            let (Some(neg_coeff), Some(neg_konst)) = (coeff.checked_neg(), konst.checked_neg())
            else {
                continue;
            };
            // Effective relation after applying the literal sign.
            // atom: c*x + k <= 0 / < 0 / == 0
            let (op, poly_neg) = match (a.op, lit.negated) {
                (Op::Le, false) => (Op::Le, false),
                (Op::Lt, false) => (Op::Lt, false),
                // not(p <= 0) == (-p < 0); not(p < 0) == (-p <= 0)
                (Op::Le, true) => (Op::Lt, true),
                (Op::Lt, true) => (Op::Le, true),
                (Op::Eq, false) => (Op::Eq, false),
                (Op::Eq, true) => continue, // disequality: no bound
            };
            let (c, k) = if poly_neg {
                (neg_coeff, neg_konst)
            } else {
                (coeff, konst)
            };
            let Some(neg_k) = k.checked_neg() else {
                continue;
            };
            // c*x + k <= 0  =>  x <= -k/c (c>0) or x >= -k/c (c<0)
            // c*x + k <  0  =>  strict; tighten by 1 (integers).
            let vi = &mut self.vars[v as usize];
            let strict_adj = i128::from(op == Op::Lt);
            match op {
                Op::Eq => {
                    if neg_k % c == 0 {
                        let val = neg_k / c;
                        vi.lo = Some(vi.lo.map_or(val, |l| l.max(val)));
                        vi.hi = Some(vi.hi.map_or(val, |h| h.min(val)));
                    }
                }
                _ if c > 0 => {
                    // x <= floor((-k - strict)/c)
                    let Some(n) = neg_k.checked_sub(strict_adj) else {
                        continue;
                    };
                    let bound = floor_div(n, c);
                    vi.hi = Some(vi.hi.map_or(bound, |h| h.min(bound)));
                }
                _ => {
                    // c < 0: x >= ceil((-k - strict)/c)
                    let Some(n) = neg_k.checked_sub(strict_adj) else {
                        continue;
                    };
                    let bound = ceil_div(n, c);
                    vi.lo = Some(vi.lo.map_or(bound, |l| l.max(bound)));
                }
            }
        }
    }

    fn in_bounds(&self, v: VarIdx, value: i128) -> bool {
        let vi = &self.vars[v as usize];
        vi.lo.is_none_or(|l| value >= l) && vi.hi.is_none_or(|h| value <= h)
    }

    fn in_range(value: i128) -> bool {
        (-VALUE_RANGE..=VALUE_RANGE).contains(&value)
    }

    // -- evaluation --------------------------------------------------------

    fn mono_value(&mut self, ai: u32, mi: u32) -> i128 {
        let a = &self.atoms[ai as usize];
        let m = &a.monos[mi as usize];
        let mut acc = m.coeff;
        for &(v, p) in &m.vars {
            let val = self.vars[v as usize].value;
            for _ in 0..p {
                match acc.checked_mul(val) {
                    Some(x) => acc = x,
                    None => {
                        self.overflow = true;
                        return 0;
                    }
                }
            }
        }
        acc
    }

    /// Full recomputation of every atom value / truth and every clause count.
    fn recompute_all(&mut self) {
        for ai in 0..self.atoms.len() {
            let n = self.atoms[ai].monos.len();
            let mut sum: i128 = 0;
            for mi in 0..n {
                let mv = self.mono_value(ai as u32, mi as u32);
                self.atoms[ai].mono_val[mi] = mv;
                match sum.checked_add(mv) {
                    Some(x) => sum = x,
                    None => {
                        self.overflow = true;
                        return;
                    }
                }
            }
            self.atoms[ai].value = sum;
            self.atoms[ai].truth = Atom::eval_truth(sum, self.atoms[ai].op);
        }
        self.unsat.clear();
        self.unsat_pos = vec![None; self.clauses.len()];
        self.unsat_weight = 0.0;
        for ci in 0..self.clauses.len() {
            let n = self.clauses[ci]
                .lits
                .iter()
                .filter(|l| self.atoms[l.atom as usize].truth != l.negated)
                .count() as u32;
            self.clauses[ci].num_true = n;
            if n == 0 {
                self.unsat_pos[ci] = Some(self.unsat.len() as u32);
                self.unsat.push(ci as u32);
                self.unsat_weight += self.clauses[ci].weight;
            }
        }
    }

    /// Apply `value(v) += delta`, keeping atoms and clause counts consistent.
    /// Returns `false` on overflow (state is then untrustworthy and the caller
    /// must abort the whole search).
    fn apply_delta(&mut self, v: VarIdx, delta: i128) -> bool {
        let Some(new_value) = self.vars[v as usize].value.checked_add(delta) else {
            self.overflow = true;
            return false;
        };
        self.vars[v as usize].value = new_value;
        let occ = std::mem::take(&mut self.vars[v as usize].mono_occ);
        for &(ai, mi) in &occ {
            let mv = self.mono_value(ai, mi);
            if self.overflow {
                self.vars[v as usize].mono_occ = occ;
                return false;
            }
            let a = &mut self.atoms[ai as usize];
            let old = a.mono_val[mi as usize];
            a.mono_val[mi as usize] = mv;
            // `mv - old` must itself be checked: both are independently-large
            // monomial values, so their DIFFERENCE can overflow i128 even when the
            // subsequent add would not. `[profile.release] overflow-checks = true`
            // makes a raw `-` here a PANIC, not a wrap — a crash, not a wrong
            // answer, but still a hard failure on adversarial input. Fold it into
            // the same fail-closed path as every other overflow.
            match mv
                .checked_sub(old)
                .and_then(|delta| a.value.checked_add(delta))
            {
                Some(x) => a.value = x,
                None => {
                    self.overflow = true;
                    self.vars[v as usize].mono_occ = occ;
                    return false;
                }
            }
        }
        self.vars[v as usize].mono_occ = occ;
        let atoms = std::mem::take(&mut self.vars[v as usize].atoms);
        for &ai in &atoms {
            let a = &self.atoms[ai as usize];
            let truth = Atom::eval_truth(a.value, a.op);
            if truth == a.truth {
                continue;
            }
            self.atoms[ai as usize].truth = truth;
            let lit_occ = std::mem::take(&mut self.atoms[ai as usize].lit_occ);
            for &(ci, negated) in &lit_occ {
                let now_true = truth != negated;
                self.bump_clause(ci, now_true);
            }
            self.atoms[ai as usize].lit_occ = lit_occ;
        }
        self.vars[v as usize].atoms = atoms;
        true
    }

    fn bump_clause(&mut self, ci: u32, now_true: bool) {
        let c = &mut self.clauses[ci as usize];
        if now_true {
            c.num_true += 1;
            if c.num_true == 1 {
                let w = c.weight;
                self.unsat_weight -= w;
                if let Some(pos) = self.unsat_pos[ci as usize].take() {
                    let last = self.unsat.pop().expect("unsat non-empty");
                    if (pos as usize) < self.unsat.len() {
                        self.unsat[pos as usize] = last;
                        self.unsat_pos[last as usize] = Some(pos);
                    }
                }
            }
        } else {
            c.num_true -= 1;
            if c.num_true == 0 {
                let w = c.weight;
                self.unsat_weight += w;
                self.unsat_pos[ci as usize] = Some(self.unsat.len() as u32);
                self.unsat.push(ci);
            }
        }
    }

    // -- move generation (z3 `arith_base`) ---------------------------------

    /// z3 `is_linear`.
    fn is_linear(&self, x: VarIdx, nl: &[NlCoeff], atom: &Atom) -> Option<i128> {
        if nl.len() == 1 && nl[0].power == 1 && atom.monos[nl[0].mono as usize].vars.len() == 1 {
            return Some(nl[0].coeff);
        }
        let mut b: i128 = 0;
        for c in nl {
            if c.power > 1 {
                return None;
            }
            let w = self.mono_value_without(atom, c.mono, x)?;
            b = b.checked_add(c.coeff.checked_mul(w)?)?;
        }
        if b == 0 {
            None
        } else {
            Some(b)
        }
    }

    /// z3 `is_quadratic`.
    fn is_quadratic(&self, x: VarIdx, nl: &[NlCoeff], atom: &Atom) -> Option<(i128, i128)> {
        let mut a: i128 = 0;
        let mut b: i128 = 0;
        for c in nl {
            let w = self.mono_value_without(atom, c.mono, x)?;
            match c.power {
                1 => b = b.checked_add(c.coeff.checked_mul(w)?)?,
                2 => a = a.checked_add(c.coeff.checked_mul(w)?)?,
                _ => return None,
            }
        }
        if a == 0 && b == 0 {
            None
        } else {
            Some((a, b))
        }
    }

    /// z3 `mul_value_without`: product of the monomial's OTHER factors.
    fn mono_value_without(&self, atom: &Atom, mono: u32, x: VarIdx) -> Option<i128> {
        let m = &atom.monos[mono as usize];
        let mut acc: i128 = 1;
        for &(v, p) in &m.vars {
            if v == x {
                continue;
            }
            let val = self.vars[v as usize].value;
            for _ in 0..p {
                acc = acc.checked_mul(val)?;
            }
        }
        Some(acc)
    }

    /// z3 `arith_base::divide` for the integer case.
    fn divide(delta: i128, coeff: i128) -> Option<i128> {
        let n = delta.checked_add(coeff.checked_abs()?.checked_sub(1)?)?;
        if coeff == 0 {
            return None;
        }
        Some(n / coeff)
    }

    /// z3 `find_linear_moves`.
    fn find_linear_moves(&mut self, ai: u32, x: VarIdx, coeff: i128) {
        let (sum, op, truth) = {
            let a = &self.atoms[ai as usize];
            (a.value, a.op, a.truth)
        };
        let push = |s: &mut Self, d: Option<i128>| {
            if let Some(d) = d {
                s.add_update(x, d);
            }
        };
        if truth {
            match op {
                Op::Le => push(
                    self,
                    sum.checked_neg()
                        .and_then(|n| n.checked_add(1))
                        .and_then(|n| Self::divide(n, coeff)),
                ),
                Op::Lt => push(self, sum.checked_neg().and_then(|n| Self::divide(n, coeff))),
                Op::Eq => {
                    push(self, Some(1));
                    push(self, Some(-1));
                }
            }
        } else {
            match op {
                Op::Le => push(self, Self::divide(sum, coeff).and_then(|d| d.checked_neg())),
                Op::Lt => push(
                    self,
                    sum.checked_add(1)
                        .and_then(|n| Self::divide(n, coeff))
                        .and_then(|d| d.checked_neg()),
                ),
                Op::Eq => {
                    let d = if sum < 0 {
                        sum.checked_abs().and_then(|n| Self::divide(n, coeff))
                    } else {
                        Self::divide(sum, coeff).and_then(|d| d.checked_neg())
                    };
                    if let Some(d) = d {
                        // z3 only accepts the exact hit.
                        if coeff
                            .checked_mul(d)
                            .and_then(|x| sum.checked_add(x))
                            .is_some_and(|r| r == 0)
                        {
                            push(self, Some(d));
                        }
                    }
                }
            }
        }
    }

    /// z3 `find_quadratic_moves` (integer case: `a*x^2 + b*x + c = sum`).
    fn find_quadratic_moves(&mut self, ai: u32, x: VarIdx, a: i128, b: i128) {
        if a == 0 {
            return;
        }
        let (sum, op, truth) = {
            let at = &self.atoms[ai as usize];
            (at.value, at.op, at.truth)
        };
        let xv = self.vars[x as usize].value;
        let Some(c) = (|| {
            let ax2 = a.checked_mul(xv)?.checked_mul(xv)?;
            let bx = b.checked_mul(xv)?;
            sum.checked_sub(ax2)?.checked_sub(bx)
        })() else {
            return;
        };
        let Some(d) = (|| {
            b.checked_mul(b)?
                .checked_sub(4i128.checked_mul(a)?.checked_mul(c)?)
        })() else {
            return;
        };
        if d < 0 {
            return;
        }
        let root = isqrt(d);
        let is_square = root.checked_mul(root) == Some(d);
        let two_a = match a.checked_mul(2) {
            Some(t) => t,
            None => return,
        };
        let (Some(nb_minus), Some(nb_plus)) = (
            b.checked_neg().and_then(|n| n.checked_sub(root)),
            b.checked_neg().and_then(|n| n.checked_add(root)),
        ) else {
            return;
        };
        let mut ll = floor_div(nb_minus, two_a);
        let mut lh = ceil_div(nb_minus, two_a);
        let mut rl = floor_div(nb_plus, two_a);
        let mut rh = ceil_div(nb_plus, two_a);
        if lh > rl {
            std::mem::swap(&mut ll, &mut rl);
            std::mem::swap(&mut lh, &mut rh);
        }
        if d > 0 && lh == rh {
            return;
        }
        if d == 0 && ll != lh {
            return;
        }
        let q = |t: i128| -> Option<i128> {
            a.checked_mul(t)?
                .checked_mul(t)?
                .checked_add(b.checked_mul(t)?)?
                .checked_add(c)
        };
        let mut cand: Vec<i128> = Vec::new();
        if truth {
            match op {
                Op::Le | Op::Lt => {
                    if d == 0 {
                        return;
                    }
                    if a < 0 {
                        if q(lh).is_some_and(|v| v <= 0) {
                            lh += 1;
                        }
                        if q(rl).is_some_and(|v| v <= 0) {
                            rl -= 1;
                        }
                        cand.push(lh);
                        cand.push(rl);
                    } else {
                        if q(ll).is_some_and(|v| v <= 0) {
                            ll -= 1;
                        }
                        if q(rh).is_some_and(|v| v <= 0) {
                            rh += 1;
                        }
                        cand.push(ll);
                        cand.push(rh);
                    }
                }
                Op::Eq => {
                    cand.push(1);
                    cand.push(-1);
                    for t in cand.drain(..).collect::<Vec<_>>() {
                        self.add_update(x, t);
                    }
                    return;
                }
            }
        } else {
            match op {
                Op::Le | Op::Lt => {
                    if d == 0 {
                        if a > 0 && ll == lh {
                            cand.push(ll);
                        }
                    } else if a > 0 {
                        if q(lh).is_some_and(|v| v > 0) {
                            lh += 1;
                        }
                        if q(rl).is_some_and(|v| v > 0) {
                            rl -= 1;
                        }
                        cand.push(lh);
                        cand.push(rl);
                    } else {
                        if q(ll).is_some_and(|v| v > 0) {
                            ll += 1;
                        }
                        if q(rh).is_some_and(|v| v > 0) {
                            rh -= 1;
                        }
                        cand.push(ll);
                        cand.push(rh);
                    }
                }
                Op::Eq => {
                    if !is_square {
                        return;
                    }
                    if ll == lh {
                        cand.push(ll);
                    }
                    if rl == rh && lh != rh {
                        cand.push(rl);
                    }
                }
            }
        }
        for t in cand {
            if let Some(delta) = t.checked_sub(xv) {
                self.add_update(x, delta);
            }
        }
    }

    /// z3 `is_permitted_update` + `add_update`.
    fn add_update(&mut self, v: VarIdx, delta: i128) {
        if delta == 0 {
            return;
        }
        if self.last_var == Some(v) && self.last_delta.checked_neg() == Some(delta) {
            return; // flip back
        }
        if self.use_tabu && self.vars[v as usize].is_tabu(self.step, delta) {
            return;
        }
        let old = self.vars[v as usize].value;
        let Some(new) = old.checked_add(delta) else {
            return;
        };
        if !Self::in_range(new) {
            return;
        }
        let mut delta_out = delta;
        if self.use_tabu && !self.in_bounds(v, new) && self.in_bounds(v, old) {
            let (lo, hi) = (self.vars[v as usize].lo, self.vars[v as usize].hi);
            if let Some(l) = lo {
                if l > new {
                    if delta_out < 0 && l < old {
                        delta_out = l - old;
                    } else {
                        return;
                    }
                }
            }
            if let Some(h) = hi {
                if h < new {
                    if delta_out > 0 && h > old {
                        delta_out = h - old;
                    } else {
                        return;
                    }
                }
            }
        }
        if delta_out == 0 {
            return;
        }
        if self.updates.len() < MAX_ATOMS {
            self.updates.push(Update {
                var: v,
                delta: delta_out,
            });
        }
    }

    /// z3 `add_lookahead(bv)`.
    fn add_lookahead(&mut self, ai: u32) {
        if self.stamp[ai as usize] == self.stamp_gen {
            return;
        }
        self.stamp[ai as usize] = self.stamp_gen;
        // `occ` is immutable for the lifetime of the search; move it out for the
        // duration of the pass so the borrow checker allows `&mut self` calls
        // without cloning the occurrence lists on every step.
        let occ = std::mem::take(&mut self.atoms[ai as usize].occ);
        for (x, nl) in &occ {
            let x = *x;
            if self.vars[x as usize].is_fixed() {
                continue;
            }
            let atom_ref = &self.atoms[ai as usize];
            if let Some(b) = self.is_linear(x, nl, atom_ref) {
                self.find_linear_moves(ai, x, b);
            } else if let Some((a, b)) = self.is_quadratic(x, nl, atom_ref) {
                self.find_quadratic_moves(ai, x, a, b);
            }
        }
        self.atoms[ai as usize].occ = occ;
    }

    /// z3 `add_lookahead_on_unsat_vars`.
    fn lookahead_unsat(&mut self) {
        self.updates.clear();
        self.stamp_gen += 1;
        // `self.unsat` is stable across `add_lookahead` (which only reads), so
        // walk it by index rather than cloning it on every step.
        let mut i = 0;
        while i < self.unsat.len() {
            let ci = self.unsat[i] as usize;
            let mut j = 0;
            while j < self.clauses[ci].lits.len() {
                let atom = self.clauses[ci].lits[j].atom;
                self.add_lookahead(atom);
                j += 1;
            }
            i += 1;
        }
    }

    /// z3 `add_lookahead_on_false_literals`.
    fn lookahead_false_lits(&mut self) {
        self.updates.clear();
        self.stamp_gen += 1;
        let sz = self.atoms.len();
        if sz == 0 {
            return;
        }
        // z3 marks an atom relevant when its currently-FALSE literal occurs in
        // some clause and the atom is not already in an unsat clause.
        let occurs_negative = |s: &Search, ai: u32| -> bool {
            let a = &s.atoms[ai as usize];
            // z3: `if (ctx.unsat_vars().contains(bv)) return false;`
            if a.lit_occ
                .iter()
                .any(|&(ci, _)| s.clauses[ci as usize].num_true == 0)
            {
                return false;
            }
            // the literal that is currently false is `Lit { atom, negated: truth }`
            s.use_list
                .get(&Lit {
                    atom: ai,
                    negated: a.truth,
                })
                .is_some_and(|v| !v.is_empty())
        };
        if sz > BIG_ATOM_SET {
            let mut taken = 0;
            let mut tries = 0;
            while taken < BIG_ATOM_SET && tries < 2 * BIG_ATOM_SET {
                tries += 1;
                self.atom_cursor = (self.atom_cursor + 1 + self.rng.below(sz)) % sz;
                let ai = self.atom_cursor as u32;
                if occurs_negative(self, ai) {
                    taken += 1;
                    self.add_lookahead(ai);
                }
            }
        } else {
            for ai in 0..sz as u32 {
                if occurs_negative(self, ai) {
                    self.add_lookahead(ai);
                }
            }
        }
    }

    /// z3 `get_score`: weighted make-break of applying `v += delta`.
    fn score_of(&mut self, v: VarIdx, delta: i128) -> f64 {
        let before = self.unsat_weight;
        if !self.apply_delta(v, delta) {
            return -1.0;
        }
        let after = self.unsat_weight;
        if let Some(back) = delta.checked_neg() {
            if !self.apply_delta(v, back) {
                self.overflow = true;
            }
        } else {
            self.overflow = true;
        }
        before - after
    }

    fn can_update(&self, v: VarIdx, delta: i128) -> bool {
        let old = self.vars[v as usize].value;
        let Some(new) = old.checked_add(delta) else {
            return false;
        };
        if old == new {
            return true;
        }
        if !Self::in_range(new) {
            return false;
        }
        if !self.in_bounds(v, new) && self.in_bounds(v, old) {
            return false;
        }
        true
    }

    /// z3 `arith_clausal::lookahead`.
    fn lookahead_one(&mut self, v: VarIdx, delta: i128) {
        if self.probe_var == Some(v) && self.probe_delta == delta {
            return;
        }
        if delta == 0 {
            return;
        }
        self.probe_var = Some(v);
        self.probe_delta = delta;
        if !self.can_update(v, delta) {
            return;
        }
        let score = self.score_of(v, delta);
        if self.overflow {
            return;
        }
        // Checked, for the same reason as the monomial-delta add above: raw `+`
        // PANICS under `[profile.release] overflow-checks = true`. This value is
        // only a tie-break heuristic, so on overflow prefer the candidate LAST by
        // saturating to i128::MAX rather than aborting the whole move search —
        // `can_update`/`score_of` above already fail closed on real overflow.
        let abs_value = self.vars[v as usize]
            .value
            .checked_add(delta)
            .map_or(i128::MAX, i128::abs);
        let last_step = self.vars[v as usize].last_step(delta);
        if score < self.best_score {
            return;
        }
        if score > self.best_score
            || self.best_abs_value == -1
            || abs_value < self.best_abs_value
            || (abs_value == self.best_abs_value && last_step < self.best_last_step)
        {
            self.best_score = score;
            self.best_var = Some(v);
            self.best_delta = delta;
            self.best_last_step = last_step;
            self.best_abs_value = abs_value;
        }
    }

    /// z3 `critical_move_on_updates`.
    fn critical_move_on_updates(&mut self) -> Option<VarIdx> {
        if self.updates.is_empty() {
            return None;
        }
        let mut updates = std::mem::take(&mut self.updates);
        updates.sort_unstable();
        updates.dedup();
        self.probe_var = None;
        self.probe_delta = 0;
        self.best_var = None;
        self.best_delta = 0;
        self.best_abs_value = -1;
        self.best_last_step = u64::MAX;
        for u in &updates {
            self.lookahead_one(u.var, u.delta);
            if self.overflow {
                break;
            }
        }
        self.updates = updates;
        let v = self.best_var?;
        let d = self.best_delta;
        self.critical_move(v, d);
        Some(v)
    }

    /// z3 `random_move_on_updates`.
    fn random_move_on_updates(&mut self) -> Option<VarIdx> {
        if self.updates.is_empty() {
            return None;
        }
        let idx = self.rng.below(self.updates.len());
        let u = self.updates[idx];
        if !self.can_update(u.var, u.delta) {
            return None;
        }
        self.critical_move(u.var, u.delta);
        Some(u.var)
    }

    /// z3 `critical_move`.
    fn critical_move(&mut self, v: VarIdx, delta: i128) {
        self.last_var = Some(v);
        self.last_delta = delta;
        let tabu_step = self.step + 3 + self.rng.below(10) as u64;
        self.vars[v as usize].set_step(self.step, tabu_step, delta);
        self.apply_delta(v, delta);
    }

    /// z3 `move_arith_variable`.
    fn move_arith_variable(&mut self) {
        self.best_score = 1.0;
        self.use_tabu = true;
        self.lookahead_unsat();
        let mut v = self.critical_move_on_updates();
        if v.is_none() && !self.overflow {
            self.best_score = 1.0;
            self.lookahead_false_lits();
            v = self.critical_move_on_updates();
        }
        if v.is_none() && !self.overflow {
            self.shift_weights();
            self.best_score = -1.0;
            self.use_tabu = false;
            self.lookahead_unsat();
            v = self.random_move_on_updates();
        }
        self.use_tabu = true;
        let _ = v;
    }

    /// ddfw `shift_weights` + `transfer_weight` (`sat_ddfw.cpp:517,557`).
    fn shift_weights(&mut self) {
        let unsat = std::mem::take(&mut self.unsat);
        for &to_idx in &unsat {
            // `select_max_same_sign`: max-weight satisfied clause sharing a
            // literal with the unsat clause.
            let mut from: Option<u32> = None;
            let mut max_w = INIT_WEIGHT;
            let lits = std::mem::take(&mut self.clauses[to_idx as usize].lits);
            for l in &lits {
                let Some(cands) = self.use_list.get(l) else {
                    continue;
                };
                for &cn in cands {
                    let c = &self.clauses[cn as usize];
                    if c.num_true > 0 && c.weight > max_w {
                        max_w = c.weight;
                        from = Some(cn);
                    }
                }
            }
            self.clauses[to_idx as usize].lits = lits;
            let from = match from {
                Some(f) => f,
                None => {
                    // `select_random_true_clause`
                    let n = self.clauses.len();
                    let mut pick = None;
                    for _ in 0..16 {
                        let idx = self.rng.below(n) as u32;
                        let c = &self.clauses[idx as usize];
                        if c.num_true > 0 && c.weight >= INIT_WEIGHT {
                            pick = Some(idx);
                            break;
                        }
                    }
                    match pick {
                        Some(p) => p,
                        None => continue,
                    }
                }
            };
            let w = if self.clauses[from as usize].weight > INIT_WEIGHT {
                INIT_WEIGHT
            } else {
                1.0
            };
            if self.clauses[from as usize].weight < w {
                continue;
            }
            self.clauses[from as usize].weight -= w;
            self.clauses[to_idx as usize].weight += w;
            self.unsat_weight += w;
        }
        self.unsat = unsat;
    }

    /// The bound-respecting zero point z3's `check_restart` resets to.
    fn base_value(&self, v: usize) -> i128 {
        let vi = &self.vars[v];
        match (vi.lo, vi.hi) {
            (Some(l), _) if l > 0 => l,
            (_, Some(h)) if h < 0 => h,
            _ => 0,
        }
    }

    fn clamp_to_bounds(&self, v: usize, value: i128) -> i128 {
        let vi = &self.vars[v];
        let mut x = value;
        if let Some(l) = vi.lo {
            x = x.max(l);
        }
        if let Some(h) = vi.hi {
            x = x.min(h);
        }
        x
    }

    /// z3 `check_restart` (reset to the bound-respecting zero point), with the
    /// one addition the fixed-wall setting needs: **randomized** restarts.
    ///
    /// z3 restarts against an effectively unbounded step budget, so replaying
    /// the same deterministic trajectory from the same zero point eventually
    /// diverges through tabu noise alone. Inside a per-file wall budget that is
    /// pure waste — the observed failure mode was a plateau at 1-2 unsatisfied
    /// clauses that survived every restart. Alternating a plain z3-style reset
    /// with a perturbation of the BEST assignment seen so far restores the
    /// diversification the step budget would otherwise have supplied.
    fn check_restart(&mut self, restarts: u64) {
        // 0: z3's plain reset. 1: perturb the best assignment seen. 2: a small
        // random point. Cycling the three keeps the trajectory from re-entering
        // the same plateau.
        let mode = if self.best_values.is_empty() {
            0
        } else {
            restarts % 3
        };
        for v in 0..self.vars.len() {
            let val = match mode {
                1 => {
                    let base = self.best_values[v];
                    if self.rng.below(4) == 0 {
                        let jitter = self.rng.below(7) as i128 - 3;
                        self.clamp_to_bounds(v, base.saturating_add(jitter))
                    } else {
                        base
                    }
                }
                2 => {
                    let r = self.rng.below(5) as i128 - 2;
                    self.clamp_to_bounds(v, r)
                }
                _ => self.base_value(v),
            };
            self.vars[v].value = val;
            self.vars[v].tabu_pos = 0;
            self.vars[v].tabu_neg = 0;
        }
        for c in &mut self.clauses {
            c.weight = INIT_WEIGHT;
        }
        self.last_var = None;
        self.last_delta = 0;
        self.probe_var = None;
        self.probe_delta = 0;
        self.recompute_all();
    }

    /// z3 `arith_clausal::search`, arithmetic mode only (see module docs).
    fn run(&mut self, deadline: Option<ay_core::time::Instant>) -> bool {
        self.extract_bounds();
        for v in 0..self.vars.len() {
            self.vars[v].value = self.base_value(v);
        }
        self.recompute_all();
        if self.overflow {
            return false;
        }
        // z3 `save_best_values`.
        self.best_cost = self.unsat.len();
        self.best_values = self.vars.iter().map(|v| v.value).collect();
        let mut local_best = self.unsat.len();
        let mut no_improve: u64 = 0;
        let mut restarts: u64 = 0;
        while self.step < MAX_STEPS {
            if self.unsat.is_empty() {
                return true;
            }
            if self.step % DEADLINE_POLL_STEPS == 0
                && deadline.is_some_and(|d| ay_core::time::Instant::now() >= d)
            {
                return false;
            }
            self.step += 1;
            if no_improve > RESTART_AFTER {
                restarts += 1;
                self.check_restart(restarts);
                if self.overflow {
                    return false;
                }
                no_improve = 0;
                local_best = self.unsat.len();
                continue;
            }
            self.move_arith_variable();
            if self.overflow {
                return false;
            }
            let cost = self.unsat.len();
            if cost < self.best_cost {
                self.best_cost = cost;
                self.best_values.clear();
                self.best_values.extend(self.vars.iter().map(|v| v.value));
            }
            if cost < local_best {
                local_best = cost;
                no_improve = 0;
            } else {
                no_improve += 1;
            }
        }
        self.unsat.is_empty()
    }
}

/// Short human-readable shape of a term, for the decline diagnostics.
fn describe(terms: &ay_core::term::TermStore, t: TermId) -> String {
    match terms.get(t) {
        TermData::App(Symbol::Named(n), args) => {
            let kids: Vec<String> = args
                .iter()
                .take(3)
                .map(|&a| match terms.get(a) {
                    TermData::App(Symbol::Named(m), _) => format!("({m} ..)"),
                    TermData::Var(v, _) => format!("{v}:{:?}", terms.sort(a)),
                    other => format!("{:?}", std::mem::discriminant(other)),
                })
                .collect();
            format!("({} {})", n, kids.join(" "))
        }
        TermData::Var(v, _) => format!("var {v}:{:?}", terms.sort(t)),
        TermData::Not(_) => "not".to_string(),
        TermData::Ite(_, _, _) => "ite".to_string(),
        other => format!("{:?}", std::mem::discriminant(other)),
    }
}

fn floor_div(a: i128, b: i128) -> i128 {
    let q = a / b;
    if (a % b != 0) && ((a < 0) != (b < 0)) {
        q - 1
    } else {
        q
    }
}

fn ceil_div(a: i128, b: i128) -> i128 {
    let q = a / b;
    if (a % b != 0) && ((a < 0) == (b < 0)) {
        q + 1
    } else {
        q
    }
}

/// Integer square root of a non-negative `i128`.
fn isqrt(d: i128) -> i128 {
    if d <= 1 {
        return d;
    }
    let mut x = d;
    let mut y = (x + 1) / 2;
    while y < x {
        x = y;
        y = (x + d / x) / 2;
    }
    x
}

// ---------------------------------------------------------------------------
// NiaSolver integration
// ---------------------------------------------------------------------------

impl NiaSolver<'_> {
    /// Exact evaluation of a whole assertion FORMULA (not just an atom) under
    /// an integer assignment (`#nia-clausal-sls`).
    ///
    /// Fail-closed: returns `None` for any construct it cannot evaluate
    /// exactly, so a witness is only ever accepted when every original
    /// assertion evaluated to a definite `true`.
    pub(crate) fn eval_formula_exact(
        &self,
        term: TermId,
        positive: bool,
        var_map: &HashMap<TermId, i64>,
    ) -> Option<bool> {
        match self.terms.get(term) {
            TermData::Const(Constant::Bool(b)) => Some(*b == positive),
            TermData::Not(inner) => self.eval_formula_exact(*inner, !positive, var_map),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "and" | "or" => {
                    // Under `positive == false` De Morgan swaps the connective.
                    let conjunctive = (name == "and") == positive;
                    let mut acc = conjunctive;
                    for &a in args {
                        let v = self.eval_formula_exact(a, positive, var_map)?;
                        if conjunctive {
                            acc &= v;
                        } else {
                            acc |= v;
                        }
                    }
                    Some(acc)
                }
                "=>" if args.len() >= 2 => {
                    let n = args.len();
                    let mut acc = false;
                    for (i, &a) in args.iter().enumerate() {
                        let pol = i + 1 == n;
                        acc |= self.eval_formula_exact(a, pol, var_map)?;
                    }
                    Some(acc == positive)
                }
                "not" if args.len() == 1 => self.eval_formula_exact(args[0], !positive, var_map),
                _ => self.eval_constraint_exact(term, positive, var_map),
            },
            _ => self.eval_constraint_exact(term, positive, var_map),
        }
    }

    /// Clausal local search over the ORIGINAL assertion formulas
    /// (`#nia-clausal-sls`) — **SAT only, never `Unsat`**.
    ///
    /// This is the lane that runs after the box-shaped fallbacks
    /// (`try_bounded_enumeration` / `try_capped_model_search` /
    /// `try_model_repair_search` / `try_bounded_factor_split`) have all
    /// declined. Those all need a finite box; local search does not, which is
    /// exactly the QF_NIA loss shape (VeryMax/AProVE termination VCs over
    /// unbounded integers).
    ///
    /// Returns `Some(TheoryResult::Sat)` only for an assignment that
    /// [`NiaSolver::eval_formula_exact`] confirms satisfies EVERY root
    /// assertion; `None` otherwise. The executor still re-validates through
    /// `finalize_sat_model_validation`.
    /// Wall cutoff for one lane invocation (#nia-clausal-sls).
    ///
    /// Prefers the shared per-solve cutoff installed by the executor (so the
    /// lane's TOTAL share is bounded however many times the split loop
    /// recreates the theory); falls back to a fraction of the remaining solve
    /// budget when no cutoff was installed. Never exceeds the solve deadline.
    fn local_search_budget(&self) -> Option<ay_core::time::Instant> {
        let now = ay_core::time::Instant::now();
        let fallback = self.deadline.map(|dl| {
            if dl <= now {
                now
            } else {
                now + (dl - now) * BUDGET_FRACTION / 100
            }
        });
        match self.local_search_deadline {
            // Shared cutoff governs, but never run past the solve deadline.
            Some(shared) => Some(match self.deadline {
                Some(dl) => shared.min(dl),
                None => shared,
            }),
            None => fallback,
        }
    }

    pub(crate) fn try_clausal_local_search(&mut self) -> Option<TheoryResult> {
        // Kill switch for A/B measurement and for quarantining the lane without
        // a rebuild (#nia-clausal-sls). Absent => lane enabled.
        if std::env::var_os("AY_NIA_NO_CLAUSAL_SLS").is_some() {
            return None;
        }
        if self.root_assertions.is_empty() {
            if self.debug {
                safe_eprintln!("[NIA] Clausal SLS: no root assertions installed; skipping");
            }
            return None;
        }
        if self.local_search_done {
            return None;
        }
        self.local_search_done = true;
        // The shared budget may already be spent by an earlier theory instance
        // in this same solve; leave the remaining wall to the rest of the
        // pipeline rather than re-running a search that has no time to finish.
        if self
            .local_search_budget()
            .is_some_and(|b| ay_core::time::Instant::now() >= b)
        {
            if self.debug {
                safe_eprintln!("[NIA] Clausal SLS: shared wall budget exhausted; skipping");
            }
            return None;
        }
        // Speculative tentative-patch scopes pin variables to guessed points;
        // they play no role here (the search owns its own assignment), but drop
        // them so nothing downstream sees a half-applied scope.
        self.undo_tentative_patch();

        let roots = self.root_assertions.clone();
        let mut builder = Builder::new(self.terms);
        let mut clauses: Vec<Vec<Lit>> = Vec::new();
        for &r in &roots {
            let Some(cs) = builder.cnf(r, true, 0) else {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Clausal SLS: assertion {:?} {} outside the supported fragment: \
                         {}; declining",
                        r,
                        describe(self.terms, r),
                        builder.decline.as_deref().unwrap_or("unknown reason")
                    );
                }
                return None;
            };
            clauses.extend(cs);
            if clauses.len() > MAX_CLAUSES {
                if self.debug {
                    safe_eprintln!("[NIA] Clausal SLS: too many clauses; declining");
                }
                return None;
            }
        }
        if clauses.is_empty() || builder.var_term.is_empty() {
            return None;
        }
        // A surviving EMPTY clause means the assertion set is refutable by
        // propositional structure alone. Local search cannot certify that, and
        // this lane never emits `unsat`, so decline rather than spin.
        if clauses.iter().any(Vec::is_empty) {
            if self.debug {
                safe_eprintln!("[NIA] Clausal SLS: empty clause in the encoding; declining");
            }
            return None;
        }
        let var_term = builder.var_term.clone();
        let nvars = var_term.len();
        if self.debug {
            safe_eprintln!(
                "[NIA] Clausal SLS: {} clauses, {} atoms, {} vars",
                clauses.len(),
                builder.atoms.len(),
                nvars
            );
        }
        let mut search = Search::new(builder, clauses, nvars);
        // Deterministic per-query salt that still varies across the split
        // loop's successive theory instances.
        let salt = self
            .asserted
            .iter()
            .fold(self.asserted.len() as u64, |acc, &(t, v)| {
                acc.wrapping_mul(31)
                    .wrapping_add(u64::from(t.0))
                    .wrapping_add(u64::from(v))
            });
        search.reseed(salt);
        let found = search.run(self.local_search_budget());
        if !found {
            if self.debug {
                safe_eprintln!(
                    "[NIA] Clausal SLS: no model after {} steps ({} clauses unsat)",
                    search.step,
                    search.unsat.len()
                );
            }
            return None;
        }

        // --- exact verification against the ORIGINAL assertion formulas -----
        let mut var_map: HashMap<TermId, i64> = HashMap::default();
        for (i, &t) in var_term.iter().enumerate() {
            let v = search.vars[i].value;
            var_map.insert(t, i64::try_from(v).ok()?);
        }
        // Any Int leaf the search did not encode (it cannot happen for a
        // formula the builder accepted, but this is the fail-closed guard)
        // must still get a value for the evaluator.
        let mut leaves: Vec<TermId> = Vec::new();
        for &r in &roots {
            self.collect_int_var_leaves(r, &mut leaves);
        }
        for l in leaves {
            var_map.entry(l).or_insert(0);
        }
        for &r in &roots {
            match self.eval_formula_exact(r, true, &var_map) {
                Some(true) => {}
                _ => {
                    if self.debug {
                        safe_eprintln!(
                            "[NIA] Clausal SLS: candidate REJECTED by exact verification"
                        );
                    }
                    return None;
                }
            }
        }
        let mut vars: Vec<TermId> = var_map.keys().copied().collect();
        vars.sort_by_key(|t| t.0);
        let values: Vec<i64> = vars.iter().map(|v| var_map[v]).collect();
        self.record_local_search_model(&vars, &values);
        if self.debug {
            safe_eprintln!(
                "[NIA] Clausal SLS: SAT with verified witness after {} steps",
                search.step
            );
        }
        Some(TheoryResult::Sat)
    }

    /// Publish the verified witness through the same channel bounded
    /// enumeration uses, extending it with the monomial auxiliary variables so
    /// the executor's model stays internally consistent.
    fn record_local_search_model(&mut self, vars: &[TermId], values: &[i64]) {
        let var_map: HashMap<TermId, i64> =
            vars.iter().copied().zip(values.iter().copied()).collect();
        let mut model: HashMap<TermId, BigInt> = HashMap::default();
        for (&var, &value) in vars.iter().zip(values) {
            model.insert(var, BigInt::from(value));
        }
        for mon in self.monomials.values() {
            if let Some(value) = self.eval_term(mon.aux_var, &var_map) {
                model.insert(mon.aux_var, value);
            }
        }
        self.bounded_enum_model = Some(model);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::term::TermStore;
    use ay_core::TheorySolver;

    fn mono(coeff: i128, vars: &[(VarIdx, u32)]) -> Mono {
        Mono {
            coeff,
            vars: vars.to_vec(),
        }
    }

    #[test]
    fn isqrt_exact_and_floor() {
        assert_eq!(isqrt(0), 0);
        assert_eq!(isqrt(1), 1);
        assert_eq!(isqrt(24), 4);
        assert_eq!(isqrt(25), 5);
        assert_eq!(isqrt(26), 5);
        assert_eq!(isqrt(1_000_000), 1000);
        assert_eq!(isqrt(999_999), 999);
    }

    #[test]
    fn floor_ceil_div_match_math() {
        assert_eq!(floor_div(7, 2), 3);
        assert_eq!(floor_div(-7, 2), -4);
        assert_eq!(floor_div(7, -2), -4);
        assert_eq!(floor_div(-7, -2), 3);
        assert_eq!(ceil_div(7, 2), 4);
        assert_eq!(ceil_div(-7, 2), -3);
        assert_eq!(ceil_div(7, -2), -3);
        assert_eq!(ceil_div(-7, -2), 4);
    }

    #[test]
    fn mul_poly_multiplies_and_merges() {
        // (x + 1) * (x - 1) = x^2 - 1
        let a = vec![mono(1, &[(0, 1)]), mono(1, &[])];
        let b = vec![mono(1, &[(0, 1)]), mono(-1, &[])];
        let p = mul_poly(&a, &b).expect("no overflow");
        assert_eq!(p.len(), 2);
        assert!(p.contains(&mono(1, &[(0, 2)])));
        assert!(p.contains(&mono(-1, &[])));
    }

    #[test]
    fn add_poly_cancels_to_empty() {
        let a = vec![mono(3, &[(0, 1)])];
        let b = vec![mono(-3, &[(0, 1)])];
        assert!(add_poly(a, b).expect("no overflow").is_empty());
    }

    #[test]
    fn distribute_caps_blowup() {
        // 40 parts of 2 clauses each = 2^40 — must decline, not hang.
        let parts: Vec<Vec<Vec<Lit>>> = (0..40)
            .map(|i| {
                vec![
                    vec![Lit {
                        atom: i,
                        negated: false,
                    }],
                    vec![Lit {
                        atom: i,
                        negated: true,
                    }],
                ]
            })
            .collect();
        assert!(distribute(parts).is_none());
    }

    #[test]
    fn distribute_products_two_by_two() {
        let parts = vec![
            vec![
                vec![Lit {
                    atom: 0,
                    negated: false,
                }],
                vec![Lit {
                    atom: 1,
                    negated: false,
                }],
            ],
            vec![
                vec![Lit {
                    atom: 2,
                    negated: false,
                }],
                vec![Lit {
                    atom: 3,
                    negated: false,
                }],
            ],
        ];
        let out = distribute(parts).expect("small product");
        assert_eq!(out.len(), 4);
        assert!(out.iter().all(|c| c.len() == 2));
    }

    // -- end-to-end lane behaviour ----------------------------------------

    /// `(or (and x*y = 6, x >= 2) (and x*y = 35, x >= 5))` with UNBOUNDED
    /// integers: no finite box exists, so every box-shaped fallback declines,
    /// but local search finds a witness. This is the target shape in miniature.
    #[test]
    fn lane_solves_unbounded_disjunctive_product() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let xy = terms.mk_mul(vec![x, y]);
        let six = terms.mk_int(BigInt::from(6));
        let two = terms.mk_int(BigInt::from(2));
        let thirty_five = terms.mk_int(BigInt::from(35));
        let five = terms.mk_int(BigInt::from(5));
        let a1 = terms.mk_eq(xy, six);
        let a2 = terms.mk_ge(x, two);
        let b1 = terms.mk_eq(xy, thirty_five);
        let b2 = terms.mk_ge(x, five);
        let left = terms.mk_and(vec![a1, a2]);
        let right = terms.mk_and(vec![b1, b2]);
        let root = terms.mk_or(vec![left, right]);

        let mut solver = NiaSolver::new(&terms);
        solver.set_root_assertions(vec![root]);
        // Pretend DPLL picked the left disjunct; the lane is free to pick either.
        solver.assert_literal(a1, true);
        solver.assert_literal(a2, true);
        let result = solver.try_clausal_local_search();
        assert!(
            matches!(result, Some(TheoryResult::Sat)),
            "lane should find a witness, got {result:?}"
        );
        let model = solver.bounded_enum_model.clone().expect("witness recorded");
        let xv = model.get(&x).expect("x in model").clone();
        let yv = model.get(&y).expect("y in model").clone();
        let prod = &xv * &yv;
        assert!(
            (prod == BigInt::from(6) && xv >= BigInt::from(2))
                || (prod == BigInt::from(35) && xv >= BigInt::from(5)),
            "witness must satisfy one disjunct exactly: x={xv} y={yv}"
        );
        assert_eq!(
            model.get(&xy).cloned(),
            Some(prod),
            "the monomial aux var must carry the true product"
        );
    }

    /// The lane must never claim `sat` on an UNSAT formula, however long it
    /// searches. `x*x = 2` has no integer solution.
    #[test]
    fn lane_never_claims_sat_on_unsat() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let xx = terms.mk_mul(vec![x, x]);
        let two = terms.mk_int(BigInt::from(2));
        let root = terms.mk_eq(xx, two);

        let mut solver = NiaSolver::new(&terms);
        solver.set_deadline(ay_core::time::Instant::now() + std::time::Duration::from_millis(300));
        solver.set_root_assertions(vec![root]);
        solver.assert_literal(root, true);
        let result = solver.try_clausal_local_search();
        assert!(
            !matches!(result, Some(TheoryResult::Sat)),
            "no integer x has x*x = 2"
        );
        assert!(
            !matches!(result, Some(TheoryResult::Unsat(_))),
            "the lane must never refute"
        );
    }

    /// Local search cannot refute, so a propositionally-false assertion set is
    /// declined outright rather than searched forever.
    #[test]
    fn lane_declines_syntactically_false_assertion() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let ge = terms.mk_ge(x, one);
        let le = terms.mk_le(x, zero);
        let root = terms.mk_and(vec![ge, le]);

        let mut solver = NiaSolver::new(&terms);
        solver.set_deadline(ay_core::time::Instant::now() + std::time::Duration::from_millis(200));
        solver.set_root_assertions(vec![root]);
        solver.assert_literal(ge, true);
        solver.assert_literal(le, true);
        assert!(solver.try_clausal_local_search().is_none());
    }

    /// The lane is attempted at most once per solver instance: the search does
    /// not depend on the SAT trail, so re-running it on every `check()` would
    /// only burn wall budget.
    #[test]
    fn lane_runs_at_most_once_per_instance() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let xx = terms.mk_mul(vec![x, x]);
        let two = terms.mk_int(BigInt::from(2));
        let root = terms.mk_eq(xx, two);

        let mut solver = NiaSolver::new(&terms);
        solver.set_deadline(ay_core::time::Instant::now() + std::time::Duration::from_millis(100));
        solver.set_root_assertions(vec![root]);
        solver.assert_literal(root, true);
        assert!(solver.try_clausal_local_search().is_none());
        let t0 = ay_core::time::Instant::now();
        assert!(solver.try_clausal_local_search().is_none());
        assert!(
            t0.elapsed() < std::time::Duration::from_millis(50),
            "second call must return immediately"
        );
    }

    /// No root assertions installed => the lane is inert (this is what keeps
    /// every non-NIA caller of `NiaSolver` unaffected).
    #[test]
    fn lane_inert_without_roots() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let ge = terms.mk_ge(x, zero);
        let mut solver = NiaSolver::new(&terms);
        solver.assert_literal(ge, true);
        assert!(solver.try_clausal_local_search().is_none());
    }

    /// `eval_formula_exact` is the gate every witness passes. It must handle
    /// nested Boolean structure and stay fail-closed on anything else.
    #[test]
    fn eval_formula_exact_handles_nested_structure() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let xy = terms.mk_mul(vec![x, y]);
        let six = terms.mk_int(BigInt::from(6));
        let ten = terms.mk_int(BigInt::from(10));
        let eq6 = terms.mk_eq(xy, six);
        let eq10 = terms.mk_eq(xy, ten);
        let root = terms.mk_or(vec![eq6, eq10]);
        let nested = terms.mk_and(vec![root, eq6]);
        let solver = NiaSolver::new(&terms);

        let mut m: HashMap<TermId, i64> = HashMap::default();
        m.insert(x, 2);
        m.insert(y, 3);
        assert_eq!(solver.eval_formula_exact(root, true, &m), Some(true));
        assert_eq!(solver.eval_formula_exact(root, false, &m), Some(false));

        m.insert(y, 4);
        assert_eq!(solver.eval_formula_exact(root, true, &m), Some(false));

        m.insert(y, 3);
        assert_eq!(solver.eval_formula_exact(nested, true, &m), Some(true));
        m.insert(y, 5);
        assert_eq!(solver.eval_formula_exact(nested, true, &m), Some(false));
    }
}
