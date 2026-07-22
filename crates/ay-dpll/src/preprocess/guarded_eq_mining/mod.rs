// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GuardedEqMining preprocessing pass (#23 keystone).
//!
//! Bool-guarded equality networks — `(or g (= a b))` / `(or (not g) (= c d))`
//! chains plus unguarded unit equalities — force DPLL(T) into per-branch
//! re-derivation of the same linear facts (measured 33k conflicts / 64k LRA
//! checks on the lustre SYNAPSE_2 1-induction check; z3 closes it in 0.02s).
//!
//! This pass mines linear equations that hold under EVERY guard valuation:
//!
//! 1. Parse unguarded unit equalities into base rows and group 2-literal
//!    guarded clauses by their Bool guard variable into a true-branch /
//!    false-branch row set per guard.
//! 2. Fixpoint: for each guard `g`, compute the intersection of the implied
//!    equation spaces `span(U ∪ T_g) ∩ span(U ∪ F_g)` (Zassenhaus over exact
//!    `BigRational` rows). Every intersection row holds whether `g` is true or
//!    false, so it is entailed by the assertion set; add it to `U` and repeat.
//! 3. Any equality atom in the assertion DAG whose row reduces to `0 = 0`
//!    against `U` is entailed true; a residual `0 = c` (`c != 0`) means the
//!    atom is entailed false.
//!
//! # Output shape (hard design constraints — both alternatives were
//! empirically falsified)
//!
//! - Entailed atoms are folded to `true`/`false` IN PLACE and the atom (or its
//!   negation) is re-asserted as a unit. `F[A -> true] ∧ A ≡ F ∧ A`, so the
//!   transform is an exact logical equivalence whenever `F ⊨ A`. Nothing is
//!   deleted and no variables are eliminated.
//! - Mined equations are NEVER emitted as additive standalone assertions
//!   (measured to regress the repro from 45s to a 60s timeout).
//! - No arithmetic ITE terms are constructed (task #28 landmine).
//!
//! # Soundness
//!
//! A wrong fold could flip a sat instance to unsat, so every mined verdict is
//! re-verified by an independent second reduction with a REVERSED column
//! order (different pivot sequence); candidates whose verdicts disagree are
//! dropped. All arithmetic is exact `BigRational`. The wiring site disables
//! the pass under proof production.

use super::PreprocessingPass;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_rational::BigRational;
use num_traits::Zero;

/// Red zone size for `stacker::maybe_grow` in DAG recursion (#8414).
const GEQ_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for DAG recursion.
const GEQ_STACK_SIZE: usize = 1024 * 1024;

/// Sentinel column for the right-hand-side constant of an equation row.
/// Sorts after every coefficient column, so it is only ever chosen as a
/// "pivot" when a row has degenerated to `0 = c` (inconsistency witness).
const RHS_COL: u32 = u32::MAX;

/// Caps keeping the pass deterministic and cheap on shapes it cannot help.
const MAX_COLUMNS: usize = 2048;
const MAX_GUARDS: usize = 1024;
const MAX_INPUT_ROWS: usize = 4096;
const MAX_BASIS_ROWS: usize = 1024;
const MAX_SWEEPS: usize = 16;
/// Element-operation fuel for all eliminations (both reductions combined).
const FUEL: u64 = 20_000_000;

/// A sparse linear equation `sum coeff_i * col_i = rhs` over compact column
/// indices. Entries are sorted by column; the rhs lives at [`RHS_COL`].
type SRow = Vec<(u32, BigRational)>;

/// A linear equation over leaf terms: `sum coeff_i * leaf_i = rhs`.
/// Leaves are variables or opaque numeric subterms (sound: any model assigns
/// each leaf SOME value, and linear combinations of true equations are true).
/// Shared with the `eq_diffvar` pass (same crate), which reuses the exact
/// same linear normal form for difference-variable canonicalization.
#[derive(Clone, Debug)]
pub(crate) struct TermRow {
    pub(crate) coeffs: Vec<(TermId, BigRational)>,
    pub(crate) rhs: BigRational,
}

/// Guarded clause rows grouped per Bool guard variable.
struct GuardGroup {
    /// Rows implied when the guard is true (from `(or (not g) eq)`).
    t_rows: Vec<TermRow>,
    /// Rows implied when the guard is false (from `(or g eq)`).
    f_rows: Vec<TermRow>,
}

/// `dst -= c * src` on sparse rows (exact rational arithmetic).
/// Returns the number of element operations performed (fuel accounting).
fn axpy(dst: &mut SRow, c: &BigRational, src: &SRow) -> u64 {
    let mut out: SRow = Vec::with_capacity(dst.len() + src.len());
    let mut i = 0;
    let mut j = 0;
    while i < dst.len() && j < src.len() {
        match dst[i].0.cmp(&src[j].0) {
            std::cmp::Ordering::Less => {
                out.push(std::mem::take(&mut dst[i]));
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                let v = -(c * &src[j].1);
                if !v.is_zero() {
                    out.push((src[j].0, v));
                }
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                let v = &dst[i].1 - c * &src[j].1;
                if !v.is_zero() {
                    out.push((dst[i].0, v));
                }
                i += 1;
                j += 1;
            }
        }
    }
    while i < dst.len() {
        out.push(std::mem::take(&mut dst[i]));
        i += 1;
    }
    while j < src.len() {
        let v = -(c * &src[j].1);
        if !v.is_zero() {
            out.push((src[j].0, v));
        }
        j += 1;
    }
    let ops = (dst.len() + src.len()) as u64;
    *dst = out;
    ops
}

/// Outcome of inserting a row into a [`Basis`].
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum Insert {
    /// Row already in the span.
    Absorbed,
    /// Row added as a new basis row.
    Added,
    /// Row reduced to `0 = c` with `c != 0` (equation bases only).
    Inconsistent,
}

/// Exact-arithmetic RREF basis: each row's pivot column is unique and is
/// eliminated from every other row, so residuals are canonical.
struct Basis {
    rows: Vec<SRow>,
    pivot_of_col: HashMap<u32, usize>,
    fuel: u64,
}

impl Basis {
    fn new(fuel: u64) -> Self {
        Self {
            rows: Vec::new(),
            pivot_of_col: HashMap::default(),
            fuel,
        }
    }

    fn spend(&mut self, ops: u64) -> bool {
        if self.fuel < ops {
            self.fuel = 0;
            return false;
        }
        self.fuel -= ops;
        true
    }

    fn out_of_fuel(&self) -> bool {
        self.fuel == 0
    }

    /// Reduce `row` against the basis. With the RREF invariant, eliminating a
    /// pivot column never reintroduces other pivot columns, so the loop ends
    /// after at most `rows.len()` eliminations.
    fn residual(&mut self, row: &SRow) -> SRow {
        let mut r = row.clone();
        loop {
            let mut hit = None;
            for (idx, (col, _)) in r.iter().enumerate() {
                if let Some(&ri) = self.pivot_of_col.get(col) {
                    hit = Some((idx, ri));
                    break;
                }
            }
            let Some((idx, ri)) = hit else { break };
            let c = r[idx].1.clone();
            let ops = axpy(&mut r, &c, &self.rows[ri]);
            if !self.spend(ops) {
                return r; // fuel exhausted; caller checks out_of_fuel()
            }
        }
        r
    }

    /// Insert a row, maintaining the RREF invariant.
    fn insert(&mut self, row: &SRow) -> Insert {
        let mut r = self.residual(row);
        if self.out_of_fuel() {
            return Insert::Absorbed; // caller checks out_of_fuel() and bails
        }
        if r.is_empty() {
            return Insert::Absorbed;
        }
        let pivot_col = r[0].0;
        if pivot_col == RHS_COL {
            return Insert::Inconsistent;
        }
        // Normalize the pivot coefficient to 1.
        let lead = r[0].1.clone();
        for (_, v) in r.iter_mut() {
            *v /= &lead;
        }
        // Back-eliminate the new pivot from all existing rows.
        for i in 0..self.rows.len() {
            if let Some(pos) = self.rows[i].iter().position(|(c, _)| *c == pivot_col) {
                let c = self.rows[i][pos].1.clone();
                let mut tmp = std::mem::take(&mut self.rows[i]);
                let ops = axpy(&mut tmp, &c, &r);
                self.rows[i] = tmp;
                if !self.spend(ops) {
                    return Insert::Absorbed; // caller checks out_of_fuel()
                }
            }
        }
        self.pivot_of_col.insert(pivot_col, self.rows.len());
        self.rows.push(r);
        Insert::Added
    }
}

/// Verdict for a candidate equality atom against the mined basis.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    EntailedTrue,
    EntailedFalse,
}

/// Guarded-equality mining pass. See module docs.
pub(crate) struct GuardedEqMining {
    /// Rewrite cache for the folding phase.
    cache: HashMap<TermId, TermId>,
    /// Atom -> replacement constant (true/false) for the folding phase.
    fold_map: HashMap<TermId, TermId>,
    /// Stats: equations mined beyond the unguarded base rows (primary run).
    pub(crate) mined_rows: u64,
    /// Stats: atoms folded to a constant (each paired with a unit re-assert).
    pub(crate) folded_atoms: u64,
    /// Stats: guards with both a true-branch and a false-branch row set.
    pub(crate) guards_two_sided: u64,
}

impl GuardedEqMining {
    pub(crate) fn new() -> Self {
        Self {
            cache: HashMap::default(),
            fold_map: HashMap::default(),
            mined_rows: 0,
            folded_atoms: 0,
            guards_two_sided: 0,
        }
    }

    /// True when the sort is numeric (Int or Real).
    pub(crate) fn is_numeric_sort(sort: &Sort) -> bool {
        matches!(sort, Sort::Int | Sort::Real)
    }

    /// Try to read a term as a rational constant (Int, Rational, or unary
    /// minus of one).
    fn as_constant(terms: &TermStore, term: TermId) -> Option<BigRational> {
        match terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
            TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
            TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
                Self::as_constant(terms, args[0]).map(|c| -c)
            }
            _ => None,
        }
    }

    /// Accumulate `scale * term` into a sparse leaf->coeff map.
    ///
    /// Total: any numeric subterm that is not +, n-ary -, constant, or
    /// constant-multiplication becomes an opaque leaf keyed by its TermId.
    /// Treating subterms as uninterpreted leaves is sound: linear
    /// combinations of true equations remain true for any leaf valuation.
    fn accumulate(
        terms: &TermStore,
        term: TermId,
        scale: &BigRational,
        coeffs: &mut HashMap<TermId, BigRational>,
        konst: &mut BigRational,
    ) {
        stacker::maybe_grow(GEQ_STACK_RED_ZONE, GEQ_STACK_SIZE, || {
            if let Some(c) = Self::as_constant(terms, term) {
                *konst += scale * c;
                return;
            }
            match terms.get(term) {
                TermData::App(Symbol::Named(name), args) => match name.as_str() {
                    "+" => {
                        for &arg in args.clone().iter() {
                            Self::accumulate(terms, arg, scale, coeffs, konst);
                        }
                    }
                    // SMT-LIB unary minus is negation; n-ary is left-fold
                    // subtraction (first argument positive, rest negative).
                    "-" if args.len() == 1 => {
                        let arg = args[0];
                        let neg = -scale.clone();
                        Self::accumulate(terms, arg, &neg, coeffs, konst);
                    }
                    "-" if args.len() >= 2 => {
                        let args = args.clone();
                        Self::accumulate(terms, args[0], scale, coeffs, konst);
                        let neg = -scale.clone();
                        for &arg in &args[1..] {
                            Self::accumulate(terms, arg, &neg, coeffs, konst);
                        }
                    }
                    "*" => {
                        let args = args.clone();
                        let mut factor = scale.clone();
                        let mut residue: Vec<TermId> = Vec::new();
                        for &arg in args.iter() {
                            match Self::as_constant(terms, arg) {
                                Some(c) => factor *= c,
                                None => residue.push(arg),
                            }
                        }
                        match residue.len() {
                            0 => *konst += factor,
                            1 => Self::accumulate(terms, residue[0], &factor, coeffs, konst),
                            // Non-linear product: opaque leaf.
                            _ => *coeffs.entry(term).or_insert_with(BigRational::zero) += scale,
                        }
                    }
                    _ => {
                        *coeffs.entry(term).or_insert_with(BigRational::zero) += scale;
                    }
                },
                // Variables, ITEs, selects, ... : opaque numeric leaf.
                _ => {
                    *coeffs.entry(term).or_insert_with(BigRational::zero) += scale;
                }
            }
        })
    }

    /// Parse a numeric equality atom `(= a b)` into a [`TermRow`]
    /// (`a - b = 0` rearranged to `coeffs = rhs`).
    pub(crate) fn parse_eq_atom(terms: &TermStore, atom: TermId) -> Option<TermRow> {
        let TermData::App(sym, args) = terms.get(atom) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        let (lhs, rhs) = (args[0], args[1]);
        if !Self::is_numeric_sort(terms.sort(lhs)) || !Self::is_numeric_sort(terms.sort(rhs)) {
            return None;
        }
        let mut coeffs: HashMap<TermId, BigRational> = HashMap::default();
        let mut konst = BigRational::zero();
        let one = BigRational::from_integer(1.into());
        let neg_one = -one.clone();
        Self::accumulate(terms, lhs, &one, &mut coeffs, &mut konst);
        Self::accumulate(terms, rhs, &neg_one, &mut coeffs, &mut konst);
        let mut entries: Vec<(TermId, BigRational)> =
            coeffs.into_iter().filter(|(_, c)| !c.is_zero()).collect();
        entries.sort_by_key(|(t, _)| t.index());
        Some(TermRow {
            coeffs: entries,
            rhs: -konst,
        })
    }

    /// Decompose a 2-literal `or` clause into (guard term, guard polarity
    /// when the equality is implied, equality row). `(or G eq)` implies eq
    /// when G is FALSE; `(or (not G) eq)` implies eq when G is TRUE.
    ///
    /// The guard may be ANY Bool term (variable, comparison atom, ...): after
    /// variable substitution, lustre guards like `v41_1` become comparison
    /// atoms (`(<= 1 v13)`), and grouping is keyed purely by the guard's
    /// TermId. Using only the branch equalities (and not the guard's own
    /// meaning) is sound: it under-approximates what each branch implies.
    fn parse_guarded_clause(
        terms: &TermStore,
        assertion: TermId,
    ) -> Option<(TermId, bool, TermRow)> {
        let TermData::App(sym, args) = terms.get(assertion) else {
            return None;
        };
        if sym.name() != "or" || args.len() != 2 {
            return None;
        }
        let args = [args[0], args[1]];
        for (lit, other) in [(args[0], args[1]), (args[1], args[0])] {
            let (gterm, implied_when) = match terms.get(lit) {
                TermData::Not(inner) => (*inner, true),
                TermData::Const(_) => continue,
                _ => (lit, false),
            };
            if *terms.sort(gterm) != Sort::Bool || matches!(terms.get(gterm), TermData::Const(_)) {
                continue;
            }
            if let Some(row) = Self::parse_eq_atom(terms, other) {
                return Some((gterm, implied_when, row));
            }
        }
        None
    }

    /// Collect every numeric equality atom in the assertion DAGs, plus the
    /// set of atoms that occur somewhere other than as a whole top-level
    /// assertion (only those are worth folding).
    pub(crate) fn collect_atoms(
        terms: &TermStore,
        assertions: &[TermId],
    ) -> (Vec<TermId>, HashSet<TermId>) {
        fn walk(
            terms: &TermStore,
            term: TermId,
            is_root: bool,
            visited_nested: &mut HashSet<TermId>,
            seen: &mut HashSet<TermId>,
            atoms: &mut Vec<TermId>,
            nested: &mut HashSet<TermId>,
        ) {
            stacker::maybe_grow(GEQ_STACK_RED_ZONE, GEQ_STACK_SIZE, || {
                if !is_root && !visited_nested.insert(term) {
                    return;
                }
                let is_eq_atom = match terms.get(term) {
                    TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                        GuardedEqMining::is_numeric_sort(terms.sort(args[0]))
                            && GuardedEqMining::is_numeric_sort(terms.sort(args[1]))
                    }
                    _ => false,
                };
                if is_eq_atom {
                    if seen.insert(term) {
                        atoms.push(term);
                    }
                    if !is_root {
                        nested.insert(term);
                    }
                }
                match terms.get(term) {
                    TermData::App(_, args) => {
                        for &arg in args.clone().iter() {
                            walk(terms, arg, false, visited_nested, seen, atoms, nested);
                        }
                    }
                    TermData::Not(inner) => {
                        walk(terms, *inner, false, visited_nested, seen, atoms, nested);
                    }
                    TermData::Ite(c, t, e) => {
                        for arg in [*c, *t, *e] {
                            walk(terms, arg, false, visited_nested, seen, atoms, nested);
                        }
                    }
                    TermData::Let(bindings, body) => {
                        let body = *body;
                        for (_, b) in bindings.clone() {
                            walk(terms, b, false, visited_nested, seen, atoms, nested);
                        }
                        walk(terms, body, false, visited_nested, seen, atoms, nested);
                    }
                    // Quantified bodies reference bound variables; mining over
                    // them would be unsound. Skip.
                    TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {}
                    TermData::Const(_) | TermData::Var(_, _) => {}
                    _ => {}
                }
            })
        }

        let mut visited_nested = HashSet::default();
        let mut seen = HashSet::default();
        let mut atoms = Vec::new();
        let mut nested = HashSet::default();
        for &assertion in assertions {
            walk(
                terms,
                assertion,
                true,
                &mut visited_nested,
                &mut seen,
                &mut atoms,
                &mut nested,
            );
        }
        (atoms, nested)
    }

    /// Convert a [`TermRow`] to a sparse column row under a column mapping.
    fn to_srow(row: &TermRow, col_of: &HashMap<TermId, u32>) -> SRow {
        let mut out: SRow = row
            .coeffs
            .iter()
            .map(|(t, c)| (col_of[t], c.clone()))
            .collect();
        if !row.rhs.is_zero() {
            out.push((RHS_COL, row.rhs.clone()));
        }
        out.sort_by_key(|(c, _)| *c);
        out
    }

    /// Map an equation-row column into the left block of a Zassenhaus row.
    fn z_left(col: u32, ncols: u32) -> u32 {
        if col == RHS_COL {
            ncols
        } else {
            col
        }
    }

    /// Map an equation-row column into the right block of a Zassenhaus row.
    fn z_right(col: u32, ncols: u32) -> u32 {
        if col == RHS_COL {
            2 * ncols + 1
        } else {
            col + ncols + 1
        }
    }

    /// Mine the fixpoint basis of unconditionally-entailed equations.
    ///
    /// Returns `None` when mining must bail (inconsistency at the base level,
    /// joint branch inconsistency, fuel exhaustion, or cap overflow): the
    /// caller then folds nothing.
    fn mine(
        base: &[SRow],
        guards: &[(Vec<SRow>, Vec<SRow>)],
        ncols: u32,
        fuel: u64,
    ) -> Option<Basis> {
        let mut basis = Basis::new(fuel);
        for row in base {
            match basis.insert(row) {
                Insert::Inconsistent => return None,
                _ if basis.out_of_fuel() => return None,
                _ => {}
            }
        }

        for _sweep in 0..MAX_SWEEPS {
            let mut changed = false;
            for (t_rows, f_rows) in guards.iter() {
                if basis.rows.len() >= MAX_BASIS_ROWS {
                    return None;
                }
                // Branch feasibility (relative to the current basis).
                let mut t_branch = Basis::new(basis.fuel);
                t_branch.rows = basis.rows.clone();
                t_branch.pivot_of_col = basis.pivot_of_col.clone();
                let mut t_inconsistent = false;
                for row in t_rows {
                    if t_branch.insert(row) == Insert::Inconsistent {
                        t_inconsistent = true;
                        break;
                    }
                }
                let mut f_branch = Basis::new(t_branch.fuel);
                f_branch.rows = basis.rows.clone();
                f_branch.pivot_of_col = basis.pivot_of_col.clone();
                let mut f_inconsistent = false;
                for row in f_rows {
                    if f_branch.insert(row) == Insert::Inconsistent {
                        f_inconsistent = true;
                        break;
                    }
                }
                basis.fuel = f_branch.fuel;
                if basis.out_of_fuel() {
                    return None;
                }

                match (t_inconsistent, f_inconsistent) {
                    // Both branches contradict the entailed rows: the formula
                    // is unsat, but leave that discovery to the solver.
                    (true, true) => return None,
                    // One branch infeasible: the guard is forced, so the
                    // other branch's equations hold unconditionally.
                    (true, false) => {
                        for row in f_rows {
                            match basis.insert(row) {
                                Insert::Added => changed = true,
                                Insert::Inconsistent => return None,
                                Insert::Absorbed => {}
                            }
                            if basis.out_of_fuel() {
                                return None;
                            }
                        }
                    }
                    (false, true) => {
                        for row in t_rows {
                            match basis.insert(row) {
                                Insert::Added => changed = true,
                                Insert::Inconsistent => return None,
                                Insert::Absorbed => {}
                            }
                            if basis.out_of_fuel() {
                                return None;
                            }
                        }
                    }
                    (false, false) => {
                        // Zassenhaus intersection of the two branch spans.
                        // Rows: [a | a] for the true branch, [b | 0] for the
                        // false branch; reduced rows with an all-zero left
                        // block span exactly span(A) ∩ span(B).
                        let mut z = Basis::new(basis.fuel);
                        for row in basis.rows.iter().chain(t_rows.iter()) {
                            let mut zr: SRow = Vec::with_capacity(row.len() * 2);
                            for (c, v) in row {
                                zr.push((Self::z_left(*c, ncols), v.clone()));
                            }
                            for (c, v) in row {
                                zr.push((Self::z_right(*c, ncols), v.clone()));
                            }
                            zr.sort_by_key(|(c, _)| *c);
                            z.insert(&zr);
                            if z.out_of_fuel() {
                                return None;
                            }
                        }
                        for row in basis.rows.iter().chain(f_rows.iter()) {
                            let zr: SRow = row
                                .iter()
                                .map(|(c, v)| (Self::z_left(*c, ncols), v.clone()))
                                .collect();
                            z.insert(&zr);
                            if z.out_of_fuel() {
                                return None;
                            }
                        }
                        basis.fuel = z.fuel;
                        // Extract intersection rows (left block all zero).
                        let mut mined: Vec<SRow> = Vec::new();
                        for zrow in &z.rows {
                            if zrow.iter().all(|(c, _)| *c > ncols) {
                                let mut row: SRow = zrow
                                    .iter()
                                    .map(|(c, v)| {
                                        let col = if *c == 2 * ncols + 1 {
                                            RHS_COL
                                        } else {
                                            *c - ncols - 1
                                        };
                                        (col, v.clone())
                                    })
                                    .collect();
                                row.sort_by_key(|(c, _)| *c);
                                mined.push(row);
                            }
                        }
                        for row in &mined {
                            match basis.insert(row) {
                                Insert::Added => changed = true,
                                // An inconsistency among entailed rows means
                                // the formula is unsat; leave it to the solver.
                                Insert::Inconsistent => return None,
                                Insert::Absorbed => {}
                            }
                            if basis.out_of_fuel() {
                                return None;
                            }
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        Some(basis)
    }

    /// Classify a candidate row against a mined basis.
    fn classify(basis: &mut Basis, row: &SRow) -> Option<Verdict> {
        let residual = basis.residual(row);
        if basis.out_of_fuel() {
            return None;
        }
        if residual.is_empty() {
            Some(Verdict::EntailedTrue)
        } else if residual.len() == 1 && residual[0].0 == RHS_COL {
            Some(Verdict::EntailedFalse)
        } else {
            None
        }
    }

    /// Bottom-up rewrite folding entailed atoms to constants. Mirrors
    /// `PropagateValues::rewrite`: check the fold map first, then rebuild
    /// through canonical constructors so Boolean constants simplify away.
    /// Only Bool atoms are replaced by Bool constants, so no arithmetic ITE
    /// terms can be created (task #28 constraint).
    fn fold(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        stacker::maybe_grow(GEQ_STACK_RED_ZONE, GEQ_STACK_SIZE, || {
            if let Some(&cached) = self.cache.get(&term) {
                return cached;
            }
            if let Some(&value) = self.fold_map.get(&term) {
                self.cache.insert(term, value);
                return value;
            }
            let result = match terms.get(term).clone() {
                TermData::Const(_) | TermData::Var(_, _) => term,
                TermData::App(sym, args) => {
                    let new_args: Vec<TermId> = args.iter().map(|&a| self.fold(terms, a)).collect();
                    if new_args == args {
                        term
                    } else {
                        match sym.name() {
                            "=" if new_args.len() == 2 => {
                                terms.mk_eq_coerce(new_args[0], new_args[1])
                            }
                            "and" => terms.mk_and(new_args),
                            "or" => terms.mk_or(new_args),
                            "not" if new_args.len() == 1 => terms.mk_not(new_args[0]),
                            "=>" if new_args.len() == 2 => {
                                terms.mk_implies(new_args[0], new_args[1])
                            }
                            "xor" if new_args.len() == 2 => terms.mk_xor(new_args[0], new_args[1]),
                            "distinct" => terms.mk_distinct(new_args),
                            "ite" if new_args.len() == 3 => {
                                terms.mk_ite(new_args[0], new_args[1], new_args[2])
                            }
                            _ => {
                                let sort = terms.sort(term).clone();
                                terms.mk_app(sym.clone(), new_args, sort)
                            }
                        }
                    }
                }
                TermData::Not(inner) => {
                    let new_inner = self.fold(terms, inner);
                    if new_inner == inner {
                        term
                    } else {
                        terms.mk_not(new_inner)
                    }
                }
                TermData::Ite(c, t, e) => {
                    let nc = self.fold(terms, c);
                    let nt = self.fold(terms, t);
                    let ne = self.fold(terms, e);
                    if nc == c && nt == t && ne == e {
                        term
                    } else {
                        terms.mk_ite(nc, nt, ne)
                    }
                }
                // Quantifiers / lets: leave untouched (atoms under binders
                // are never fold candidates; see collect_atoms).
                _ => term,
            };
            self.cache.insert(term, result);
            result
        })
    }

    /// Core of the pass; returns the unit re-assertions appended (empty when
    /// nothing was folded).
    fn apply_inner(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> Vec<TermId> {
        // ---- Phase A: scan top-level assertions ------------------------
        // Every top-level assertion pins its own term true (and `(not T)`
        // pins T false): guards matching a pinned term are decided, so their
        // implied-branch equalities hold unconditionally.
        let mut fixed_bools: HashMap<TermId, bool> = HashMap::default();
        for &assertion in assertions.iter() {
            match terms.get(assertion) {
                TermData::Not(inner) => {
                    fixed_bools.entry(*inner).or_insert(false);
                }
                _ => {
                    fixed_bools.entry(assertion).or_insert(true);
                }
            }
        }

        let mut base_rows: Vec<TermRow> = Vec::new();
        let mut guard_order: Vec<TermId> = Vec::new();
        let mut guard_groups: HashMap<TermId, GuardGroup> = HashMap::default();
        for &assertion in assertions.iter() {
            if let Some(row) = Self::parse_eq_atom(terms, assertion) {
                base_rows.push(row);
                continue;
            }
            if let Some((gvar, implied_when, row)) = Self::parse_guarded_clause(terms, assertion) {
                if let Some(&fixed) = fixed_bools.get(&gvar) {
                    // Pinned guard: the implied-branch equality holds
                    // unconditionally; the other branch clause is satisfied.
                    if fixed == implied_when {
                        base_rows.push(row);
                    }
                    continue;
                }
                let group = guard_groups.entry(gvar).or_insert_with(|| {
                    guard_order.push(gvar);
                    GuardGroup {
                        t_rows: Vec::new(),
                        f_rows: Vec::new(),
                    }
                });
                if implied_when {
                    group.t_rows.push(row);
                } else {
                    group.f_rows.push(row);
                }
            }
        }

        // Only guards constraining both branches can mine new rows.
        let two_sided: Vec<(Vec<TermRow>, Vec<TermRow>)> = guard_order
            .iter()
            .filter_map(|g| {
                let group = guard_groups.remove(g)?;
                (!group.t_rows.is_empty() && !group.f_rows.is_empty())
                    .then_some((group.t_rows, group.f_rows))
            })
            .collect();
        self.guards_two_sided = two_sided.len() as u64;

        if base_rows.is_empty() && two_sided.is_empty() {
            return Vec::new();
        }
        if two_sided.len() > MAX_GUARDS {
            return Vec::new();
        }

        // ---- Phase B: candidate atoms ----------------------------------
        let (atoms, nested) = Self::collect_atoms(terms, assertions);
        // Atoms that only occur as whole top-level assertions are already
        // unit facts; folding them would be pure churn.
        let candidates: Vec<(TermId, TermRow)> = atoms
            .iter()
            .filter(|atom| nested.contains(*atom))
            .filter_map(|&atom| Self::parse_eq_atom(terms, atom).map(|row| (atom, row)))
            .collect();
        if candidates.is_empty() {
            return Vec::new();
        }

        // ---- Phase C: column assignment --------------------------------
        let mut col_order: Vec<TermId> = Vec::new();
        let mut col_seen: HashSet<TermId> = HashSet::default();
        let all_rows = base_rows
            .iter()
            .chain(two_sided.iter().flat_map(|(t, f)| t.iter().chain(f.iter())))
            .chain(candidates.iter().map(|(_, row)| row));
        let mut input_row_count = 0usize;
        for row in all_rows {
            input_row_count += 1;
            for (leaf, _) in &row.coeffs {
                if col_seen.insert(*leaf) {
                    col_order.push(*leaf);
                }
            }
        }
        if col_order.len() > MAX_COLUMNS || input_row_count > MAX_INPUT_ROWS {
            return Vec::new();
        }
        let ncols = col_order.len() as u32;

        let make_cols = |order: &[TermId]| -> HashMap<TermId, u32> {
            order
                .iter()
                .enumerate()
                .map(|(i, t)| (*t, i as u32))
                .collect()
        };

        // ---- Phase D: primary mining run --------------------------------
        let col_of = make_cols(&col_order);
        let base_srows: Vec<SRow> = base_rows
            .iter()
            .map(|r| Self::to_srow(r, &col_of))
            .collect();
        let guard_srows: Vec<(Vec<SRow>, Vec<SRow>)> = two_sided
            .iter()
            .map(|(t, f)| {
                (
                    t.iter().map(|r| Self::to_srow(r, &col_of)).collect(),
                    f.iter().map(|r| Self::to_srow(r, &col_of)).collect(),
                )
            })
            .collect();
        let Some(mut basis) = Self::mine(&base_srows, &guard_srows, ncols, FUEL / 2) else {
            return Vec::new();
        };
        let base_rank = {
            // Rank of the unguarded rows alone, to report mined-row stats.
            let mut b = Basis::new(FUEL / 8);
            let mut rank = 0u64;
            for row in &base_srows {
                if b.insert(row) == Insert::Added {
                    rank += 1;
                }
            }
            rank
        };
        self.mined_rows = (basis.rows.len() as u64).saturating_sub(base_rank);

        let mut verdicts: Vec<(TermId, Verdict)> = Vec::new();
        for (atom, row) in &candidates {
            let srow = Self::to_srow(row, &col_of);
            if let Some(verdict) = Self::classify(&mut basis, &srow) {
                verdicts.push((*atom, verdict));
            }
            if basis.out_of_fuel() {
                return Vec::new();
            }
        }
        if verdicts.is_empty() {
            return Vec::new();
        }

        // ---- Phase E: independent second reduction (reversed pivot order)
        // Soundness gate: a wrong fold could flip sat to unsat, so every
        // verdict must be re-derived with a different pivot sequence.
        let mut rev_order = col_order.clone();
        rev_order.reverse();
        let col_of_rev = make_cols(&rev_order);
        let base_rev: Vec<SRow> = base_rows
            .iter()
            .rev()
            .map(|r| Self::to_srow(r, &col_of_rev))
            .collect();
        let guard_rev: Vec<(Vec<SRow>, Vec<SRow>)> = two_sided
            .iter()
            .rev()
            .map(|(t, f)| {
                (
                    t.iter().map(|r| Self::to_srow(r, &col_of_rev)).collect(),
                    f.iter().map(|r| Self::to_srow(r, &col_of_rev)).collect(),
                )
            })
            .collect();
        let Some(mut basis2) = Self::mine(&base_rev, &guard_rev, ncols, FUEL / 2) else {
            return Vec::new();
        };
        let confirmed: Vec<(TermId, Verdict)> = verdicts
            .into_iter()
            .filter(|(atom, verdict)| {
                let row = candidates
                    .iter()
                    .find(|(a, _)| a == atom)
                    .map(|(_, r)| Self::to_srow(r, &col_of_rev));
                match row {
                    Some(srow) => Self::classify(&mut basis2, &srow) == Some(*verdict),
                    None => false,
                }
            })
            .collect();
        if basis2.out_of_fuel() || confirmed.is_empty() {
            return Vec::new();
        }

        // ---- Phase F: fold to constants + paired unit re-assertions ----
        // F[A -> true] ∧ A ≡ F ∧ A and F ⊨ A, so the transform is an exact
        // logical equivalence. Mined equations are never added on their own.
        let true_term = terms.true_term();
        let false_term = terms.false_term();
        self.fold_map.clear();
        self.cache.clear();
        let mut units: Vec<TermId> = Vec::new();
        for &(atom, verdict) in &confirmed {
            match verdict {
                Verdict::EntailedTrue => {
                    self.fold_map.insert(atom, true_term);
                    units.push(atom);
                }
                Verdict::EntailedFalse => {
                    self.fold_map.insert(atom, false_term);
                    units.push(terms.mk_not(atom));
                }
            }
        }
        self.folded_atoms = confirmed.len() as u64;
        for assertion in assertions.iter_mut() {
            *assertion = self.fold(terms, *assertion);
        }
        assertions.extend(units.iter().copied());
        units
    }
}

impl Default for GuardedEqMining {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for GuardedEqMining {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        !self.apply_inner(terms, assertions).is_empty()
    }

    fn apply_with_sources(
        &mut self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
        source_sets: &mut Vec<Vec<TermId>>,
    ) -> bool {
        debug_assert_eq!(assertions.len(), source_sets.len());
        // Snapshot to detect which assertions Phase F rewrites: a folded
        // assertion's new content is justified by the whole guarded-equality
        // network, so its provenance must be WIDENED to the fold justification
        // (mirroring augment_lia_source_sets_with_substitutions for
        // VariableSubstitution). With only positional provenance, incremental
        // sessions could assign a folded assertion an activation depth
        // shallower than the scoped assertions that justified the fold and
        // keep it past the pop that retracts the justifiers — a latent
        // wrong-unsat.
        let before: Vec<TermId> = assertions.clone();
        let units = self.apply_inner(terms, assertions);
        if units.is_empty() {
            debug_assert_eq!(assertions.len(), source_sets.len());
            return false;
        }
        // Union of all original sources: each mined unit (and each rewritten
        // assertion) is justified by the whole guarded-equality network, not a
        // single source assertion.
        let mut union_sources: Vec<TermId> = source_sets.iter().flatten().copied().collect();
        union_sources.sort_by_key(|t| t.index());
        union_sources.dedup();
        for (i, &old) in before.iter().enumerate() {
            if assertions[i] != old {
                let set = &mut source_sets[i];
                set.extend(union_sources.iter().copied());
                set.sort_by_key(|t| t.index());
                set.dedup();
            }
        }
        for _ in 0..units.len() {
            source_sets.push(union_sources.clone());
        }
        debug_assert_eq!(assertions.len(), source_sets.len());
        true
    }

    fn reset(&mut self) {
        self.cache.clear();
        self.fold_map.clear();
    }
}

#[cfg(test)]
mod tests;
