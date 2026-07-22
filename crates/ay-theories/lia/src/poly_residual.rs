// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Polynomial-residual conflict detection for nonlinear arithmetic atoms.
//!
//! LRA treats nonlinear products (`x*y`, `x*x`) and non-constant `div`/`mod`
//! applications as *unsupported*: their atoms are skipped during bound
//! assertion and the relaxation degrades to `Unknown` ("sat with unsupported
//! atoms"). Branch-and-bound then stalls: once every integer variable is
//! pinned by splits, `find_unsplit_integer_var` has nothing left to split and
//! the whole DPLL(T) query collapses to `Unknown` — even when the asserted
//! nonlinear atoms are *evaluably* contradictory.
//!
//! This module recovers sound conflicts from such assignments by normalizing
//! every asserted arithmetic atom into a **polynomial residual**: an exact
//! multivariate polynomial over *opaque factors* (variables, UF/`div`/`mod`/
//! ITE applications), with LRA-fixed variables substituted by their values.
//! Four checks run to a pinning fixpoint:
//!
//! 1. **Constant truth**: a residual with no remaining monomials evaluates to
//!    a ground truth value; disagreement with the asserted polarity is a
//!    conflict. (E.g. `2*sum = -n - n*n + 30` asserted false with `n = 5`,
//!    `sum = 0` pinned: `0 = 0` is true — conflict.)
//! 2. **Residual identity**: two equality atoms whose residuals share the
//!    same canonical variable part are related by a ring identity valid for
//!    *every* assignment. Same constant with opposite polarities, or
//!    different constants both asserted true, is a conflict. (E.g. the
//!    accumulator consecution `2s = -i + i*i` (true) vs
//!    `2(s+i) = -(i+1) + (i+1)*(i+1)` (false): both expand to the residual
//!    `2s + i - [i*i]`, so the pair is contradictory with **no** branching.)
//! 3. **Divisibility (GCD)**: an equality residual over integer-valued
//!    monomials whose coefficient GCD does not divide the constant has no
//!    integer solution.
//! 4. **Pinning**: an equality residual that is affine in a single remaining
//!    factor forces that factor's value (or is immediately infeasible if the
//!    factor is integer-valued and the forced value is fractional); the pin
//!    is added to the substitution and the pass repeats.
//!
//! Soundness: every returned conflict lists currently-asserted literals whose
//! conjunction is arithmetically infeasible. Substituted values carry the
//! complete reason sets of the LRA bounds that fixed them
//! (`Bound::complete_reason_pairs`, #8151 provenance-aware), pins carry the
//! equality atom plus its own evaluation reasons, and ring identities need no
//! reasons at all. A final liveness guard re-verifies every literal against
//! the current assertion trail before the conflict is reported.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::{Sort, TheoryLit};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::types::positive_mod;
use crate::LiaSolver;

/// Maximum number of asserted atoms to scan. Larger assignments skip the
/// pass entirely (it is a recovery path, not a decision procedure).
const MAX_RESIDUAL_ATOMS: usize = 256;
/// Maximum distinct monomials in any intermediate polynomial.
const MAX_POLY_MONOMIALS: usize = 32;
/// Maximum degree (factor multiset size) of any monomial.
const MAX_MONOMIAL_DEGREE: usize = 4;
/// Pinning fixpoint rounds. Each round either conflicts, pins at least one
/// new factor, or terminates.
const MAX_PIN_ROUNDS: usize = 8;
/// Total term-node budget for one pass (all atoms, all rounds).
const MAX_EVAL_NODES: usize = 65_536;

/// A monomial: a sorted multiset of opaque factor terms (`[x, x]` is `x²`).
/// The empty monomial is the constant term and never appears in `Poly::terms`.
type Monomial = Vec<TermId>;

/// Per-pinned-value substitution entry: the forced value plus the asserted
/// literals justifying it.
type SubstEntry = (BigRational, Vec<TheoryLit>);

/// Canonical residual key for an equality atom: the scaled monomial part,
/// the scaled constant, and the index of the originating record.
type EqResidualKey = (Vec<(Monomial, BigRational)>, BigRational, usize);

/// An exact multivariate polynomial: `constant + Σ coeff·monomial`.
#[derive(Debug, Clone, Default)]
struct Poly {
    terms: HashMap<Monomial, BigRational>,
    constant: BigRational,
}

impl Poly {
    fn from_constant(c: BigRational) -> Self {
        Self {
            terms: HashMap::default(),
            constant: c,
        }
    }

    fn from_factor(f: TermId) -> Self {
        let mut terms = HashMap::default();
        terms.insert(vec![f], BigRational::one());
        Self {
            terms,
            constant: BigRational::zero(),
        }
    }

    fn add_monomial(&mut self, mono: Monomial, coeff: BigRational) {
        if coeff.is_zero() {
            return;
        }
        if mono.is_empty() {
            self.constant += coeff;
            return;
        }
        if let Some(existing) = self.terms.get_mut(&mono) {
            *existing += coeff;
            if existing.is_zero() {
                self.terms.remove(&mono);
            }
        } else {
            self.terms.insert(mono, coeff);
        }
    }

    fn add_scaled(&mut self, other: &Self, scale: &BigRational) {
        if scale.is_zero() {
            return;
        }
        self.constant += &other.constant * scale;
        for (mono, coeff) in &other.terms {
            self.add_monomial(mono.clone(), coeff * scale);
        }
    }

    fn is_constant(&self) -> bool {
        self.terms.is_empty()
    }

    /// Multiply two polynomials, failing on size/degree blowup.
    fn mul(&self, other: &Self) -> Option<Self> {
        let mut out = Self::from_constant(&self.constant * &other.constant);
        for (mono, coeff) in &self.terms {
            out.add_monomial(mono.clone(), coeff * &other.constant);
        }
        for (mono, coeff) in &other.terms {
            out.add_monomial(mono.clone(), coeff * &self.constant);
        }
        for (m1, c1) in &self.terms {
            for (m2, c2) in &other.terms {
                if m1.len() + m2.len() > MAX_MONOMIAL_DEGREE {
                    return None;
                }
                let mut mono = Vec::with_capacity(m1.len() + m2.len());
                mono.extend_from_slice(m1);
                mono.extend_from_slice(m2);
                mono.sort_unstable();
                out.add_monomial(mono, c1 * c2);
            }
        }
        if out.terms.len() > MAX_POLY_MONOMIALS {
            return None;
        }
        Some(out)
    }

    /// Deterministically sorted non-constant entries.
    fn sorted_monomials(&self) -> Vec<(Monomial, BigRational)> {
        let mut entries: Vec<(Monomial, BigRational)> = self
            .terms
            .iter()
            .map(|(m, c)| (m.clone(), c.clone()))
            .collect();
        entries.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        entries
    }
}

/// Comparison operator of a normalized residual atom (`poly OP 0`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ResidualOp {
    /// `poly = 0`
    Eq,
    /// `poly <= 0`
    Le,
    /// `poly < 0`
    Lt,
}

/// One asserted atom in residual form.
#[derive(Debug)]
struct ResidualAtom {
    /// The asserted literal (atom term + asserted polarity).
    lit: TheoryLit,
    op: ResidualOp,
    poly: Poly,
    /// Literals justifying substituted values used during evaluation.
    reasons: Vec<TheoryLit>,
    /// Whether the *unsubstituted* atom involved a nonlinear monomial or a
    /// `div`/`mod` application (i.e. something LRA cannot natively decide).
    nonlinear: bool,
}

/// Evaluate a term into polynomial form, substituting pinned factors.
///
/// Returns `None` when the term falls outside the supported fragment or a
/// size/degree/node budget is exceeded. Reasons for every substitution used
/// are appended to `used`; `saw_nonlinear` is set when a product of two
/// non-constant polynomials or a `div`/`mod` application is encountered.
fn eval_poly(
    terms: &TermStore,
    term: TermId,
    subst: &HashMap<TermId, SubstEntry>,
    used: &mut Vec<TheoryLit>,
    nodes: &mut usize,
    saw_nonlinear: &mut bool,
) -> Option<Poly> {
    if *nodes == 0 {
        return None;
    }
    *nodes -= 1;

    let opaque_factor = |term: TermId, used: &mut Vec<TheoryLit>| -> Option<Poly> {
        if !matches!(terms.sort(term), Sort::Int | Sort::Real) {
            return None;
        }
        if let Some((value, reasons)) = subst.get(&term) {
            used.extend(reasons.iter().copied());
            return Some(Poly::from_constant(value.clone()));
        }
        Some(Poly::from_factor(term))
    };

    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => {
            Some(Poly::from_constant(BigRational::from(n.clone())))
        }
        TermData::Const(Constant::Rational(w)) => Some(Poly::from_constant(w.0.clone())),
        TermData::Var(_, _) => opaque_factor(term, used),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                let mut out = Poly::default();
                for &arg in args {
                    let p = eval_poly(terms, arg, subst, used, nodes, saw_nonlinear)?;
                    out.add_scaled(&p, &BigRational::one());
                    if out.terms.len() > MAX_POLY_MONOMIALS {
                        return None;
                    }
                }
                Some(out)
            }
            "-" if !args.is_empty() => {
                let mut out = Poly::default();
                if args.len() == 1 {
                    let p = eval_poly(terms, args[0], subst, used, nodes, saw_nonlinear)?;
                    out.add_scaled(&p, &-BigRational::one());
                } else {
                    let first = eval_poly(terms, args[0], subst, used, nodes, saw_nonlinear)?;
                    out.add_scaled(&first, &BigRational::one());
                    for &arg in &args[1..] {
                        let p = eval_poly(terms, arg, subst, used, nodes, saw_nonlinear)?;
                        out.add_scaled(&p, &-BigRational::one());
                        if out.terms.len() > MAX_POLY_MONOMIALS {
                            return None;
                        }
                    }
                }
                Some(out)
            }
            "*" if !args.is_empty() => {
                // Structural nonlinearity (pre-substitution): this is what
                // LRA's parser sees, so it decides whether the pass has any
                // work LRA could not already do.
                let non_const_args = args
                    .iter()
                    .filter(|&&arg| !matches!(terms.get(arg), TermData::Const(_)))
                    .count();
                if non_const_args > 1 {
                    *saw_nonlinear = true;
                }
                let mut out = Poly::from_constant(BigRational::one());
                for &arg in args {
                    let p = eval_poly(terms, arg, subst, used, nodes, saw_nonlinear)?;
                    out = out.mul(&p)?;
                }
                Some(out)
            }
            "div" | "mod" if args.len() == 2 => {
                *saw_nonlinear = true;
                // Constant-fold when both operands ground to integers
                // (SMT-LIB Euclidean semantics); otherwise treat the whole
                // application as an opaque factor.
                let mut sub_used = Vec::new();
                let folded = (|| {
                    let pa = eval_poly(terms, args[0], subst, &mut sub_used, nodes, saw_nonlinear)?;
                    let pb = eval_poly(terms, args[1], subst, &mut sub_used, nodes, saw_nonlinear)?;
                    if !pa.is_constant() || !pb.is_constant() {
                        return None;
                    }
                    if !pa.constant.is_integer() || !pb.constant.is_integer() {
                        return None;
                    }
                    let a = pa.constant.to_integer();
                    let b = pb.constant.to_integer();
                    if b.is_zero() {
                        return None;
                    }
                    let r = positive_mod(&a, &b.abs());
                    let value = if name == "mod" {
                        r
                    } else {
                        // Euclidean quotient: (a - r) / b is exact.
                        (a - &r) / b
                    };
                    Some(Poly::from_constant(BigRational::from(value)))
                })();
                match folded {
                    Some(p) => {
                        used.extend(sub_used);
                        Some(p)
                    }
                    None => opaque_factor(term, used),
                }
            }
            _ => opaque_factor(term, used),
        },
        TermData::Ite(_, _, _) => opaque_factor(term, used),
        _ => None,
    }
}

impl LiaSolver<'_> {
    /// Detect a conflict among asserted atoms via polynomial residuals.
    ///
    /// Called from the `check()` Unknown-recovery path (after LRA degrades on
    /// unsupported nonlinear atoms). Returns `Some(literals)` when the
    /// current assignment is provably arithmetically infeasible; the caller
    /// reports `TheoryResult::Unsat(literals)`.
    pub(crate) fn check_polynomial_residual_conflict(&self) -> Option<Vec<TheoryLit>> {
        if self.asserted.is_empty() || self.asserted.len() > MAX_RESIDUAL_ATOMS {
            return None;
        }

        // Deduplicate asserted atoms, preserving first-seen order.
        let mut seen: HashSet<(TermId, bool)> = HashSet::default();
        let mut atoms: Vec<(TermId, bool)> = Vec::with_capacity(self.asserted.len());
        for &(term, value) in &self.asserted {
            if seen.insert((term, value)) {
                atoms.push((term, value));
            }
        }

        let mut subst = self.fixed_value_substitution();
        let mut nodes = MAX_EVAL_NODES;

        for round in 0..MAX_PIN_ROUNDS {
            if self.should_timeout() {
                return None;
            }
            let records = self.build_residual_atoms(&atoms, &subst, &mut nodes);
            if round == 0 && !records.iter().any(|r| r.nonlinear) {
                // Purely linear assignments are LRA's job; nothing to add.
                return None;
            }

            // 1) Ground truth disagreement.
            for rec in &records {
                if rec.poly.is_constant() {
                    let c = &rec.poly.constant;
                    let truth = match rec.op {
                        ResidualOp::Eq => c.is_zero(),
                        ResidualOp::Le => !c.is_positive(),
                        ResidualOp::Lt => c.is_negative(),
                    };
                    if truth != rec.lit.value {
                        let mut lits = vec![rec.lit];
                        lits.extend(rec.reasons.iter().copied());
                        if let Some(conflict) = self.finish_residual_conflict(lits) {
                            return Some(conflict);
                        }
                    }
                }
            }

            // 2) Divisibility: an integer-monomial equality whose coefficient
            //    GCD does not divide the constant has no solution.
            for rec in &records {
                if rec.op != ResidualOp::Eq || !rec.lit.value || rec.poly.is_constant() {
                    continue;
                }
                if self.residual_gcd_feasible(&rec.poly) == Some(false) {
                    let mut lits = vec![rec.lit];
                    lits.extend(rec.reasons.iter().copied());
                    if let Some(conflict) = self.finish_residual_conflict(lits) {
                        return Some(conflict);
                    }
                }
            }

            // 3) Residual identity: equalities sharing a canonical variable
            //    part are contradictory when their constants disagree (both
            //    true) or agree (one true, one false). The underlying lemma
            //    is a ring identity, valid for every assignment.
            let mut eq_keys: Vec<EqResidualKey> = Vec::new();
            for (idx, rec) in records.iter().enumerate() {
                if rec.op != ResidualOp::Eq || rec.poly.is_constant() {
                    continue;
                }
                let mut entries = rec.poly.sorted_monomials();
                let lead = entries[0].1.clone();
                for entry in &mut entries {
                    entry.1 /= &lead;
                }
                let cst = &rec.poly.constant / &lead;
                eq_keys.push((entries, cst, idx));
            }
            eq_keys.sort_unstable_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
            let mut group_start = 0;
            while group_start < eq_keys.len() {
                let mut group_end = group_start + 1;
                while group_end < eq_keys.len() && eq_keys[group_end].0 == eq_keys[group_start].0 {
                    group_end += 1;
                }
                for first in group_start..group_end {
                    for second in (first + 1)..group_end {
                        let (_, cst_a, idx_a) = &eq_keys[first];
                        let (_, cst_b, idx_b) = &eq_keys[second];
                        let a = &records[*idx_a];
                        let b = &records[*idx_b];
                        let contradictory = match (a.lit.value, b.lit.value) {
                            (true, true) => cst_a != cst_b,
                            (true, false) | (false, true) => cst_a == cst_b,
                            (false, false) => false,
                        };
                        if contradictory {
                            let mut lits = vec![a.lit, b.lit];
                            lits.extend(a.reasons.iter().copied());
                            lits.extend(b.reasons.iter().copied());
                            if let Some(conflict) = self.finish_residual_conflict(lits) {
                                return Some(conflict);
                            }
                        }
                    }
                }
                group_start = group_end;
            }

            // 4) Pinning: `a·f + c = 0` (asserted true, single degree-1
            //    monomial) forces f = -c/a. Fractional forced values for
            //    integer-valued factors are immediate conflicts.
            let mut pinned_new = false;
            for rec in &records {
                if rec.op != ResidualOp::Eq || !rec.lit.value || rec.poly.terms.len() != 1 {
                    continue;
                }
                let (mono, coeff) = rec.poly.terms.iter().next().unwrap();
                if mono.len() != 1 {
                    continue;
                }
                let factor = mono[0];
                if subst.contains_key(&factor) {
                    continue;
                }
                let value = -(&rec.poly.constant / coeff);
                if matches!(self.terms.sort(factor), Sort::Int) && !value.is_integer() {
                    let mut lits = vec![rec.lit];
                    lits.extend(rec.reasons.iter().copied());
                    if let Some(conflict) = self.finish_residual_conflict(lits) {
                        return Some(conflict);
                    }
                    continue;
                }
                let mut reasons = vec![rec.lit];
                reasons.extend(rec.reasons.iter().copied());
                subst.insert(factor, (value, reasons));
                pinned_new = true;
            }
            if !pinned_new {
                return None;
            }
        }
        None
    }

    /// Substitution of LRA-fixed integer variables/opaque terms.
    fn fixed_value_substitution(&self) -> HashMap<TermId, SubstEntry> {
        let mut subst: HashMap<TermId, SubstEntry> = HashMap::default();
        let mut vars: Vec<TermId> = self.integer_vars.iter().copied().collect();
        vars.sort_unstable_by_key(|t| t.0);
        for term in vars {
            let Some((Some(lb), Some(ub))) = self.lra.get_bounds(term) else {
                continue;
            };
            let li = Self::effective_int_lower(&lb);
            let ui = Self::effective_int_upper(&ub);
            if li != ui {
                continue;
            }
            let mut reasons: Vec<TheoryLit> = Vec::new();
            for (t, v) in lb.complete_reason_pairs() {
                reasons.push(TheoryLit::new(t, v));
            }
            for (t, v) in ub.complete_reason_pairs() {
                reasons.push(TheoryLit::new(t, v));
            }
            subst.insert(term, (BigRational::from(li), reasons));
        }
        subst
    }

    /// Normalize asserted comparison atoms into residual form.
    fn build_residual_atoms(
        &self,
        atoms: &[(TermId, bool)],
        subst: &HashMap<TermId, SubstEntry>,
        nodes: &mut usize,
    ) -> Vec<ResidualAtom> {
        let mut out = Vec::new();
        for &(term, value) in atoms {
            let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            // (op, swap): residual is lhs-rhs, or rhs-lhs when swapped.
            let (op, swap) = match name.as_str() {
                "=" => (ResidualOp::Eq, false),
                "<=" => (ResidualOp::Le, false),
                "<" => (ResidualOp::Lt, false),
                ">=" => (ResidualOp::Le, true),
                ">" => (ResidualOp::Lt, true),
                _ => continue,
            };
            if !matches!(self.terms.sort(args[0]), Sort::Int | Sort::Real) {
                continue;
            }
            let mut reasons = Vec::new();
            let mut nonlinear = false;
            let Some(pl) = eval_poly(
                self.terms,
                args[0],
                subst,
                &mut reasons,
                nodes,
                &mut nonlinear,
            ) else {
                continue;
            };
            let Some(pr) = eval_poly(
                self.terms,
                args[1],
                subst,
                &mut reasons,
                nodes,
                &mut nonlinear,
            ) else {
                continue;
            };
            let (pos, neg) = if swap { (pr, pl) } else { (pl, pr) };
            let mut poly = pos;
            poly.add_scaled(&neg, &-BigRational::one());
            out.push(ResidualAtom {
                lit: TheoryLit::new(term, value),
                op,
                poly,
                reasons,
                nonlinear,
            });
        }
        out
    }

    /// GCD feasibility of `poly = 0` over the integers.
    ///
    /// Returns `Some(false)` when provably infeasible, `Some(true)` when the
    /// divisibility test passes, `None` when inapplicable (a factor is not
    /// integer-valued, so monomial values are not guaranteed integral).
    fn residual_gcd_feasible(&self, poly: &Poly) -> Option<bool> {
        for mono in poly.terms.keys() {
            for &factor in mono {
                if !matches!(self.terms.sort(factor), Sort::Int) {
                    return None;
                }
            }
        }
        // Scale to integer coefficients.
        let mut denom_lcm = poly.constant.denom().clone();
        for coeff in poly.terms.values() {
            denom_lcm = denom_lcm.lcm(coeff.denom());
        }
        let scale = BigRational::from(denom_lcm);
        let constant = (&poly.constant * &scale).to_integer();
        let mut gcd = BigInt::zero();
        for coeff in poly.terms.values() {
            gcd = gcd.gcd(&(coeff * &scale).to_integer());
        }
        if gcd.is_zero() {
            return Some(true);
        }
        Some((constant % gcd).is_zero())
    }

    /// Deduplicate, sanity-check, and liveness-guard a conflict literal set.
    fn finish_residual_conflict(&self, lits: Vec<TheoryLit>) -> Option<Vec<TheoryLit>> {
        let mut seen: HashSet<(TermId, bool)> = HashSet::default();
        let mut out: Vec<TheoryLit> = Vec::with_capacity(lits.len());
        for lit in lits {
            if lit.term.is_sentinel() {
                continue;
            }
            if seen.insert((lit.term, lit.value)) {
                out.push(lit);
            }
        }
        if out.is_empty() {
            return None;
        }
        // #8764-style stale-reason guard: every literal must be live, either
        // on LIA's own trail or on LRA's (cross-theory) trail.
        let all_live = out.iter().all(|lit| {
            self.asserted
                .iter()
                .any(|&(t, v)| t == lit.term && v == lit.value)
                || self
                    .lra
                    .conflict_literals_all_asserted(std::slice::from_ref(lit))
        });
        if !all_live {
            return None;
        }
        Some(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{TheoryResult, TheorySolver};

    /// Build `2*sum = -n - n*n + 30` over the given vars.
    fn quadratic_eq(
        terms: &mut TermStore,
        sum_term: TermId,
        n_term: TermId,
        offset: i64,
    ) -> TermId {
        let two = terms.mk_int(BigInt::from(2));
        let neg_one = terms.mk_int(BigInt::from(-1));
        let off = terms.mk_int(BigInt::from(offset));
        let lhs = terms.mk_mul(vec![two, sum_term]);
        let neg_n = terms.mk_mul(vec![neg_one, n_term]);
        let n_sq = terms.mk_mul(vec![n_term, n_term]);
        let neg_n_sq = terms.mk_mul(vec![neg_one, n_sq]);
        let rhs = terms.mk_add(vec![neg_n, neg_n_sq, off]);
        terms.mk_eq(lhs, rhs)
    }

    #[test]
    fn ground_truth_conflict_on_fixed_vars() {
        // n = 5, sum = 0, and `2*sum = -n - n*n + 30` asserted FALSE.
        // Ground evaluation: 0 = -5 - 25 + 30 = 0 is true -> conflict.
        let mut terms = TermStore::new();
        let n = terms.mk_var("n", Sort::Int);
        let sum = terms.mk_var("sum", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let zero = terms.mk_int(BigInt::from(0));
        let n_eq_5 = terms.mk_eq(n, five);
        let sum_eq_0 = terms.mk_eq(sum, zero);
        let eq = quadratic_eq(&mut terms, sum, n, 30);

        let mut solver = LiaSolver::new(&terms);
        solver.assert_literal(n_eq_5, true);
        solver.assert_literal(sum_eq_0, true);
        solver.assert_literal(eq, false);
        // Run LRA so the fixed bounds for n/sum exist.
        let _ = solver.lra.check();

        let conflict = solver
            .check_polynomial_residual_conflict()
            .expect("ground-evaluation conflict expected");
        assert!(
            conflict.iter().any(|lit| lit.term == eq && !lit.value),
            "conflict must cite the violated equality: {conflict:?}"
        );

        let result = solver.check();
        assert!(
            matches!(
                result,
                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
            ),
            "full check must report the nonlinear conflict, got {result:?}"
        );
    }

    #[test]
    fn residual_identity_conflict_without_branching() {
        // Accumulator consecution: `2s = -n - n*n + 30` (true) and
        // `2(s+n) = -(n-1) - (n-1)*(n-1) + 30` (false) share the residual
        // `2s + n + n^2 - 30` -> contradiction with no bounds on n at all.
        let mut terms = TermStore::new();
        let n = terms.mk_var("n", Sort::Int);
        let s = terms.mk_var("s", Sort::Int);
        let body_eq = quadratic_eq(&mut terms, s, n, 30);

        let two = terms.mk_int(BigInt::from(2));
        let one = terms.mk_int(BigInt::from(1));
        let neg_one = terms.mk_int(BigInt::from(-1));
        let thirty = terms.mk_int(BigInt::from(30));
        let s_plus_n = terms.mk_add(vec![s, n]);
        let lhs = terms.mk_mul(vec![two, s_plus_n]);
        let n_minus_1 = terms.mk_sub(vec![n, one]);
        let neg_nm1 = terms.mk_mul(vec![neg_one, n_minus_1]);
        let nm1_sq = terms.mk_mul(vec![n_minus_1, n_minus_1]);
        let neg_nm1_sq = terms.mk_mul(vec![neg_one, nm1_sq]);
        let rhs = terms.mk_add(vec![neg_nm1, neg_nm1_sq, thirty]);
        let head_eq = terms.mk_eq(lhs, rhs);

        let mut solver = LiaSolver::new(&terms);
        solver.assert_literal(body_eq, true);
        solver.assert_literal(head_eq, false);

        let conflict = solver
            .check_polynomial_residual_conflict()
            .expect("residual identity conflict expected");
        let cited: Vec<(TermId, bool)> = conflict.iter().map(|lit| (lit.term, lit.value)).collect();
        assert!(cited.contains(&(body_eq, true)), "conflict: {conflict:?}");
        assert!(cited.contains(&(head_eq, false)), "conflict: {conflict:?}");
    }

    #[test]
    fn no_conflict_on_satisfiable_nonlinear_assignment() {
        // n = 5, sum = 0, and `2*sum = -n - n*n + 30` asserted TRUE:
        // 0 = 0 holds, so no conflict may be reported.
        let mut terms = TermStore::new();
        let n = terms.mk_var("n", Sort::Int);
        let sum = terms.mk_var("sum", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let zero = terms.mk_int(BigInt::from(0));
        let n_eq_5 = terms.mk_eq(n, five);
        let sum_eq_0 = terms.mk_eq(sum, zero);
        let eq = quadratic_eq(&mut terms, sum, n, 30);

        let mut solver = LiaSolver::new(&terms);
        solver.assert_literal(n_eq_5, true);
        solver.assert_literal(sum_eq_0, true);
        solver.assert_literal(eq, true);
        let _ = solver.lra.check();

        assert!(
            solver.check_polynomial_residual_conflict().is_none(),
            "satisfiable assignment must not conflict"
        );
    }

    #[test]
    fn pinning_propagates_through_equalities() {
        // n fixed to 1 by bounds; `2s = -n - n*n + 30` (true) pins s = 14;
        // `2(s+n) = 30` asserted FALSE then evaluates to 30 = 30 -> conflict.
        let mut terms = TermStore::new();
        let n = terms.mk_var("n", Sort::Int);
        let s = terms.mk_var("s", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let two = terms.mk_int(BigInt::from(2));
        let thirty = terms.mk_int(BigInt::from(30));
        let n_eq_1 = terms.mk_eq(n, one);
        let body_eq = quadratic_eq(&mut terms, s, n, 30);
        let s_plus_n = terms.mk_add(vec![s, n]);
        let lhs = terms.mk_mul(vec![two, s_plus_n]);
        let head_eq = terms.mk_eq(lhs, thirty);

        let mut solver = LiaSolver::new(&terms);
        solver.assert_literal(n_eq_1, true);
        solver.assert_literal(body_eq, true);
        solver.assert_literal(head_eq, false);
        let _ = solver.lra.check();

        let conflict = solver
            .check_polynomial_residual_conflict()
            .expect("pinning conflict expected");
        let cited: Vec<(TermId, bool)> = conflict.iter().map(|lit| (lit.term, lit.value)).collect();
        assert!(cited.contains(&(head_eq, false)), "conflict: {conflict:?}");
        assert!(cited.contains(&(body_eq, true)), "conflict: {conflict:?}");
    }

    #[test]
    fn gcd_divisibility_conflict() {
        // `2*(x*y) + 4*z = 7` has no integer solution (gcd 2 does not divide 7).
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let z = terms.mk_var("z", Sort::Int);
        let two = terms.mk_int(BigInt::from(2));
        let four = terms.mk_int(BigInt::from(4));
        let seven = terms.mk_int(BigInt::from(7));
        let xy = terms.mk_mul(vec![x, y]);
        let two_xy = terms.mk_mul(vec![two, xy]);
        let four_z = terms.mk_mul(vec![four, z]);
        let lhs = terms.mk_add(vec![two_xy, four_z]);
        let eq = terms.mk_eq(lhs, seven);

        let mut solver = LiaSolver::new(&terms);
        solver.assert_literal(eq, true);

        let conflict = solver
            .check_polynomial_residual_conflict()
            .expect("GCD conflict expected");
        assert!(
            conflict.iter().any(|lit| lit.term == eq && lit.value),
            "conflict must cite the equality: {conflict:?}"
        );
    }

    #[test]
    fn mod_constant_folding_conflict() {
        // x = 7 fixed; 7 mod 3 = 1, so `(mod x 3) = 1` asserted FALSE
        // contradicts the pinned value of x.
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let seven = terms.mk_int(BigInt::from(7));
        let three = terms.mk_int(BigInt::from(3));
        let one = terms.mk_int(BigInt::from(1));
        let x_eq_7 = terms.mk_eq(x, seven);
        let x_mod_3 = terms.mk_mod(x, three);
        let mod_eq = terms.mk_eq(x_mod_3, one);

        let mut solver = LiaSolver::new(&terms);
        solver.assert_literal(x_eq_7, true);
        solver.assert_literal(mod_eq, false);
        let _ = solver.lra.check();

        let conflict = solver
            .check_polynomial_residual_conflict()
            .expect("mod folding conflict expected");
        let cited: Vec<(TermId, bool)> = conflict.iter().map(|lit| (lit.term, lit.value)).collect();
        assert!(cited.contains(&(mod_eq, false)), "conflict: {conflict:?}");
    }
}
