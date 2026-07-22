// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Script-level EqDiffVar reduction for the proof-interpolation route
//! (rank-4 inc-17; design option C of the inc-16 blocker).
//!
//! The ay-dpll EqDiffVar preprocessing pass (inc-14) is DISABLED under proof
//! production: its fresh definitional variables detach reconstructed proof
//! leaves from the original assertions. Consequence (inc-16, causally
//! verified): the IMC route's proof-mode interpolation solves time out on
//! SYNAPSE/FIREFLY/MESI guarded-eq-network k-unrollings that the non-proof
//! path decides in ~0.5s.
//!
//! Instead of teaching the in-solver proof pipeline about definitional
//! variables, this module applies the SAME reduction OUTSIDE the solver, on
//! the `ChcExpr` A/B constraint lists `proof_backed` renders into the scoped
//! proof-solve script:
//!
//! 1. Canonicalize every NESTED Int equality/disequality atom to an integer
//!    linear row `lin = rhs` over VARIABLE leaves (sign/gcd-normalized,
//!    mirroring `ay-dpll/src/preprocess/eq_diffvar` — restricted to plain
//!    variable leaves, which is the entire SYNAPSE/FIREFLY/MESI class).
//! 2. Introduce ONE fresh Int variable `d := lin` per distinct `lin` and
//!    rewrite each atom to `(= d rhs)` / `(distinct d rhs)` in place.
//! 3. Assert the definition as the unconditional inequality PAIR
//!    `(<= d lin)` / `(>= d lin)` (the inc-14 validated shape), placed in
//!    the partition(s) where `d` occurs: A-only occurrences -> A-side def,
//!    B-only -> B-side, both -> A-side (when `d` occurs on both sides every
//!    defining leaf is provably shared, so the A-side placement cannot
//!    enlarge the shared signature).
//!
//! The proof solve then runs on ORDINARY input assertions — every proof leaf
//! traces to a script assert exactly as in the rewrite-free flow, so the
//! interpolation traversal needs no new classification logic. The produced
//! interpolant may mention the definitional variables; `proof_backed`
//! back-substitutes `d := lin` (exact linear form) BEFORE the locality
//! pre-filter and the Craig validation gate.
//!
//! # Soundness
//!
//! The rewrite is a definitional extension: `A' ∧ B'` is equisatisfiable
//! with `A ∧ B`, and for any interpolant `I` of `(A', B')`, the
//! back-substituted `I[d := lin]` is an interpolant of `(A, B)` (models of
//! `A` extend uniquely by `d := lin(m)`; models of `I[d:=lin] ∧ B` likewise).
//! None of this is TRUSTED: the final candidate is Craig-validated by the
//! existing `is_valid_interpolant_until` gate against the ORIGINAL A/B
//! constraints with the ORIGINAL shared-variable set. Any bug in this module
//! (mis-canonicalization, wrong def placement, leftover definitional vars)
//! can only produce a candidate that fails that gate and falls back to the
//! cascade — a completeness loss, never a wrong answer.
//!
//! Kill switches: `AY_EQ_DIFFVAR_PROOF=0` disables this module only;
//! `AY_EQ_DIFFVAR=0` (the inc-14 master switch) disables both the in-solver
//! pass and this one, so A/B harnesses keep a single global toggle.

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Caps mirroring the inc-14 pass: bound the work on shapes it cannot help.
const MAX_DIFF_VARS: usize = 1024;
const MAX_ROW_LEAVES: usize = 64;
/// Candidate-scan node budget across all constraints (mirrors the
/// `MAX_PROOF_ITP_SCAN_NODES` applicability scan in `proof_backed`).
const MAX_DV_SCAN_NODES: usize = 200_000;

/// `AY_EQ_DIFFVAR_PROOF` kill switch (default ON), subordinate to the
/// inc-14 master switch `AY_EQ_DIFFVAR`. Read per call (not cached) so A/B
/// harnesses can toggle within a process, matching
/// `ay_dpll::preprocess::eq_diffvar_enabled`.
pub(crate) fn eq_diffvar_proof_enabled() -> bool {
    if std::env::var("AY_EQ_DIFFVAR").is_ok_and(|v| v == "0") {
        return false;
    }
    std::env::var("AY_EQ_DIFFVAR_PROOF").map_or(true, |v| v != "0")
}

/// Outcome of the script-level reduction.
pub(crate) struct ProofDiffVarRewrite {
    /// Rewritten A partition: folded A constraints ++ A-side definitions.
    pub(crate) a_constraints: Vec<ChcExpr>,
    /// Rewritten B partition: folded B constraints ++ B-side definitions.
    pub(crate) b_constraints: Vec<ChcExpr>,
    /// Back-substitution map: definitional var name -> exact linear form.
    pub(crate) subst: FxHashMap<String, ChcExpr>,
    /// Stats: distinct difference variables introduced (defs emitted).
    pub(crate) diff_vars: usize,
    /// Stats: constraints whose content changed.
    pub(crate) rewritten_constraints: usize,
}

/// Canonical integer linear row over variable leaves: gcd-1 coefficients,
/// positive leading (lexicographically-smallest-name) coefficient, sorted by
/// name. The dedup key deliberately EXCLUDES the constant side, so
/// `(= x y)` and `(= x (+ y 5))` share one difference variable (the whole
/// point: their rewritten atoms conflict through `d`'s bounds).
type CanonKey = Vec<(String, i64)>;

/// Apply the reduction to the proof-route constraint lists. Returns `None`
/// when nothing was rewritten (the caller keeps the original script flow).
///
/// `var_sorts` is the declared-variable map of the script (used only for
/// fresh-name collision avoidance; the fragment gate in `proof_backed` has
/// already validated it).
pub(crate) fn apply_for_proof_script(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    var_sorts: &FxHashMap<String, ChcSort>,
) -> Option<ProofDiffVarRewrite> {
    // ---- Phase A: candidate atoms ---------------------------------------
    // Mirrors `GuardedEqMining::collect_atoms` + `EqDiffVar::canonicalize`:
    // only atoms occurring NESTED (not as a whole top-level constraint) are
    // candidates; a whole-constraint unit atom is already a fixed fact.
    let mut scan = Scan::new();
    for (idx, constraint) in a_constraints.iter().chain(b_constraints.iter()).enumerate() {
        scan.walk(constraint, idx, true);
        if scan.budget == 0 {
            return None; // scan blew the budget: shape too large, keep the original flow
        }
    }
    // Keep only nested candidates, in first-seen order.
    let canon: Vec<&CandidateAtom> = scan
        .order
        .iter()
        .filter_map(|atom| scan.candidates.get(atom))
        .filter(|c| c.nested)
        .collect();
    if canon.is_empty() {
        return None;
    }

    // ---- Phase B: difference-variable assignment ------------------------
    let mut dvar_of: FxHashMap<CanonKey, String> = FxHashMap::default();
    let mut dvar_order: Vec<(CanonKey, String)> = Vec::new();
    let mut pairs: Vec<(ChcExpr, ChcExpr)> = Vec::new();
    let mut dvar_of_atom: FxHashMap<ChcExpr, String> = FxHashMap::default();
    let mut name_seq = 0usize;
    for cand in &canon {
        let dvar = match dvar_of.get(&cand.key) {
            Some(name) => name.clone(),
            None => {
                if dvar_order.len() >= MAX_DIFF_VARS {
                    continue;
                }
                let name = fresh_dvar_name(var_sorts, &mut name_seq);
                dvar_of.insert(cand.key.clone(), name.clone());
                dvar_order.push((cand.key.clone(), name.clone()));
                name
            }
        };
        let d = ChcExpr::var(ChcVar::new(dvar.clone(), ChcSort::Int));
        let rhs = ChcExpr::int(cand.rhs);
        let replacement = match cand.op {
            ChcOp::Eq => ChcExpr::eq(d, rhs),
            _ => ChcExpr::ne(d, rhs),
        };
        pairs.push((cand.atom.clone(), replacement));
        dvar_of_atom.insert(cand.atom.clone(), dvar);
    }
    if pairs.is_empty() {
        return None;
    }

    // ---- Phase C: fold + definition placement ---------------------------
    let a_len = a_constraints.len();
    let mut rewritten: Vec<ChcExpr> = Vec::with_capacity(a_len + b_constraints.len());
    let mut used_in_a: FxHashSet<String> = FxHashSet::default();
    let mut used_in_b: FxHashSet<String> = FxHashSet::default();
    let mut rewritten_constraints = 0usize;
    for (idx, constraint) in a_constraints.iter().chain(b_constraints.iter()).enumerate() {
        let folded = constraint.substitute_expr_pairs(&pairs);
        if folded != *constraint {
            rewritten_constraints += 1;
            // Mark every dvar of the candidate atoms recorded for this
            // constraint as used on its side. `substitute_expr_pairs` can
            // rewrite PARTIALLY on node-budget exhaustion, so this is an
            // over-approximation — but a def for a dvar whose atom survived
            // unreplaced is still definitional, and its linear leaves are
            // already present on that side via the surviving atom, so the
            // shared-variable signature cannot be enlarged.
            let used = if idx < a_len {
                &mut used_in_a
            } else {
                &mut used_in_b
            };
            if let Some(atoms) = scan.atoms_of_constraint.get(&idx) {
                for atom in atoms {
                    if let Some(dvar) = dvar_of_atom.get(atom) {
                        used.insert(dvar.clone());
                    }
                }
            }
        }
        rewritten.push(folded);
    }
    if rewritten_constraints == 0 {
        return None;
    }

    // Identical-constraint guard: the fold can collapse two originally
    // distinct constraints into one expr (e.g. `(= x y)` and `(= x (+ y 0))`
    // share a replacement). The downstream assert-count check in
    // `proof_backed` assumes a 1:1 script/assert correspondence, so skip the
    // rewrite when it introduces duplicates the original list did not have.
    {
        let mut originals: FxHashSet<&ChcExpr> = FxHashSet::default();
        let original_dups = a_constraints
            .iter()
            .chain(b_constraints.iter())
            .any(|c| !originals.insert(c));
        let mut folded: FxHashSet<&ChcExpr> = FxHashSet::default();
        let folded_dups = rewritten.iter().any(|c| !folded.insert(c));
        if folded_dups && !original_dups {
            return None;
        }
    }

    // Definitions for every USED dvar, in deterministic introduction order.
    let mut subst: FxHashMap<String, ChcExpr> = FxHashMap::default();
    let mut a_defs: Vec<ChcExpr> = Vec::new();
    let mut b_defs: Vec<ChcExpr> = Vec::new();
    for (key, dvar) in &dvar_order {
        let in_a = used_in_a.contains(dvar);
        let in_b = used_in_b.contains(dvar);
        if !in_a && !in_b {
            continue; // every constraint using it kept its original form
        }
        let lin = build_lin(key);
        let d = ChcExpr::var(ChcVar::new(dvar.clone(), ChcSort::Int));
        // Inequality PAIR, not a unit equality: the inc-14 validated shape
        // (a unit equality is food for downstream equality inlining).
        let defs = if in_a { &mut a_defs } else { &mut b_defs };
        defs.push(ChcExpr::le(d.clone(), lin.clone()));
        defs.push(ChcExpr::ge(d, lin.clone()));
        subst.insert(dvar.clone(), lin);
    }
    if subst.is_empty() {
        return None;
    }

    let diff_vars = subst.len();
    let mut a_out: Vec<ChcExpr> = rewritten[..a_len].to_vec();
    let mut b_out: Vec<ChcExpr> = rewritten[a_len..].to_vec();
    a_out.append(&mut a_defs);
    b_out.append(&mut b_defs);
    Some(ProofDiffVarRewrite {
        a_constraints: a_out,
        b_constraints: b_out,
        subst,
        diff_vars,
        rewritten_constraints,
    })
}

/// Fresh definitional variable name. `__ay_*` is rejected by the frontend
/// for user declarations (the script is re-parsed by the scoped solver), so
/// the prefix is `ay_eqdv_p`; collisions with declared script variables are
/// skipped (deterministically) rather than mangled.
fn fresh_dvar_name(var_sorts: &FxHashMap<String, ChcSort>, seq: &mut usize) -> String {
    loop {
        let name = format!("ay_eqdv_p{}", *seq);
        *seq += 1;
        if !var_sorts.contains_key(&name) {
            return name;
        }
    }
}

/// Build the exact linear form `sum coeff_i * var_i` for a canonical key.
fn build_lin(key: &CanonKey) -> ChcExpr {
    let mut acc: Option<ChcExpr> = None;
    for (name, coeff) in key {
        let var = ChcExpr::var(ChcVar::new(name.clone(), ChcSort::Int));
        let part = match *coeff {
            1 => var,
            -1 => ChcExpr::neg(var),
            c => ChcExpr::mul(ChcExpr::int(c), var),
        };
        acc = Some(match acc {
            None => part,
            Some(prev) => ChcExpr::add(prev, part),
        });
    }
    acc.unwrap_or(ChcExpr::Int(0))
}

/// One canonicalized candidate atom.
struct CandidateAtom {
    /// The atom expression as it appears in the constraints.
    atom: ChcExpr,
    /// `Eq` or `Ne` (the rewrite preserves the operator over `d`).
    op: ChcOp,
    key: CanonKey,
    rhs: i64,
    /// Whether the atom occurs somewhere other than as a whole constraint.
    nested: bool,
}

/// Candidate-atom scan state (Phase A).
struct Scan {
    budget: usize,
    candidates: FxHashMap<ChcExpr, CandidateAtom>,
    /// First-seen order of candidate atoms (determinism).
    order: Vec<ChcExpr>,
    /// Constraint index -> candidate atoms occurring in it (for definition
    /// placement: which partition uses which difference variable).
    atoms_of_constraint: FxHashMap<usize, Vec<ChcExpr>>,
}

impl Scan {
    fn new() -> Self {
        Self {
            budget: MAX_DV_SCAN_NODES,
            candidates: FxHashMap::default(),
            order: Vec::new(),
            atoms_of_constraint: FxHashMap::default(),
        }
    }

    fn walk(&mut self, expr: &ChcExpr, constraint_idx: usize, is_root: bool) {
        if self.budget == 0 {
            return;
        }
        self.budget -= 1;
        crate::expr::maybe_grow_expr_stack(|| {
            if let ChcExpr::Op(op @ (ChcOp::Eq | ChcOp::Ne), args) = expr {
                if args.len() == 2 {
                    if let Some((key, rhs)) = canonicalize(args[0].as_ref(), args[1].as_ref()) {
                        if !self.candidates.contains_key(expr) {
                            self.order.push(expr.clone());
                            self.candidates.insert(
                                expr.clone(),
                                CandidateAtom {
                                    atom: expr.clone(),
                                    op: *op,
                                    key,
                                    rhs,
                                    nested: false,
                                },
                            );
                        }
                        if !is_root {
                            if let Some(entry) = self.candidates.get_mut(expr) {
                                entry.nested = true;
                            }
                        }
                        self.atoms_of_constraint
                            .entry(constraint_idx)
                            .or_default()
                            .push(expr.clone());
                    }
                }
            }
            // Recurse through Boolean/arithmetic structure. ChcExpr in the
            // proof-route fragment has no binders, so descending everywhere
            // is safe; atoms inside ITE conditions etc. are fair candidates
            // (the rewrite is an equivalence at every position).
            if let ChcExpr::Op(_, args) = expr {
                for arg in args {
                    self.walk(arg.as_ref(), constraint_idx, false);
                }
            }
        });
    }
}

/// Canonicalize an Int (dis)equality `lhs OP rhs` into a normalized linear
/// row over variable leaves. Returns `None` (atom skipped, never folded)
/// when: a side is not an exact linear form over Int variables, fewer than 2
/// or more than `MAX_ROW_LEAVES` distinct variables remain, any coefficient
/// overflows i64, or the normalized constant is non-integral (such an atom
/// is constant-valued over Int; deciding it is left to the solver, exactly
/// like inc-14).
fn canonicalize(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<(CanonKey, i64)> {
    let mut coeffs: FxHashMap<String, i128> = FxHashMap::default();
    let mut konst: i128 = 0;
    accumulate(lhs, 1, &mut coeffs, &mut konst)?;
    accumulate(rhs, -1, &mut coeffs, &mut konst)?;
    let mut entries: Vec<(String, i128)> = coeffs.into_iter().filter(|(_, c)| *c != 0).collect();
    if entries.len() < 2 || entries.len() > MAX_ROW_LEAVES {
        return None;
    }
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    // gcd-normalize with the sign of the leading coefficient.
    let mut gcd: i128 = 0;
    for (_, c) in &entries {
        gcd = gcd_i128(gcd, c.unsigned_abs() as i128);
    }
    if gcd == 0 {
        return None;
    }
    let divisor = if entries[0].1 < 0 { -gcd } else { gcd };
    let rhs_val = -konst;
    if rhs_val % divisor != 0 {
        return None; // e.g. `2x - 2y = 1`: constant-valued over Int; skip.
    }
    let rhs_norm = rhs_val / divisor;
    let mut key: CanonKey = Vec::with_capacity(entries.len());
    for (name, c) in entries {
        let c = c / divisor;
        key.push((name, i64::try_from(c).ok()?));
    }
    Some((key, i64::try_from(rhs_norm).ok()?))
}

/// Exact linear accumulation: `coeffs/konst += mult * expr`. Returns `None`
/// on any non-linear / non-Int shape or arithmetic overflow.
fn accumulate(
    expr: &ChcExpr,
    mult: i128,
    coeffs: &mut FxHashMap<String, i128>,
    konst: &mut i128,
) -> Option<()> {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Int(n) => {
            *konst = konst.checked_add(mult.checked_mul(i128::from(*n))?)?;
            Some(())
        }
        ChcExpr::Var(v) if v.sort == ChcSort::Int => {
            let slot = coeffs.entry(v.name.clone()).or_insert(0);
            *slot = slot.checked_add(mult)?;
            Some(())
        }
        ChcExpr::Op(ChcOp::Add, args) => {
            for arg in args {
                accumulate(arg.as_ref(), mult, coeffs, konst)?;
            }
            Some(())
        }
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            // SMT-LIB n-ary minus: a - b - c ...; unary minus is negation.
            if args.len() == 1 {
                return accumulate(args[0].as_ref(), mult.checked_neg()?, coeffs, konst);
            }
            accumulate(args[0].as_ref(), mult, coeffs, konst)?;
            for arg in &args[1..] {
                accumulate(arg.as_ref(), mult.checked_neg()?, coeffs, konst)?;
            }
            Some(())
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            accumulate(args[0].as_ref(), mult.checked_neg()?, coeffs, konst)
        }
        ChcExpr::Op(ChcOp::Mul, args) if !args.is_empty() => {
            // Exactly one non-constant factor allowed (linear); constants fold.
            let mut product: i128 = 1;
            let mut non_const: Option<&ChcExpr> = None;
            for arg in args {
                match arg.as_ref() {
                    ChcExpr::Int(n) => product = product.checked_mul(i128::from(*n))?,
                    other => {
                        if non_const.is_some() {
                            return None;
                        }
                        non_const = Some(other);
                    }
                }
            }
            match non_const {
                Some(inner) => accumulate(inner, mult.checked_mul(product)?, coeffs, konst),
                None => {
                    *konst = konst.checked_add(mult.checked_mul(product)?)?;
                    Some(())
                }
            }
        }
        // Anything else (ITE, Bool shapes, non-Int vars, div/mod, ...) makes
        // the atom a non-candidate. The inc-14 TermStore pass generalizes
        // unknown subterms to opaque leaves; the proof-route class
        // (SYNAPSE/FIREFLY/MESI guarded var-var networks) is covered by
        // plain variable leaves, and a skipped atom is merely not reduced.
        _ => None,
    })
}

/// Binary gcd on non-negative i128.
fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

#[cfg(test)]
#[path = "proof_eq_diffvar_tests.rs"]
mod tests;
