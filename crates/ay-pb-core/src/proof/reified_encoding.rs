// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof-producing (VeriPB "reification via redundancy") introduction of the
//! auxiliary variables of a Sinz sequential-counter cardinality CNF encoding.
//!
//! # Why this exists
//!
//! The DEC-LIN-CERT lift ([`super::drat_lift`]) only handles AUX-FREE encodings:
//! it declines the moment a DRAT clause references a variable index above
//! `num_pb_vars`. A compact cardinality encoding (Sinz 2005) introduces aux
//! "counter register" variables `r(i,j)`, so the lift rejects it.
//!
//! To use such an encoding in a VeriPB proof, every aux var must first be
//! **introduced** into the proof database. VeriPB's `red` (redundancy) rule lets
//! us add a constraint `C` as long as a *witness* substitution `ω` shows `C` is
//! satisfiability-preserving against the current database. For a **fresh**
//! reified variable `z` (one not yet mentioned in any database constraint), each
//! Tseitin defining clause of `z` is redundant under the witness that maps `z` to
//! the value satisfying that clause:
//!
//!   * a clause containing the positive literal `z`  → witness `z -> 1`
//!   * a clause containing the negative literal `~z` → witness `z -> 0`
//!
//! This is the reusable, empirically VeriPB-3.0-verified idiom (see the module
//! test `sinz_reified_intro_is_veripb_verified`, which runs the official checker).
//!
//! # Scope
//!
//! This module is **self-contained and additive**: it does not touch
//! [`super::cert`] / [`super::drat_lift`] wiring. It is a prototype that proves
//! out the witness idiom so the compact-encoding path can later be wired into the
//! certified-UNSAT route.
//!
//! It covers both:
//!   * the **cardinality** case (all coefficients 1), via
//!     [`encode_sinz_cardinality`]; and
//!   * the general **weighted** PB case (coefficients may exceed 1), via
//!     [`encode_sinz_weighted`].
//!
//! ## Weighted case — same witness rule, empirically verified
//!
//! The weighted Sinz encoding (register `r(i,w)` = "accumulated weight from the
//! first `i+1` terms is `>= w`") introduces two clause shapes the cardinality
//! encoding never produces, both of which reference a **predecessor** register
//! `r(i-1, j-c_i)` in addition to `r(i,j)`:
//!
//!   * forward:  `lit_i ∧ r(i-1, j-c_i) → r(i,j)`  →  `[-lit_i, -r(i-1,j-c_i), r(i,j)]`
//!   * backward: `r(i,j) → r(i-1,j) ∨ r(i-1, j-c_i)` → `[-r(i,j), r(i-1,j), r(i-1,j-c_i)]`
//!
//! These clauses mention **two** aux variables. The introduction witness is still
//! the **largest-aux-index polarity** rule (see [`aux_intro_witness`] /
//! [`emit_sinz_aux_introductions`]): the register being *defined* is always the
//! one with the largest index (`r(i,j)`, since `i > i-1`), and it is fresh at the
//! time this clause is introduced (clauses are emitted in aux-variable order, so
//! every clause defining `r(i,j)` precedes any later clause that uses `r(i,j)` as
//! a predecessor). The predecessor `r(i-1, j-c_i)` is already in the database from
//! an earlier row and simply rides along.
//!
//! This was confirmed empirically with the official VeriPB 3.0 checker across
//! three weighted shapes — a coefficient `> rhs`, a coefficient `> 1` that drives
//! the `r(i-1, j-c_i)` predecessor clauses, and a mixed instance — all of which
//! pass with **no** special-cased witness. The end-to-end test
//! [`tests::sinz_weighted_reified_intro_is_veripb_verified`] runs the checker.

use std::io::Write;

use super::steps::ProofStep;
use super::veripb::{Result, VeriPbWriter};
use crate::types::{PbInstance, PbRel};

/// A Sinz sequential-counter encoding of a single cardinality constraint, plus
/// the metadata needed to introduce its aux variables in a VeriPB proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SinzCardinalityEncoding {
    /// CNF clauses (DIMACS signed literals, 1-based variables). The original
    /// `lits` variables are referenced as given; aux register variables occupy
    /// the contiguous range `[aux_base, aux_base + aux_count)`.
    pub clauses: Vec<Vec<i32>>,
    /// First (1-based) DIMACS index used for an auxiliary register variable.
    pub aux_base: u32,
    /// Number of auxiliary register variables allocated (`n * k`).
    pub aux_count: u32,
}

impl SinzCardinalityEncoding {
    /// `true` iff `var` is one of this encoding's auxiliary register variables.
    fn is_aux(&self, var: u32) -> bool {
        var >= self.aux_base && var < self.aux_base + self.aux_count
    }
}

/// Encode the cardinality constraint `sum(lits[i]) >= k` with the Sinz 2005
/// sequential counter, allocating aux register variables starting at `aux_base`.
///
/// `lits` are DIMACS signed literals (1-based). Requires `k >= 1`,
/// `k <= lits.len()`, and a non-empty `lits`. This mirrors the cardinality case
/// of `crate::encoding`'s `encode_sequential_counter` exactly (so the produced
/// clauses match the solver's encoding), but takes an explicit `aux_base` and
/// reports the aux range for proof introduction.
///
/// The constraint is satisfied iff the final register `r(n-1, k-1)` is true; the
/// last emitted clause is the unit `[r(n-1, k-1)]` asserting it.
#[must_use]
pub fn encode_sinz_cardinality(lits: &[i32], k: usize, aux_base: u32) -> SinzCardinalityEncoding {
    let n = lits.len();
    assert!(n > 0, "cardinality encoding needs at least one literal");
    assert!(k >= 1, "cardinality threshold must be positive");
    assert!(k <= n, "threshold {k} exceeds literal count {n}");

    let aux_count = (n * k) as u32;
    // r(i, j) is the 1-based DIMACS variable for "at least j+1 of the first i+1
    // literals are true". Aux vars are laid out row-major: r(i, j) = base + i*k + j.
    let r = |i: usize, j: usize| -> i32 { (aux_base + (i * k + j) as u32) as i32 };

    let mut clauses: Vec<Vec<i32>> = Vec::new();

    // Base case i = 0 (cardinality: coefficient c0 = 1, so only level j = 0 is
    // reachable from the first literal).
    clauses.push(vec![-lits[0], r(0, 0)]); // lit0 -> r(0,0)
    clauses.push(vec![-r(0, 0), lits[0]]); // r(0,0) -> lit0
    for j in 1..k {
        clauses.push(vec![-r(0, j)]); // levels >= 2 impossible from one literal
    }

    // Inductive case (cardinality: each subsequent coefficient is 1).
    for i in 1..n {
        for j in 0..k {
            // (a) carry: r(i-1, j) -> r(i, j)
            clauses.push(vec![-r(i - 1, j), r(i, j)]);

            if j == 0 {
                // (c) level 1 reached by this literal alone: lit_i -> r(i, 0)
                clauses.push(vec![-lits[i], r(i, 0)]);
            } else {
                // (b) lit_i AND r(i-1, j-1) -> r(i, j)
                clauses.push(vec![-lits[i], -r(i - 1, j - 1), r(i, j)]);
            }

            // backward: r(i, j) -> r(i-1, j) OR lit_i
            clauses.push(vec![-r(i, j), r(i - 1, j), lits[i]]);

            if j > 0 {
                // backward: r(i, j) -> r(i-1, j) OR r(i-1, j-1)
                clauses.push(vec![-r(i, j), r(i - 1, j), r(i - 1, j - 1)]);
            }
        }
    }

    // Constraint holds iff the top register is set.
    clauses.push(vec![r(n - 1, k - 1)]);

    SinzCardinalityEncoding {
        clauses,
        aux_base,
        aux_count,
    }
}

/// Encode the **weighted** PB constraint `sum(coeffs[i] * lits[i]) >= rhs` with
/// the generalized Sinz sequential (weighted) counter, allocating aux register
/// variables starting at `aux_base`.
///
/// `lits` are DIMACS signed literals (1-based). `coeffs` are the matching
/// positive coefficients. Requires `coeffs.len() == lits.len()`, a non-empty
/// input, all `coeffs[i] >= 1`, and `rhs >= 1`. The caller must have already
/// handled the trivial always-SAT / always-UNSAT cases (matching the contract of
/// `crate::encoding`'s `encode_sequential_counter`).
///
/// The register `r(i, j)` (0-indexed `j` for weight level `j + 1`) means "the
/// accumulated weight from the first `i + 1` terms is `>= j + 1`". There are
/// `n * rhs` aux registers (`r` row-major: `r(i, j) = aux_base + i*rhs + j`).
///
/// This mirrors `crate::encoding`'s `encode_sequential_counter` **clause for
/// clause and in the same order** (so the produced clauses match exactly what the
/// solver emits), but takes an explicit `aux_base` and reports the aux range for
/// proof introduction. The cardinality case (`coeffs` all 1) reduces to the same
/// clause set as [`encode_sinz_cardinality`].
///
/// The result reuses [`SinzCardinalityEncoding`] (the struct is a generic
/// "Sinz-aux CNF + aux range" carrier; the name is historical). Introduce its aux
/// with [`emit_sinz_aux_introductions`] — the same largest-aux-index polarity
/// witness applies (see the module docs for why, including the weighted-only
/// predecessor clause shapes).
///
/// The constraint is satisfied iff the final register `r(n-1, rhs-1)` is true;
/// the last emitted clause is the unit `[r(n-1, rhs-1)]` asserting it.
#[must_use]
pub fn encode_sinz_weighted(
    coeffs: &[i128],
    lits: &[i32],
    rhs: i128,
    aux_base: u32,
) -> SinzCardinalityEncoding {
    let n = coeffs.len();
    assert_eq!(n, lits.len(), "coeffs and lits must have equal length");
    assert!(n > 0, "weighted encoding needs at least one term");
    assert!(rhs >= 1, "weighted threshold must be positive");
    assert!(
        coeffs.iter().all(|&c| c >= 1),
        "coefficients must be positive"
    );

    // Track weight levels 1..=rhs; level j+1 lives in register column j.
    let k = rhs as usize;
    let aux_count = (n * k) as u32;
    // r(i, j) = "accumulated weight from first i+1 terms is >= j+1".
    // Aux vars are laid out row-major: r(i, j) = base + i*k + j.
    let r = |i: usize, j: usize| -> i32 { (aux_base + (i * k + j) as u32) as i32 };

    let mut clauses: Vec<Vec<i32>> = Vec::new();

    // Base case i = 0 (the first term contributes weight c0, clamped to rhs).
    let c0 = coeffs[0].min(rhs) as usize;
    // lit0 true -> weight levels 1..=c0 are reached: lit0 -> r(0, j).
    for j in 0..c0.min(k) {
        clauses.push(vec![-lits[0], r(0, j)]);
    }
    // lit0 false -> none of those levels are reached: r(0, j) -> lit0.
    for j in 0..c0.min(k) {
        clauses.push(vec![-r(0, j), lits[0]]);
    }
    // Levels beyond c0 are impossible from just the first term.
    for j in c0..k {
        clauses.push(vec![-r(0, j)]);
    }

    // Inductive case: each subsequent term i contributes weight ci.
    for i in 1..n {
        let ci = coeffs[i].min(rhs) as usize;

        for j in 0..k {
            let w = j + 1; // weight level tracked by column j

            // Forward implications (sufficient conditions -> r(i, j)):

            // (a) carry: r(i-1, j) -> r(i, j)
            clauses.push(vec![-r(i - 1, j), r(i, j)]);

            if w <= ci {
                // (c) lit_i alone reaches weight level w: lit_i -> r(i, j)
                clauses.push(vec![-lits[i], r(i, j)]);
            } else if ci > 0 {
                // (b) lit_i AND r(i-1, j-ci) -> r(i, j)   [WEIGHTED-ONLY shape:
                //     references the predecessor register r(i-1, j-ci)]
                let prev_idx = j - ci;
                clauses.push(vec![-lits[i], -r(i - 1, prev_idx), r(i, j)]);
            }

            // Backward implication (necessary condition):
            // r(i, j) -> r(i-1, j) OR lit_i
            clauses.push(vec![-r(i, j), r(i - 1, j), lits[i]]);

            if w > ci && ci > 0 {
                // r(i, j) -> r(i-1, j) OR r(i-1, j-ci)   [WEIGHTED-ONLY shape:
                //     references the predecessor register r(i-1, j-ci)]
                let prev_idx = j - ci;
                clauses.push(vec![-r(i, j), r(i - 1, j), r(i - 1, prev_idx)]);
            }
        }
    }

    // Constraint holds iff the top register (weight >= rhs) is set.
    clauses.push(vec![r(n - 1, k - 1)]);

    SinzCardinalityEncoding {
        clauses,
        aux_base,
        aux_count,
    }
}

/// Format a CNF clause (DIMACS signed literals) as a VeriPB constraint body
/// **without** the trailing semicolon (what [`ProofStep::Red`] expects for its
/// constraint argument). The clause `(a ∨ ¬b)` is the PB constraint
/// `+1 xa +1 ~xb >= 1`. An empty clause renders as `>= 1`.
fn clause_constraint_body(clause: &[i32]) -> String {
    let mut body = String::new();
    for &lit in clause {
        if lit > 0 {
            body.push_str(&format!("+1 x{lit} "));
        } else {
            body.push_str(&format!("+1 ~x{} ", -lit));
        }
    }
    body.push_str(">= 1");
    body
}

/// Build the VeriPB `red` witness for introducing the aux variable `aux_var` as
/// implied by `clause`. The witness maps `aux_var` to the value that satisfies
/// `clause`: `1` if `clause` contains `+aux_var`, `0` if it contains `~aux_var`.
///
/// This is the reusable Sinz-aux introduction idiom. Because `aux_var` is fresh
/// when first introduced, every defining clause is redundant under this witness
/// (the witness is satisfiability-preserving against the existing database).
fn aux_intro_witness(aux_var: u32, clause: &[i32]) -> String {
    let positive = clause.contains(&(aux_var as i32));
    let value = if positive { 1 } else { 0 };
    format!("x{aux_var} -> {value} ;")
}

/// Emit, in order, a VeriPB `red` step **introducing** every clause of `encoding`
/// that defines an auxiliary register variable, returning the number of steps
/// emitted (one per clause).
///
/// Each clause is introduced with the polarity-based witness for the **largest**
/// aux variable it mentions — that is the register variable this clause helps
/// define, and the one that is fresh at introduction time (clauses are processed
/// in aux-variable order, so a register's own clauses precede every clause that
/// references it as a predecessor). This holds for both the cardinality and the
/// weighted encodings, including the weighted-only clause shapes that reference a
/// predecessor register `r(i-1, j-c_i)` (see the module docs): the largest index
/// is the freshly-defined `r(i,j)`. Clauses with no aux variable (none occur for
/// either Sinz encoding — every clause defines exactly one register) would be
/// introduced with a trivial witness on no variable, which never happens here.
///
/// After these steps, every encoding clause is present in the VeriPB database as
/// a derived (redundancy-justified) constraint, so a subsequent DRAT/RUP
/// refutation over the encoding is liftable. The caller is responsible for the
/// cutting-plane / RUP steps that derive the contradiction and for the
/// conclusion line.
pub fn emit_sinz_aux_introductions<W: Write>(
    writer: &mut VeriPbWriter<W>,
    encoding: &SinzCardinalityEncoding,
) -> Result<usize> {
    let mut emitted = 0usize;
    for clause in &encoding.clauses {
        // The variable being defined by this clause is the largest aux index it
        // touches. (For the base/inductive Sinz clauses this is exactly the
        // register on the implication's "output" side.)
        let defined = clause
            .iter()
            .map(|&lit| lit.unsigned_abs())
            .filter(|&var| encoding.is_aux(var))
            .max();

        let Some(aux_var) = defined else {
            // No aux variable: not expected for the cardinality Sinz encoding,
            // but stay total — such a clause would have to be justified by the
            // caller as a RUP step, not introduced here, so skip it.
            continue;
        };

        let constraint = clause_constraint_body(clause);
        let witness = aux_intro_witness(aux_var, clause);
        writer.log_step(ProofStep::Red(constraint, witness))?;
        emitted += 1;
    }
    Ok(emitted)
}

/// SUPERSEDED (kept for reference) by `emit_sinz_introductions_pol_derived` /
/// [`emit_sinz_introductions_pol_derived_weighted`], which the certified-UNSAT
/// path ([`super::cert`]) now uses. This variant emitted the final
/// constraint-assertion unit `[r_top]` as a `rup` step. That turned out to be
/// UNSOUND-as-written: `r_top` is NOT reverse-unit-propagation-derivable from
/// {input PB row + Sinz definitions} (PB cardinality/weighted rows do not
/// unit-propagate at the root), so VeriPB rejects the `rup` with "not implied by
/// RUP". Forcing `r_top -> 1` via `red` fails too (the backward-clause proofgoal
/// is not auto-provable). The top register must instead be DERIVED by a checked
/// cutting-plane (`pol`) telescope — see `emit_sinz_introductions_pol_derived`.
/// Retained only so the historical asserted idiom stays documented next to its
/// fix; no caller uses it.
#[allow(dead_code)]
pub(super) fn emit_sinz_introductions_asserted<W: Write>(
    writer: &mut VeriPbWriter<W>,
    encoding: &SinzCardinalityEncoding,
) -> Result<usize> {
    let mut emitted = 0usize;
    let last = encoding.clauses.len().wrapping_sub(1);
    for (idx, clause) in encoding.clauses.iter().enumerate() {
        let defined = clause
            .iter()
            .map(|&lit| lit.unsigned_abs())
            .filter(|&var| encoding.is_aux(var))
            .max();
        let Some(aux_var) = defined else {
            continue;
        };
        let constraint = clause_constraint_body(clause);
        // Final clause is the assertion unit `[r_top]` (single positive aux): RUP.
        if idx == last && clause.len() == 1 && clause[0] > 0 {
            writer.log_step(ProofStep::Rup(format!("{constraint} ;")))?;
        } else {
            let witness = aux_intro_witness(aux_var, clause);
            writer.log_step(ProofStep::Red(constraint, witness))?;
        }
        emitted += 1;
    }
    Ok(emitted)
}

/// Introduce the Sinz definition clauses via `red` (polarity witness) and then
/// **derive** the top-register assertion `r(n-1, k-1) >= 1` ("the cardinality
/// constraint holds") with a checkable cutting-plane (`pol`) sequence, instead of
/// asserting it by `rup`/force-true `red`. Returns the [`ConstraintId`] of the
/// derived `r(n-1, k-1) >= 1` constraint.
///
/// # Why a cutting-plane derivation
///
/// The top register `r(n-1, k-1)` is **not** RUP-derivable at the root from the
/// input PB row plus the Sinz definitions (PB cardinality rows do not
/// unit-propagate), and forcing it true via `red` generates a proofgoal on the
/// backward definition clause that VeriPB cannot auto-prove. It *is* derivable by
/// cutting planes. This is the core of certified PB-to-CNF translation
/// (Gocht & Nordström, "Certified CNF Translations for Pseudo-Boolean Solving",
/// SAT 2022); for the sequential counter it is a telescoping derivation up the
/// register chain.
///
/// # The derivation (empirically VeriPB-3.0-verified for all `2 <= k <= n`)
///
/// We build the **saturated column sum** `C_i := sum_{j=0}^{k-1} r(i,j)` stage by
/// stage. `C_i` lower-bounds the prefix count clamped at `k`. The saturation step
/// after each stage is what makes this work for `k <= n-2`, where a single Farkas
/// combination provably fails (the literal over-counting from carry steps
/// overwhelms the input row; only `k in {n-1, n}` admit a one-division derivation).
///
///   * `C_0 := (r(0,0) >= lit_0)`  — the base clause `[-lit_0, r(0,0)]`.
///   * For `i = 1..n-1`:
///       - `inc_i := (base(i)) + sum_{j=1}^{k-1} carry(i,j)`
///         where `base(i) = [-lit_i, r(i,0)]` gives `r(i,0) >= lit_i` and
///         `carry(i,j) = [-r(i-1,j), r(i,j)]` gives `r(i,j) >= r(i-1,j)`. So
///         `inc_i : sum_j r(i,j) >= lit_i + sum_{j=1}^{k-1} r(i-1,j)`.
///       - `s_i := inc_i + C_{i-1}`, then `C_i := saturate(s_i)`. Saturation caps
///         the clamped count at `k` (prevents the `-1` "leak" of an over-counted
///         carry, which is the crux of the telescope).
///   * `with_input := C_{n-1} + INPUT` (the input row `sum lit_m >= k`), then
///     `sat := saturate(with_input)` gives `sum_{j=0}^{k-1} r(n-1,j) >= k`.
///   * **Peel the top**: add the literal axioms `~r(n-1,j) >= 0` for every
///     `j != k-1`. Since each `r(n-1,j) <= 1`, this leaves `r(n-1,k-1) >= 1`.
///
/// The peel uses VeriPB literal axioms (`~xV` in reverse-polish loads `+1 ~xV >= 0`).
///
/// SOUNDNESS: every step is a checked `pol`/`red`; VeriPB re-validates the whole
/// proof, so an error in this routine can only *withhold* a certificate. The
/// caller supplies `input_row_id` (the `>=` direction of the cardinality row as it
/// appears in the OPB / proof database) and is responsible for the contradiction
/// steps that follow and for the conclusion line.
///
/// Test-only wrapper: production call sites use the weighted generalization
/// [`emit_sinz_introductions_pol_derived_weighted`] directly (this is its
/// all-coefficients-1 specialization, exercised by the certification tests).
#[cfg(test)]
pub(super) fn emit_sinz_introductions_pol_derived<W: Write>(
    writer: &mut VeriPbWriter<W>,
    encoding: &SinzCardinalityEncoding,
    lits: &[i32],
    k: usize,
    input_row_id: super::ConstraintId,
) -> Result<super::ConstraintId> {
    // The cardinality case is the all-coefficients-1 weighted case.
    let unit_coeffs = vec![1i128; lits.len()];
    emit_sinz_introductions_pol_derived_weighted(
        writer,
        encoding,
        &unit_coeffs,
        lits,
        k,
        input_row_id,
    )
}

/// WEIGHTED generalization of `emit_sinz_introductions_pol_derived`: derive the
/// top register `r(n-1, rhs-1) >= 1` of the **weighted** Sinz encoding
/// ([`encode_sinz_weighted`]) for `sum(coeffs[i] * lits[i]) >= rhs` by the same
/// saturating column-sum telescope, generalized so each term contributes its
/// coefficient `c_i` (clamped at `rhs`) instead of `1`. `k == rhs`.
///
/// # The weighted telescope (saturation handles the clamping)
///
/// Column sum `C_i := sum_{j=0}^{k-1} r(i,j)` still lower-bounds the prefix weight
/// clamped at `k`. The per-stage increment is generalized:
///
///   * `C_0 := sum_{j=0}^{min(c_0,k)-1} (r(0,j) >= lit_0)` — the base "lit_0
///     reaches weight level j+1" clauses `[-lit_0, r(0,j)]`, giving
///     `sum_{j<c_0} r(0,j) >= min(c_0,k) * lit_0`.
///   * For `i = 1..n-1`:
///       - `inc_i := sum_{j=0}^{min(c_i,k)-1} (r(i,j) >= lit_i)` [forward (c)]
///         `+ sum_{j=min(c_i,k)}^{k-1} (r(i,j) >= r(i-1,j))` [carry (a)]
///         i.e. the bottom `min(c_i,k)` columns are driven by `lit_i` (contributing
///         `min(c_i,k) * lit_i`), the rest carry the previous column.
///       - `s_i := inc_i + C_{i-1}`, then `C_i := saturate(s_i)`.
///   * `with_input := C_{n-1} + INPUT` (the literal-normalized input row
///     `sum c_m * lit_m >= k`), then `saturate` gives `sum_j r(n-1,j) >= k`.
///   * **Peel the top**: add literal axioms `~r(n-1,j) >= 0` for every `j != k-1`,
///     isolating `r(n-1, k-1) >= 1`.
///
/// With all `c_i == 1` this reduces clause-for-clause to the cardinality telescope.
/// Both the (c) clauses `[-lit_i, r(i,j)]` (for `j < min(c_i,k)`) and the (a) carry
/// clauses `[-r(i-1,j), r(i,j)]` (for all `j`) are emitted by
/// [`encode_sinz_weighted`], so every `id_of` lookup resolves.
///
/// SOUNDNESS: every step is a checked `pol`/`red`; VeriPB re-validates the whole
/// proof, so an error here can only *withhold* a certificate.
pub(super) fn emit_sinz_introductions_pol_derived_weighted<W: Write>(
    writer: &mut VeriPbWriter<W>,
    encoding: &SinzCardinalityEncoding,
    coeffs: &[i128],
    lits: &[i32],
    k: usize,
    input_row_id: super::ConstraintId,
) -> Result<super::ConstraintId> {
    use super::ConstraintId;

    let n = lits.len();
    debug_assert_eq!(coeffs.len(), n, "coeffs and lits must align");
    let aux_base = encoding.aux_base;
    // r(i, j) DIMACS variable, matching `encode_sinz_weighted`'s layout.
    let r = |i: usize, j: usize| -> i32 { (aux_base + (i * k + j) as u32) as i32 };
    // Coefficient of term i, clamped at k=rhs (matching the encoder's clamp). The
    // number of "bottom" columns term i drives directly via its (c) clauses.
    let ci_clamped = |i: usize| -> usize { (coeffs[i].min(k as i128)).max(0) as usize };

    // 1) Introduce every definition clause (all clauses except the final r_top
    //    unit) via `red`, recording each one's allocated ConstraintId so the
    //    telescope can reference them. Clauses are emitted in `encoding.clauses`
    //    order, exactly as `emit_sinz_aux_introductions` does.
    let last = encoding.clauses.len().wrapping_sub(1);
    let mut def_ids: std::collections::HashMap<Vec<i32>, ConstraintId> =
        std::collections::HashMap::new();
    for (idx, clause) in encoding.clauses.iter().enumerate() {
        if idx == last && clause.len() == 1 && clause[0] > 0 {
            // The final r_top unit is *derived* below, not introduced.
            continue;
        }
        let defined = clause
            .iter()
            .map(|&lit| lit.unsigned_abs())
            .filter(|&var| encoding.is_aux(var))
            .max();
        let Some(aux_var) = defined else { continue };
        let id = writer.log_step(ProofStep::Red(
            clause_constraint_body(clause),
            aux_intro_witness(aux_var, clause),
        ))?;
        def_ids.insert(clause.clone(), id);
    }

    let id_of = |clause: Vec<i32>| -> ConstraintId {
        *def_ids
            .get(&clause)
            .expect("definition clause was introduced above")
    };

    // 2) Telescope the saturated column sum C_i := sum_{j} r(i,j).
    // C_0 := sum_{j < min(c_0, k)} (r(0,j) >= lit_0)  ==  [-lit_0, r(0,j)].
    // (For cardinality c_0 = 1 this is the single clause [-lit_0, r(0,0)].)
    let c0 = ci_clamped(0).min(k).max(1); // at least column 0 (c_i >= 1)
    let mut col = id_of(vec![-lits[0], r(0, 0)]);
    for j in 1..c0 {
        let cj = id_of(vec![-lits[0], r(0, j)]);
        col = writer.log_step(ProofStep::Addition(col, cj))?;
    }
    if c0 > 1 {
        // Saturate the base column sum too (clamp at k); harmless for c0 == 1.
        col = writer.log_step(ProofStep::Saturate(col))?;
    }
    for i in 1..n {
        let ci = ci_clamped(i).min(k).max(1);
        // inc_i := sum_{j < ci} (c)[r(i,j) >= lit_i]  +  sum_{j >= ci} (a)carry.
        // Bottom `ci` columns are driven by lit_i; the rest carry r(i-1,j).
        let mut acc = id_of(vec![-lits[i], r(i, 0)]);
        for j in 1..ci {
            let cj = id_of(vec![-lits[i], r(i, j)]);
            acc = writer.log_step(ProofStep::Addition(acc, cj))?;
        }
        for j in ci..k {
            let carry = id_of(vec![-r(i - 1, j), r(i, j)]);
            acc = writer.log_step(ProofStep::Addition(acc, carry))?;
        }
        // s_i := inc_i + C_{i-1}; C_i := saturate(s_i).
        let s = writer.log_step(ProofStep::Addition(acc, col))?;
        col = writer.log_step(ProofStep::Saturate(s))?;
    }

    // 3) with_input := C_{n-1} + INPUT; sat := saturate(with_input)
    //    yields sum_{j=0}^{k-1} r(n-1, j) >= k.
    let with_input = writer.log_step(ProofStep::Addition(col, input_row_id))?;
    let mut top_sum = writer.log_step(ProofStep::Saturate(with_input))?;

    // 4) Peel the top: add literal axioms ~r(n-1, j) >= 0 for all j != k-1.
    //    Each r(n-1, j) <= 1, so this isolates r(n-1, k-1) >= 1.
    //    A reverse-polish expression `<id> ~xV +` adds the axiom +1 ~xV >= 0.
    for j in 0..k {
        if j == k - 1 {
            continue;
        }
        let var = r(n - 1, j);
        let rp = format!("{top_sum} ~x{var} + ;");
        top_sum = writer.log_step(ProofStep::Polynomial(rp))?;
    }

    Ok(top_sum)
}

/// One Sinz-encoded `>=` direction together with everything the pol-derivation
/// ([`emit_sinz_introductions_pol_derived_weighted`]) needs to CERTIFY its top register:
/// the encoding, the normalized `lits`/`rhs` of the row it encodes, and the
/// VeriPB `input_row_id` of that normalized row in the proof database.
///
/// # `input_row_id` — VeriPB stores rows literal-normalized
///
/// Empirically (VeriPB 3.0.2, `--trace`), VeriPB imports each OPB row in
/// **literal-normalized** form — positive coefficients over literals, with `~x`
/// for negated occurrences. For example `-1 x1 -2 x2 >= -2` is stored as
/// `ConstraintId i: 1 ~x1 2 ~x2 >= 1`, which is exactly what
/// [`normalize_ge_positive`] computes. So the `>=` direction's
/// [`normalize_ge_positive`] output (`coeffs`/`lits`/`rhs`) matches the stored row
/// term-for-term, and no extra normalization `pol` step is required even for
/// negative input coefficients — `input_row_id` points straight at the stored row.
///
/// An equality row contributes **two** stored ids: the `>=` direction at id `i`
/// and the `<=`-rewritten-as-`>=` direction at id `i + 1` (both literal-
/// normalized). `encode_instance_proof_producing` tracks the running id so each
/// direction gets its own correct `input_row_id`.
#[derive(Debug, Clone)]
pub(super) struct SinzConstraintCert {
    /// The Sinz aux CNF + aux range for this direction.
    pub encoding: SinzCardinalityEncoding,
    /// Normalized positive coefficients of the row, aligned with `lits` (matches
    /// what `encode_sinz_weighted` was given). Needed by the WEIGHTED pol
    /// telescope so each term contributes its coefficient.
    pub coeffs: Vec<i128>,
    /// Normalized signed DIMACS literals of the row (matches the encoding's
    /// `lits`, and term-for-term the literals of VeriPB's stored input row).
    pub lits: Vec<i32>,
    /// Normalized threshold of the row (`k` = `rhs`; the encoding's top register
    /// is `r(n-1, rhs-1)`).
    pub rhs: usize,
    /// VeriPB ConstraintId of the (literal-normalized) input row this encoding
    /// proves — the `>=` direction's id in the proof database. The telescope adds
    /// this row to the saturated column sum to derive the top register.
    pub input_row_id: super::ConstraintId,
}

/// A full-instance proof-producing CNF encoding: the CNF to hand to the SAT
/// solver, plus the per-Sinz-constraint aux metadata needed to introduce those
/// aux variables into a VeriPB proof (via [`emit_sinz_aux_introductions`]) before
/// the lifted DRAT/RUP refutation.
#[derive(Debug, Clone)]
pub(super) struct ProofProducingEncoding {
    /// Full CNF (DIMACS signed literals) over PB variables and Sinz aux vars.
    pub clauses: Vec<Vec<i32>>,
    /// Per-constraint Sinz encodings whose aux vars must be `red`-introduced (in
    /// this order) before the lifted refutation. Each encoding's aux range is
    /// disjoint and above `num_vars`; introducing them in vector order keeps the
    /// global aux-variable order (each register is fresh when introduced).
    ///
    /// Each carries the metadata ([`SinzConstraintCert`]) the pol-derivation needs
    /// to CERTIFY its top register (`lits`, `rhs`, and the VeriPB `input_row_id`),
    /// so the compact cert path can derive each top register by cutting planes
    /// instead of (unsoundly) asserting it via `rup`.
    pub encodings: Vec<SinzConstraintCert>,
    /// Highest variable index used (PB vars + all aux). The SAT solver should be
    /// created with this many variables.
    pub max_var: u32,
}

/// Cap on total auxiliary variables introduced across the whole instance. Beyond
/// this the proof would be impractically large; we decline (the caller falls back
/// to the aux-free lift), keeping the certificate optional but bounded.
const PROOF_PRODUCING_AUX_BUDGET: u64 = 4_000_000;

/// Encode an entire PB instance into CNF in **proof-producing** form: every
/// non-trivial `>=` direction with threshold `>= 2` uses the Sinz
/// sequential-counter encoding (whose aux vars are VeriPB-`red`-introducible via
/// [`emit_sinz_aux_introductions`]); at-least-one rows (threshold 1) become a
/// single clause (RUP-implied by the input PB row, like the aux-free lift).
///
/// Returns `None` (decline → caller uses the aux-free path) when the instance
/// contains a shape this path does not yet certify: a non-linear term (product of
/// literals), a trivially-false row (handled cheaply by the aux-free path), or an
/// aux-var count over [`PROOF_PRODUCING_AUX_BUDGET`].
///
/// SOUNDNESS: the returned `clauses` and `encodings` come from the SAME Sinz
/// encoding, so the CNF handed to the SAT solver is exactly the CNF introduced
/// into the proof database. The whole proof is re-checked by the external VeriPB
/// checker before any CERTIFIED claim (verify-before-claim, in [`super::cert`]),
/// so a normalization/encoding mismatch can only *withhold* a certificate, never
/// produce a wrong one.
#[must_use]
pub(super) fn encode_instance_proof_producing(
    instance: &PbInstance,
) -> Option<ProofProducingEncoding> {
    let num_pb = instance.num_vars;
    let mut next_aux = num_pb + 1;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut encodings: Vec<SinzConstraintCert> = Vec::new();

    // VeriPB ConstraintId of the NEXT input row not yet consumed, tracked in OPB
    // order. `Ge`/`Le` rows consume one id; `Eq` rows consume two (the `>=` then
    // the `<=`-as-`>=` direction), matching `veripb_input_constraint_count`. This
    // is the id the pol-derivation adds to the saturated column sum, so it MUST
    // stay in lockstep with the `directions` loop below.
    let mut next_input_row_id: u64 = 1;

    for constraint in &instance.constraints {
        // Linear terms only: each term must be a single literal. A non-linear
        // (product) term would need its own AND-aux introduction; decline so the
        // caller falls back to the aux-free path. (DEC-LIN is linear anyway.)
        let mut terms: Vec<(i128, i32)> = Vec::with_capacity(constraint.terms.len());
        for term in &constraint.terms {
            if term.lits.len() != 1 {
                return None;
            }
            let lit = term.lits[0];
            let dimacs = if lit.negated {
                -(lit.var as i32)
            } else {
                lit.var as i32
            };
            terms.push((term.coeff, dimacs));
        }

        // Directions: `Ge` → one; `Eq` → the `>=` direction plus the negated
        // (`<=` rewritten as `>=`) direction. Both directions are implied by the
        // input equality, so their Sinz register units are red-introducible.
        //
        // The input-row id is the FIRST direction's id; the second (Eq `<=`)
        // direction lives at the next id. We pair each direction with its id here
        // so the per-direction Sinz cert records the correct `input_row_id`.
        let mut directions: Vec<(Vec<i128>, Vec<i32>, i128, super::ConstraintId)> = Vec::new();
        let ge_id = super::ConstraintId::new(next_input_row_id)?;
        let (gc, gl, gr) = normalize_ge_positive(&terms, constraint.rhs);
        directions.push((gc, gl, gr, ge_id));
        if constraint.rel == PbRel::Eq {
            let le_id = super::ConstraintId::new(next_input_row_id + 1)?;
            let negated: Vec<(i128, i32)> = terms.iter().map(|&(c, l)| (-c, l)).collect();
            let (nc, nl, nr) = normalize_ge_positive(&negated, -constraint.rhs);
            directions.push((nc, nl, nr, le_id));
        }
        // Advance the running id by this constraint's VeriPB contribution.
        next_input_row_id += if constraint.rel == PbRel::Eq { 2 } else { 1 };

        for (coeffs, lits, rhs, input_row_id) in directions {
            if rhs <= 0 {
                continue; // trivially satisfied: nothing to encode
            }
            let sum: i128 = coeffs.iter().sum();
            if rhs > sum {
                // Trivially false ⇒ instance is (trivially) UNSAT; the aux-free
                // path certifies this cheaply. Decline rather than special-case.
                return None;
            }
            if lits.is_empty() {
                continue;
            }
            if rhs == 1 {
                // At-least-one: a single clause, RUP-implied by the input row.
                clauses.push(lits);
                continue;
            }
            // rhs >= 2: Sinz sequential counter; its aux vars are red-introduced.
            // Decline any rhs beyond u64 BEFORE the casts below: `rhs as u64`
            // truncates mod 2^64 — a multiple of 2^64 would pass the budget
            // gate as 0 and panic on `k - 1` inside encode_sinz_weighted
            // (overflow checks are on), while other residues would silently
            // encode the WRONG threshold. Thresholds that large are far past
            // the aux budget anyway; declining keeps the aux-free route in
            // play and the answer untouched.
            let Ok(rhs_width) = u64::try_from(rhs) else {
                return None;
            };
            let aux_count = (lits.len() as u64).saturating_mul(rhs_width);
            if u64::from(next_aux).saturating_add(aux_count) > PROOF_PRODUCING_AUX_BUDGET {
                return None; // proof would be impractically large; decline
            }
            let enc = encode_sinz_weighted(&coeffs, &lits, rhs, next_aux);
            next_aux += enc.aux_count;
            clauses.extend(enc.clauses.iter().cloned());
            // Record the metadata the pol-derivation needs to CERTIFY r_top: the
            // normalized coeffs/lits/rhs and the VeriPB id of this normalized
            // input row.
            encodings.push(SinzConstraintCert {
                encoding: enc,
                coeffs,
                lits,
                rhs: rhs as usize,
                input_row_id,
            });
        }
    }

    Some(ProofProducingEncoding {
        clauses,
        encodings,
        max_var: next_aux - 1,
    })
}

/// Normalize `sum(coeff_i * lit_i) >= rhs` to all-positive coefficients by
/// flipping negative-coefficient literals: `c*l = |c|*(~l) - |c|`, so a negative
/// `c` becomes `|c|` on `~l` with `rhs += |c|`. Mirrors the solver encoder's
/// `normalize_ge_direction`. Drops zero-coefficient terms.
fn normalize_ge_positive(terms: &[(i128, i32)], rhs: i128) -> (Vec<i128>, Vec<i32>, i128) {
    let mut coeffs = Vec::with_capacity(terms.len());
    let mut lits = Vec::with_capacity(terms.len());
    let mut adjusted = rhs;
    for &(coeff, lit) in terms {
        if coeff == 0 {
            continue;
        }
        if coeff > 0 {
            coeffs.push(coeff);
            lits.push(lit);
        } else {
            coeffs.push(-coeff);
            lits.push(-lit);
            adjusted -= coeff; // rhs += |coeff|
        }
    }
    (coeffs, lits, adjusted)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_matches_known_3_of_3_layout() {
        // n = 3, k = 3, aux_base = 4: aux vars are x4..x12 (9 registers).
        let enc = encode_sinz_cardinality(&[1, 2, 3], 3, 4);
        assert_eq!(enc.aux_base, 4);
        assert_eq!(enc.aux_count, 9);
        // Final clause asserts the top register r(2,2) = x12.
        assert_eq!(enc.clauses.last().unwrap(), &vec![12]);
        // Base-case definition of r(0,0) = x4 (both implication directions).
        assert!(enc.clauses.contains(&vec![-1, 4]));
        assert!(enc.clauses.contains(&vec![-4, 1]));
        // Unreachable levels for the first literal: ~r(0,1), ~r(0,2).
        assert!(enc.clauses.contains(&vec![-5]));
        assert!(enc.clauses.contains(&vec![-6]));
    }

    #[test]
    fn witness_polarity_follows_aux_literal_sign() {
        // Positive occurrence -> force true.
        assert_eq!(aux_intro_witness(7, &[-4, 7]), "x7 -> 1 ;");
        // Negative occurrence -> force false.
        assert_eq!(aux_intro_witness(7, &[-7, 4, 2]), "x7 -> 0 ;");
    }

    #[test]
    fn clause_body_formats_pb_literals_without_semicolon() {
        assert_eq!(
            clause_constraint_body(&[-2, -4, 8]),
            "+1 ~x2 +1 ~x4 +1 x8 >= 1"
        );
        assert_eq!(clause_constraint_body(&[12]), "+1 x12 >= 1");
    }

    #[test]
    fn intro_emits_one_red_per_clause() {
        let enc = encode_sinz_cardinality(&[1, 2, 3], 3, 4);
        let mut writer = VeriPbWriter::new(Vec::new(), 2).expect("header");
        let emitted = emit_sinz_aux_introductions(&mut writer, &enc).expect("intro");
        assert_eq!(emitted, enc.clauses.len());
        let text = String::from_utf8(writer.into_inner()).expect("utf8");
        // First red introduces r(0,0)=x4 with a force-true witness.
        assert!(text.contains("red +1 ~x1 +1 x4 >= 1: x4 -> 1 ;"));
        // The top-register unit clause is introduced force-true.
        assert!(text.contains("red +1 x12 >= 1: x12 -> 1 ;"));
    }

    /// Reference re-implementation of [`crate::encoding`]'s
    /// `encode_sequential_counter` (kept private there). The weighted
    /// proof-producing encoder must match this clause-for-clause and in order, so
    /// the test pins the contract without reaching across module boundaries.
    fn reference_seq_counter(coeffs: &[i128], lits: &[i32], rhs: i128, base: u32) -> Vec<Vec<i32>> {
        let n = coeffs.len();
        let k = rhs as usize;
        let r = |i: usize, j: usize| -> i32 { (base + (i * k + j) as u32) as i32 };
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        let c0 = coeffs[0].min(rhs) as usize;
        for j in 0..c0.min(k) {
            clauses.push(vec![-lits[0], r(0, j)]);
        }
        for j in 0..c0.min(k) {
            clauses.push(vec![-r(0, j), lits[0]]);
        }
        for j in c0..k {
            clauses.push(vec![-r(0, j)]);
        }
        for i in 1..n {
            let ci = coeffs[i].min(rhs) as usize;
            for j in 0..k {
                let w = j + 1;
                clauses.push(vec![-r(i - 1, j), r(i, j)]);
                if w <= ci {
                    clauses.push(vec![-lits[i], r(i, j)]);
                } else if ci > 0 {
                    clauses.push(vec![-lits[i], -r(i - 1, j - ci), r(i, j)]);
                }
                clauses.push(vec![-r(i, j), r(i - 1, j), lits[i]]);
                if w > ci && ci > 0 {
                    clauses.push(vec![-r(i, j), r(i - 1, j), r(i - 1, j - ci)]);
                }
            }
        }
        clauses.push(vec![r(n - 1, k - 1)]);
        clauses
    }

    #[test]
    fn weighted_matches_reference_sequential_counter() {
        // Several shapes: coeff > rhs, coeff > 1 driving predecessor clauses,
        // mixed, and the degenerate cardinality case.
        let cases: &[(&[i128], &[i32], i128)] = &[
            (&[2, 1, 1], &[1, 2, 3], 3), // shape A
            (&[3, 1], &[1, 2], 2),       // shape B: coeff > rhs
            (&[1, 3, 1], &[1, 2, 3], 4), // shape C: ci=3>1 predecessor clauses
            (&[1, 1, 1], &[1, 2, 3], 3), // reduces to cardinality
        ];
        for (coeffs, lits, rhs) in cases {
            let enc = encode_sinz_weighted(coeffs, lits, *rhs, 100);
            let expected = reference_seq_counter(coeffs, lits, *rhs, 100);
            assert_eq!(
                enc.clauses, expected,
                "weighted encoding diverged from sequential counter for {coeffs:?} >= {rhs}"
            );
            assert_eq!(enc.aux_base, 100);
            assert_eq!(enc.aux_count, (coeffs.len() * (*rhs as usize)) as u32);
        }
    }

    #[test]
    fn weighted_reduces_to_cardinality_for_unit_coeffs() {
        // With all coefficients 1, the weighted encoder must produce exactly the
        // cardinality clause set.
        let weighted = encode_sinz_weighted(&[1, 1, 1], &[1, 2, 3], 3, 4);
        let cardinality = encode_sinz_cardinality(&[1, 2, 3], 3, 4);
        assert_eq!(weighted, cardinality);
    }

    #[test]
    fn weighted_emits_predecessor_referencing_clauses() {
        // Shape C exercises the weighted-only clause shapes that reference a
        // predecessor register r(i-1, j-ci). For +1 x1 +3 x2 +1 x3 >= 4 with
        // aux_base = 4 (k = 4): i = 1, ci = 3, j = 3 (w = 4 > ci):
        //   forward  [-lit2, -r(0, 0), r(1, 3)] = [-2, -4, 11]
        //   backward [-r(1, 3), r(0, 3), r(0, 0)] = [-11, 7, 4]
        let enc = encode_sinz_weighted(&[1, 3, 1], &[1, 2, 3], 4, 4);
        assert!(
            enc.clauses.contains(&vec![-2, -4, 11]),
            "missing weighted forward predecessor clause"
        );
        assert!(
            enc.clauses.contains(&vec![-11, 7, 4]),
            "missing weighted backward predecessor clause"
        );
        // The largest-aux-index witness rule still defines r(1,3)=x11 in both:
        // positive in the forward clause (force 1), negative in the backward
        // clause (force 0).
        assert_eq!(aux_intro_witness(11, &[-2, -4, 11]), "x11 -> 1 ;");
        assert_eq!(aux_intro_witness(11, &[-11, 7, 4]), "x11 -> 0 ;");
    }

    /// END-TO-END acceptance: build a tiny UNSAT cardinality OPB instance, emit a
    /// full VeriPB proof (Sinz aux introductions for the `>= 3` row + a single RUP
    /// deriving the empty constraint), and require the OFFICIAL VeriPB checker to
    /// print "VERIFIED UNSATISFIABLE". Skips cleanly if the checker is absent.
    #[test]
    fn sinz_reified_intro_is_veripb_verified() {
        use std::path::PathBuf;
        use std::process::Command;

        // Locate the official VeriPB checker; skip if unavailable.
        let veripb = {
            let mut found: Option<PathBuf> = None;
            if let Some(p) = std::env::var_os("VERIPB_BIN").map(PathBuf::from) {
                if p.is_file() {
                    found = Some(p);
                }
            }
            if found.is_none() {
                // Fall back to `veripb` resolved from PATH.
                found = std::env::var_os("PATH").and_then(|paths| {
                    std::env::split_paths(&paths)
                        .map(|dir| dir.join("veripb"))
                        .find(|p| p.is_file())
                });
            }
            match found {
                Some(p) => p,
                None => {
                    eprintln!("VeriPB checker not present; skipping reified-intro verification");
                    return;
                }
            }
        };

        // Tiny UNSAT instance over 3 vars:
        //   C1: x1 + x2 + x3 >= 3          (forces all three true)
        //   C2: ~x1 + ~x2 + ~x3 >= 2       (the normalized form of "<= 1": at most
        //                                   one true). C1 and C2 are contradictory.
        let opb = "* #variable= 3 #constraint= 2\n\
                   +1 x1 +1 x2 +1 x3 >= 3 ;\n\
                   +1 ~x1 +1 ~x2 +1 ~x3 >= 2 ;\n";

        // Build the proof: introduce the Sinz aux of C1 (>= 3), then RUP empty.
        // f = 2 input constraints (C1, C2).
        let enc = encode_sinz_cardinality(&[1, 2, 3], 3, /* aux_base after x1..x3 */ 4);
        let mut writer = VeriPbWriter::new(Vec::<u8>::new(), 2).expect("header");
        let emitted = emit_sinz_aux_introductions(&mut writer, &enc).expect("aux intros");
        assert_eq!(emitted, enc.clauses.len());
        // With the Sinz definition of C1 in the database (so x1=x2=x3=1) plus C2
        // (at most one true), the empty constraint follows by RUP.
        writer
            .log_step(ProofStep::Rup(String::from(">= 1 ;")))
            .expect("rup empty");
        // Conclusion points at the RUP-derived contradiction: f(2) + emitted + 1.
        let final_id =
            super::super::ConstraintId::new(2 + emitted as u64 + 1).expect("non-zero id");
        writer.conclude_unsat(final_id).expect("conclude");
        let proof = String::from_utf8(writer.into_inner()).expect("utf8 proof");

        // Write OPB + proof to temp files and run the official checker.
        let stem = format!("ay_pb_sinz_reified_{}", std::process::id());
        let opb_path = std::env::temp_dir().join(format!("{stem}.opb"));
        let pbp_path = std::env::temp_dir().join(format!("{stem}.pbp"));
        std::fs::write(&opb_path, opb).expect("write opb");
        std::fs::write(&pbp_path, &proof).expect("write pbp");

        let output = Command::new(&veripb)
            .arg(&opb_path)
            .arg(&pbp_path)
            .output()
            .expect("run veripb");

        let _ = std::fs::remove_file(&opb_path);
        let _ = std::fs::remove_file(&pbp_path);

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stdout.contains("VERIFIED UNSATISFIABLE"),
            "VeriPB did not verify the Sinz reified-intro proof\n\
             stdout: {stdout}\nstderr: {stderr}\nproof:\n{proof}"
        );
    }

    /// Locate the official VeriPB checker (env `VERIPB_BIN`, else `veripb`
    /// from PATH), returning `None` to signal a clean test skip when absent.
    fn locate_veripb() -> Option<std::path::PathBuf> {
        use std::path::PathBuf;
        if let Some(p) = std::env::var_os("VERIPB_BIN").map(PathBuf::from) {
            if p.is_file() {
                return Some(p);
            }
        }
        std::env::var_os("PATH").and_then(|paths| {
            std::env::split_paths(&paths)
                .map(|dir| dir.join("veripb"))
                .find(|p| p.is_file())
        })
    }

    /// Run the official VeriPB checker over `opb`/`proof` and assert it prints
    /// "VERIFIED UNSATISFIABLE". `tag` distinguishes temp files / messages.
    fn assert_veripb_verifies(veripb: &std::path::Path, tag: &str, opb: &str, proof: &str) {
        use std::process::Command;
        let stem = format!("ay_pb_{tag}_{}", std::process::id());
        let opb_path = std::env::temp_dir().join(format!("{stem}.opb"));
        let pbp_path = std::env::temp_dir().join(format!("{stem}.pbp"));
        std::fs::write(&opb_path, opb).expect("write opb");
        std::fs::write(&pbp_path, proof).expect("write pbp");

        let output = Command::new(veripb)
            .arg(&opb_path)
            .arg(&pbp_path)
            .output()
            .expect("run veripb");

        let _ = std::fs::remove_file(&opb_path);
        let _ = std::fs::remove_file(&pbp_path);

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stdout.contains("VERIFIED UNSATISFIABLE"),
            "VeriPB did not verify the weighted reified-intro proof ({tag})\n\
             stdout: {stdout}\nstderr: {stderr}\nproof:\n{proof}"
        );
    }

    /// Build a VeriPB proof for a tiny UNSAT instance whose first row is the
    /// weighted PB constraint `sum(coeffs*lits) >= rhs`: introduce that row's
    /// Sinz aux via the largest-index polarity witness, then RUP the empty
    /// constraint and conclude UNSAT. `f_count` is the number of input OPB rows.
    fn build_weighted_unsat_proof(
        coeffs: &[i128],
        lits: &[i32],
        rhs: i128,
        aux_base: u32,
        f_count: u64,
    ) -> String {
        let enc = encode_sinz_weighted(coeffs, lits, rhs, aux_base);
        let mut writer = VeriPbWriter::new(Vec::<u8>::new(), f_count).expect("header");
        let emitted = emit_sinz_aux_introductions(&mut writer, &enc).expect("aux intros");
        assert_eq!(emitted, enc.clauses.len());
        // The aux definitions pin the weighted constraint; together with the
        // contradicting input rows the empty constraint follows by RUP.
        writer
            .log_step(ProofStep::Rup(String::from(">= 1 ;")))
            .expect("rup empty");
        let final_id =
            super::super::ConstraintId::new(f_count + emitted as u64 + 1).expect("non-zero id");
        writer.conclude_unsat(final_id).expect("conclude");
        String::from_utf8(writer.into_inner()).expect("utf8 proof")
    }

    /// END-TO-END acceptance for the WEIGHTED case: for several tiny UNSAT
    /// weighted OPB instances, emit the Sinz aux introductions (weighted clauses)
    /// + a RUP deriving the empty constraint, and require the OFFICIAL VeriPB
    /// checker to print "VERIFIED UNSATISFIABLE". Skips cleanly if the checker is
    /// absent. Covers (a) a coefficient > rhs and (b) a coefficient > 1 that
    /// drives the `r(i-1, j-ci)` predecessor clauses.
    #[test]
    fn sinz_weighted_reified_intro_is_veripb_verified() {
        let Some(veripb) = locate_veripb() else {
            eprintln!("VeriPB checker not present; skipping weighted reified-intro verification");
            return;
        };

        // Shape A: +2 x1 +1 x2 +1 x3 >= 3 (coeff 2 = c0 < rhs). Contradict with
        // ~x1 >= 1: x1 must be false, but then max weight = 2 < 3 => UNSAT.
        // aux_base = 4 (after x1..x3); f = 2 input rows.
        let opb_a = "* #variable= 3 #constraint= 2\n\
                     +2 x1 +1 x2 +1 x3 >= 3 ;\n\
                     +1 ~x1 >= 1 ;\n";
        let proof_a = build_weighted_unsat_proof(&[2, 1, 1], &[1, 2, 3], 3, 4, 2);
        assert_veripb_verifies(&veripb, "sinz_w_a", opb_a, &proof_a);

        // Shape B: +3 x1 +1 x2 >= 2 with a COEFFICIENT GREATER THAN RHS (c0 is
        // clamped from 3 to 2). Contradict with ~x1 >= 1: x1 false leaves max
        // weight 1 < 2 => UNSAT. aux_base = 3 (after x1,x2); f = 2.
        let opb_b = "* #variable= 2 #constraint= 2\n\
                     +3 x1 +1 x2 >= 2 ;\n\
                     +1 ~x1 >= 1 ;\n";
        let proof_b = build_weighted_unsat_proof(&[3, 1], &[1, 2], 2, 3, 2);
        assert_veripb_verifies(&veripb, "sinz_w_b", opb_b, &proof_b);

        // Shape C: +1 x1 +3 x2 +1 x3 >= 4 — ci = 3 > 1 in the inductive step
        // drives the r(i-1, j-ci) PREDECESSOR clauses (e.g. [-2,-4,11] and
        // [-11,7,4]). Contradict with ~x1 >= 1 and ~x2 >= 1: only x3 (weight 1)
        // remains, max 1 < 4 => UNSAT. aux_base = 4 (after x1..x3); f = 3.
        let opb_c = "* #variable= 3 #constraint= 3\n\
                     +1 x1 +3 x2 +1 x3 >= 4 ;\n\
                     +1 ~x1 >= 1 ;\n\
                     +1 ~x2 >= 1 ;\n";
        let proof_c = build_weighted_unsat_proof(&[1, 3, 1], &[1, 2, 3], 4, 4, 3);
        assert_veripb_verifies(&veripb, "sinz_w_c", opb_c, &proof_c);
    }

    /// Build a VeriPB proof that DERIVES the Sinz top register `r(n-1,k-1) >= 1`
    /// by cutting planes (`pol`) — never asserting it via `rup`/force-`red` — for
    /// the cardinality row `x1 + ... + xn >= k`, then refutes a contradicting set
    /// of unit rows. Returns the proof text and the OPB.
    ///
    /// Contradiction: force `x_k, ..., x_n` false via units, so the max count of
    /// the first `k-1` free literals is `k-1 < k` — UNSAT. Those units are *not*
    /// referenced by the `pol` chain (the derivation is purely from the input row
    /// + the `red`-introduced Sinz definitions); they only drive the final RUP.
    fn build_pol_derived_rtop_proof(n: usize, k: usize) -> (String, String) {
        let lits: Vec<i32> = (1..=n as i32).collect();
        let aux_base = (n as u32) + 1;
        let enc = encode_sinz_cardinality(&lits, k, aux_base);

        // OPB: input cardinality row (id 1) + units ~x_k .. ~x_n (ids 2..).
        let num_vars = n + n * k;
        let units: Vec<i32> = (k as i32..=n as i32).collect();
        let f = 1 + units.len();
        let mut opb = format!("* #variable= {num_vars} #constraint= {f}\n");
        opb.push_str("+1 ");
        opb.push_str(
            &(1..=n)
                .map(|v| format!("x{v}"))
                .collect::<Vec<_>>()
                .join(" +1 "),
        );
        opb.push_str(&format!(" >= {k} ;\n"));
        for u in &units {
            opb.push_str(&format!("+1 ~x{u} >= 1 ;\n"));
        }

        let mut writer = VeriPbWriter::new(Vec::<u8>::new(), f as u64).expect("header");
        let input_row_id = super::super::ConstraintId::new(1).expect("input row id");
        // Derive r_top via cutting planes.
        let _rtop = emit_sinz_introductions_pol_derived(&mut writer, &enc, &lits, k, input_row_id)
            .expect("pol-derived r_top");
        // With r_top forced 1 plus the units (count < k), the empty constraint
        // follows by RUP (the backward definition clauses unit-propagate down).
        let empty_id = writer
            .log_step(ProofStep::Rup(String::from(">= 1 ;")))
            .expect("rup empty");
        writer.conclude_unsat(empty_id).expect("conclude");
        let proof = String::from_utf8(writer.into_inner()).expect("utf8 proof");
        (opb, proof)
    }

    /// END-TO-END acceptance for the CUTTING-PLANE-DERIVED top register: for a
    /// range of `(n, k)` cardinality instances — including `k <= n-2`, where a
    /// single Farkas combination provably cannot derive `r_top` and the staged
    /// saturating telescope is required — emit a proof that derives
    /// `r(n-1,k-1) >= 1` purely by `pol` from the input row + `red`-introduced
    /// Sinz definitions, then refutes a contradicting unit set, and require the
    /// OFFICIAL VeriPB checker to print "VERIFIED UNSATISFIABLE". Skips cleanly if
    /// the checker is absent.
    #[test]
    fn sinz_cardinality_pol_derived_rtop_is_veripb_verified() {
        let Some(veripb) = locate_veripb() else {
            eprintln!("VeriPB checker not present; skipping pol-derived r_top verification");
            return;
        };

        // Cover the single-division band (k in {n-1, n}) AND the genuinely staged
        // regime (k <= n-2): (4,3)=k=n-1, (5,3)/(8,6)/(6,4)/(8,5)/(10,4)=k<=n-2,
        // (3,3)=k=n, (4,1)=k=1 edge.
        let cases: &[(usize, usize)] = &[
            (4, 3),
            (5, 3),
            (8, 6),
            (6, 4),
            (8, 5),
            (10, 4),
            (3, 3),
            (4, 1),
        ];
        for &(n, k) in cases {
            let (opb, proof) = build_pol_derived_rtop_proof(n, k);
            assert_veripb_verifies(&veripb, &format!("sinz_pol_{n}_{k}"), &opb, &proof);
        }
    }

    /// Build a VeriPB proof that DERIVES the WEIGHTED Sinz top register
    /// `r(n-1,rhs-1) >= 1` by cutting planes (`pol`) for the weighted row
    /// `sum(coeffs*lits) >= rhs`, then refutes a contradicting set of unit rows
    /// (forcing enough literals false that the remaining max weight is `< rhs`).
    /// Returns the OPB and proof text. `false_lits` are the 1-based variables to
    /// force false (each appears as a `~x >= 1` unit row after the input row).
    fn build_pol_derived_rtop_weighted_proof(
        coeffs: &[i128],
        rhs: i128,
        false_lits: &[i32],
    ) -> (String, String) {
        let n = coeffs.len();
        let lits: Vec<i32> = (1..=n as i32).collect();
        let aux_base = (n as u32) + 1;
        let k = rhs as usize;
        let enc = encode_sinz_weighted(coeffs, &lits, rhs, aux_base);

        let num_vars = n + n * k;
        let f = 1 + false_lits.len();
        let mut opb = format!("* #variable= {num_vars} #constraint= {f}\n");
        // Input weighted row (id 1).
        let body: Vec<String> = coeffs
            .iter()
            .zip(&lits)
            .map(|(c, l)| format!("+{c} x{l}"))
            .collect();
        opb.push_str(&format!("{} >= {rhs} ;\n", body.join(" ")));
        for &u in false_lits {
            opb.push_str(&format!("+1 ~x{u} >= 1 ;\n"));
        }

        let mut writer = VeriPbWriter::new(Vec::<u8>::new(), f as u64).expect("header");
        let input_row_id = super::super::ConstraintId::new(1).expect("input row id");
        let _rtop = emit_sinz_introductions_pol_derived_weighted(
            &mut writer,
            &enc,
            coeffs,
            &lits,
            k,
            input_row_id,
        )
        .expect("weighted pol-derived r_top");
        // r_top forced 1 plus the units (remaining weight < rhs) => empty by RUP.
        let empty_id = writer
            .log_step(ProofStep::Rup(String::from(">= 1 ;")))
            .expect("rup empty");
        writer.conclude_unsat(empty_id).expect("conclude");
        let proof = String::from_utf8(writer.into_inner()).expect("utf8 proof");
        (opb, proof)
    }

    /// END-TO-END acceptance for the WEIGHTED CUTTING-PLANE-DERIVED top register:
    /// for several weighted instances (coefficients > 1, coefficients > rhs, mixed)
    /// derive `r(n-1,rhs-1) >= 1` purely by `pol` from the input weighted row +
    /// `red`-introduced Sinz definitions, then refute a contradicting unit set, and
    /// require the OFFICIAL VeriPB checker to print "VERIFIED UNSATISFIABLE". Skips
    /// cleanly if the checker is absent.
    #[test]
    fn sinz_weighted_pol_derived_rtop_is_veripb_verified() {
        let Some(veripb) = locate_veripb() else {
            eprintln!(
                "VeriPB checker not present; skipping weighted pol-derived r_top verification"
            );
            return;
        };

        // (coeffs, rhs, false_lits-to-contradict). After forcing false_lits false,
        // the remaining max weight must be < rhs so the RUP closes.
        struct Case {
            coeffs: &'static [i128],
            rhs: i128,
            false_lits: &'static [i32],
        }
        let cases: &[Case] = &[
            // c0 = 2 < rhs; force x1 false => max 2 < 3.
            Case {
                coeffs: &[2, 1, 1],
                rhs: 3,
                false_lits: &[1],
            },
            // coeff > rhs (clamped 3->2); force x1 false => max 1 < 2.
            Case {
                coeffs: &[3, 1],
                rhs: 2,
                false_lits: &[1],
            },
            // ci = 3 > 1 inductive predecessor clauses; force x1,x2 false => max 1 < 4.
            Case {
                coeffs: &[1, 3, 1],
                rhs: 4,
                false_lits: &[1, 2],
            },
            // all-2 weighted, staged regime; force x1,x2,x3 false => max 2 < 4.
            Case {
                coeffs: &[2, 2, 2, 2],
                rhs: 4,
                false_lits: &[1, 2, 3],
            },
            // mixed coeffs, larger rhs; force x1 false => max 1+2+3 = 6 < 7.
            Case {
                coeffs: &[4, 1, 2, 3],
                rhs: 7,
                false_lits: &[1],
            },
            // all-3 weighted, multi-stage saturation; force x1,x2 false => max 3+3 = 6 < 7.
            Case {
                coeffs: &[3, 3, 3, 3],
                rhs: 7,
                false_lits: &[1, 2],
            },
        ];
        for (idx, c) in cases.iter().enumerate() {
            let (opb, proof) = build_pol_derived_rtop_weighted_proof(c.coeffs, c.rhs, c.false_lits);
            assert_veripb_verifies(&veripb, &format!("sinz_wpol_{idx}"), &opb, &proof);
        }
    }
}
