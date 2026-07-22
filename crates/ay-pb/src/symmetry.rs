// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sound instance-level symmetry breaking for pseudo-Boolean instances.
//!
//! This module detects the safest, highest-value class of symmetries —
//! **fully interchangeable variables** — and adds *lex-leader* ordering
//! constraints to the instance before solving. Symmetry breaking changes the
//! search effort, never the verdict: every satisfying class keeps at least one
//! representative.
//!
//! # What is detected
//!
//! Two variables `x_a` and `x_b` are *fully interchangeable* when the
//! transposition `(a b)` is an exact automorphism of the pair
//! (constraints ∪ objective). The cheap, provably-sound sufficient condition we
//! use is **identical column signatures**: in every constraint `x_a` and `x_b`
//! occur with the same coefficient *and* the same polarity, and they have the
//! same objective coefficient and polarity. When that holds, swapping the two
//! columns maps the instance to itself term-for-term, so the swap is a genuine
//! automorphism.
//!
//! For a maximal group `{x_a, x_b, x_c, …}` of mutually interchangeable
//! variables (ordered by variable index `a < b < c < …`) we add the lex-leader
//! chain
//!
//! ```text
//! x_a >= x_b,  x_b >= x_c,  …
//! ```
//!
//! encoded as the pseudo-Boolean constraints `+1 x_a -1 x_b >= 0`, etc.
//!
//! # Soundness argument
//!
//! Let `G` be a group of variables whose every pairwise transposition is an
//! automorphism of the instance (the column-signature test guarantees this).
//! Then the full symmetric group on `G` is a subgroup of the automorphism
//! group. Take any satisfying assignment `M`. Sort the values of the variables
//! in `G` into non-increasing order by applying the permutation `σ` of `G` that
//! reorders them; `σ` is an automorphism, so `σ(M)` is also a satisfying
//! assignment **with the same objective value** (the objective is invariant
//! because all members of `G` share one objective coefficient). The sorted
//! assignment satisfies `x_a >= x_b >= …`. Hence:
//!
//! * Satisfiability is preserved: every model has a symmetric image obeying the
//!   chain, so the augmented instance is SAT iff the original is.
//! * The optimum is preserved: the objective is invariant on each orbit, so the
//!   best feasible objective value is unchanged.
//!
//! Adding `+1 x_a -1 x_b >= 0` therefore removes only symmetric duplicates and
//! never the last representative of an orbit. This is the standard lex-leader
//! argument (Crawford et al., 1996; Devriendt et al., "Symmetric Explanation
//! Learning", SAT 2016).
//!
//! # Verified vector (matrix / row & column) transpositions
//!
//! Beyond single-variable swaps, the module also detects *variable-vector*
//! transpositions `σ = (a_1 b_1)(a_2 b_2)…(a_k b_k)` — the symmetry of
//! matrix-structured instances where two index-rows (or columns) of a Boolean
//! matrix may be exchanged. Candidate generators are derived from pairs of
//! same-shape constraints, then **exactly verified**: a candidate `σ` is only
//! accepted when applying it to the constraint multiset reproduces that multiset
//! and the objective is invariant. For a verified `σ` we add the single
//! binary-weighted lex-leader constraint
//!
//! ```text
//! Σ 2^(k-i) a_i  -  Σ 2^(k-i) b_i  >=  0
//! ```
//!
//! whose left side compares the two row vectors as binary numbers (MSB first).
//! Since `binval(a) >= binval(b)` iff `a ≥_lex b`, and `σ` swaps the two
//! vectors, every orbit keeps a representative satisfying it; the constraint is
//! sound by the same lex-leader argument. We bail (add nothing) when `k`
//! exceeds 62 (to keep the `2^(k-i)` weights inside `i128`) or when any candidate
//! fails exact verification.
//!
//! # Conservative gates
//!
//! * Variables that appear in any **non-linear** term (a product of literals)
//!   are excluded entirely — the simple column signature does not capture
//!   product structure, so we add nothing for them.
//! * Variables that appear **more than once** in the same constraint are
//!   excluded (ambiguous signature).
//! * Detection is skipped for instances above a size budget (the pairwise
//!   bucketing is by exact signature hashing, but we still bound work).
//! * Symmetry breaking is **never** applied on the proof-logging path; the
//!   caller must only invoke it for uncertified solves.

use std::collections::BTreeMap;

use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

/// Maximum number of variables for which we run interchangeability detection.
///
/// Detection is `O(V * T)` where `T` is the total number of terms; the bucket
/// comparison is exact. We keep a generous ceiling so realistic competition
/// instances are covered while pathological inputs stay bounded.
const MAX_VARS_FOR_DETECTION: usize = 2_000_000;

/// A summary of the symmetry breaking that was applied to an instance.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SymmetryBreakResult {
    /// Number of interchangeable-variable groups (size >= 2) detected.
    pub interchangeable_groups: usize,
    /// Number of verified variable-vector transposition generators (matrix
    /// row/column symmetry) for which a binary-weighted lex constraint was added.
    pub vector_transposition_generators: usize,
    /// Number of lex-leader ordering constraints added to the instance (sum of
    /// the single-variable chains and the vector transposition constraints).
    pub lex_constraints_added: usize,
}

impl SymmetryBreakResult {
    /// Whether any symmetry-breaking constraint was added.
    #[must_use]
    pub fn changed_instance(&self) -> bool {
        self.lex_constraints_added > 0
    }
}

/// Structural gate: does the instance carry a *large* automorphism group worth
/// the symmetry arm (probe + scalable detection)? This is the ZERO-OVERHEAD
/// no-op guard for non-symmetric instances — it must be cheap and reject anything
/// that would not yield generators, so the normal portfolio keeps the FULL
/// budget.
///
/// Two stages, cheapest first:
///   1. O(terms) pre-filter: linear, in the scalable size range, and not wildly
///      shape-diverse (a non-templated instance with thousands of distinct
///      constraint shapes cannot have matrix-interchange symmetry).
///   2. ONE colour-refinement pass (1-WL, near-linear). The instance only passes
///      if the refined VARIABLE partition has substantial NON-SINGLETON structure
///      — i.e. many variables remain in equivalence cells of size ≥ 2, the
///      signature of a real automorphism group (e.g. mat: all variables in 2
///      cells of size >1000). A non-symmetric instance refines to (near-)all
///      singletons (e.g. dbst: 2800/2800 singletons) and is rejected here. The
///      refinement is the same code the detector reuses; it is ~30–330 ms even on
///      the largest instances, so a rejected instance pays only that, not the
///      probe + failed detection.
///
/// Returns `false` (no arm) for anything without exploitable symmetry. It can
/// only ever cause the detector to RUN or NOT RUN — soundness is unaffected
/// either way (every emitted constraint is still verified).
#[must_use]
pub fn is_highly_symmetric_candidate(instance: &PbInstance) -> bool {
    let num_constraints = instance.constraints.len();
    // The scalable detector only engages above the legacy pairwise cap; below it
    // the cheap pairwise search already runs, so the gate targets large instances.
    if num_constraints <= MAX_CONSTRAINTS_FOR_GENERATOR_SEARCH {
        return false;
    }
    if num_constraints > MAX_CONSTRAINTS_FOR_SCALABLE {
        return false;
    }
    // (1) O(terms) pre-filter: reject non-linear and wildly shape-diverse inputs.
    let mut shapes: std::collections::HashSet<u64> = std::collections::HashSet::new();
    for c in &instance.constraints {
        let mut coeffs: Vec<(i128, bool)> = Vec::with_capacity(c.terms.len());
        for t in &c.terms {
            if t.lits.len() != 1 {
                return false; // non-linear
            }
            coeffs.push((t.coeff, t.lits[0].negated));
        }
        coeffs.sort_unstable();
        shapes.insert(hash64(&(c.rel, c.rhs, &coeffs)));
        if shapes.len() > HIGHLY_SYMMETRIC_MAX_SHAPES {
            return false; // far too shape-diverse for matrix symmetry
        }
    }

    // (2) Refinement check: only proceed if the refined partition shows real
    // automorphism structure. This is what makes the arm a TRUE no-op on
    // shape-regular-but-asymmetric instances (e.g. dbst, which passes (1) with 64
    // shapes but refines to all singletons).
    refined_partition_has_symmetry(instance)
}

/// Maximum number of distinct constraint shapes for the highly-symmetric gate.
/// The "mat" family has ~6 shapes across 35k–408k rows; a generous cap keeps the
/// gate broad while still excluding shape-diverse (non-templated) instances. This
/// is only a cheap pre-filter — the refinement check below is the real gate.
const HIGHLY_SYMMETRIC_MAX_SHAPES: usize = 64;

/// Minimum fraction (in tenths) of ACTIVE variables that must lie in a
/// non-singleton refined cell for the instance to be treated as symmetric. mat
/// puts 100% in non-singleton cells; a non-symmetric instance puts ~0%.
const SYMMETRY_NONSINGLETON_TENTHS: usize = 5; // >= 50% of active vars

/// Runs one colour-refinement pass and reports whether the refined VARIABLE
/// partition has substantial non-singleton structure (≥ a configurable fraction
/// of active variables in cells of size ≥ 2, and at least one sizeable cell).
fn refined_partition_has_symmetry(instance: &PbInstance) -> bool {
    let Some(index) = build_scalable_index(instance) else {
        return false;
    };
    let mut cell_sizes: BTreeMap<u64, usize> = BTreeMap::new();
    let mut active = 0usize;
    for vi in 0..index.nvars {
        if !index.var_incidence[vi].is_empty() {
            active += 1;
            *cell_sizes.entry(index.base_var_color[vi]).or_insert(0) += 1;
        }
    }
    if active == 0 {
        return false;
    }
    let in_nonsingleton: usize = cell_sizes.values().filter(|&&n| n >= 2).sum();
    let max_cell = cell_sizes.values().copied().max().unwrap_or(0);
    // A genuine automorphism group leaves a large share of variables mutually
    // interchangeable; require both a high fraction AND a non-trivial cell.
    max_cell >= 2 && in_nonsingleton * 10 >= active * SYMMETRY_NONSINGLETON_TENTHS
}

/// Per-variable column signature: the set of `(constraint_index, coeff,
/// negated)` entries plus the objective `(coeff, negated)`.
///
/// Two variables are fully interchangeable iff their signatures are equal. We
/// store the signature as sorted vectors so equality is a cheap `==`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ColumnSignature {
    /// `(constraint_index, coeff, negated)` for each constraint the variable
    /// occurs in, sorted ascending. `constraint_index` ties the occurrence to a
    /// specific row so two variables match only when they occur in the *same*
    /// rows with the *same* coefficient and polarity.
    rows: Vec<(usize, i128, bool)>,
    /// Objective term, if any: `(coeff, negated)`. `None` when the variable does
    /// not occur in the objective.
    objective: Option<(i128, bool)>,
}

/// Outcome of attempting to build a single variable's column signature.
///
/// A free variable (one that occurs nowhere) keeps a `Linear` signature with
/// empty `rows` and no `objective`; it is filtered out before bucketing because
/// breaking free variables is pointless (and could only ever pair variables
/// that are vacuously interchangeable, yielding no search benefit).
enum SignatureOutcome {
    /// The variable has a well-formed linear signature.
    Linear(ColumnSignature),
    /// The variable cannot be safely used for symmetry detection (it occurs in
    /// a non-linear term, or appears multiple times in one constraint, etc.).
    Excluded,
}

/// Detects fully interchangeable variable groups and appends lex-leader
/// ordering constraints to a *copy* of the instance.
///
/// Returns the augmented instance together with a [`SymmetryBreakResult`]. The
/// returned instance is **equisatisfiable** with the input and has the **same
/// optimum** (see the module-level soundness argument). When no sound symmetry
/// is found, the instance is returned unchanged with an all-zero result.
///
/// The input instance is not mutated. The header `num_vars` is preserved (no
/// new variables are introduced); `num_constraints` is updated to reflect the
/// added rows.
#[must_use]
pub fn break_symmetries(instance: &PbInstance) -> (PbInstance, SymmetryBreakResult) {
    break_symmetries_with_deadline(instance, None)
}

/// Like [`break_symmetries`] but bounds the (scalable) generator search by an
/// optional wall-clock `deadline`. When the deadline is hit mid-search the
/// detector returns whatever verified generators it already found (or none) —
/// always sound, since every emitted constraint comes from a verified generator.
#[must_use]
pub fn break_symmetries_with_deadline(
    instance: &PbInstance,
    deadline: Option<std::time::Instant>,
) -> (PbInstance, SymmetryBreakResult) {
    let mut augmented = instance.clone();
    let mut result = SymmetryBreakResult::default();

    // (1) Interchangeable single variables: emit `x_a >= x_b` chains.
    let groups = detect_interchangeable_groups(instance);
    for group in &groups {
        // `group` is sorted ascending by variable index. Emit the chain
        // x_g0 >= x_g1 >= ... as consecutive `+1 x_gi -1 x_gi+1 >= 0`.
        for window in group.windows(2) {
            let hi = window[0];
            let lo = window[1];
            augmented.constraints.push(lex_ge_constraint(hi, lo));
            result.lex_constraints_added += 1;
        }
    }
    result.interchangeable_groups = groups.len();

    // (2) Verified variable-vector transposition generators (matrix/row & column
    // symmetry). Each generator is an *exactly verified* automorphism, so the
    // binary-weighted lex constraint we add is sound. Generators are computed on
    // the original instance (not the partially-augmented one) so verification is
    // against the genuine input.
    //
    // For small instances the legacy O(rows^2) pairwise search is used (it is
    // exhaustive over disjoint generators on tiny inputs and keeps the existing
    // tests/behaviour exact). For large instances — the highly-symmetric "mat"
    // family with tens to hundreds of thousands of constraints, where the
    // pairwise search is skipped — the SCALABLE colour-refinement detector runs
    // instead. Both feed the SAME `is_automorphism` oracle and lex emitter.
    if instance.constraints.len() > MAX_CONSTRAINTS_FOR_GENERATOR_SEARCH {
        // SCALABLE path (large, highly-symmetric instances): colour-refinement +
        // individualise-refine yields general permutation generators; emit one
        // lex-leader `x <=_lex σ(x)` per verified generator.
        let generators = detect_scalable_generators(instance, deadline);
        for generator in &generators {
            if let Some(constraint) = permutation_lex_leader_constraint(generator) {
                augmented.constraints.push(constraint);
                result.vector_transposition_generators += 1;
                result.lex_constraints_added += 1;
            }
        }
    } else {
        // LEGACY path (small instances): exact pairwise involution search,
        // emitting the binary-weighted vector lex-leader (unchanged behaviour).
        let generators = detect_verified_vector_transpositions(instance);
        for generator in &generators {
            if let Some(constraint) = binary_lex_leader_constraint(&generator.a, &generator.b) {
                augmented.constraints.push(constraint);
                result.vector_transposition_generators += 1;
                result.lex_constraints_added += 1;
            }
        }
    }

    augmented.num_constraints = augmented
        .num_constraints
        .saturating_add(u32::try_from(result.lex_constraints_added).unwrap_or(u32::MAX));

    (augmented, result)
}

/// Builds the lex-leader constraint `x_hi >= x_lo`, i.e. `+1 x_hi -1 x_lo >= 0`.
///
/// Soundness: for any assignment violating this (`x_hi = 0, x_lo = 1`) the
/// transposition `(hi lo)` — an automorphism of the instance — yields an
/// equivalent assignment satisfying it. So no orbit loses all representatives.
fn lex_ge_constraint(hi: u32, lo: u32) -> PbConstraint {
    PbConstraint {
        terms: vec![
            PbTerm {
                coeff: 1,
                lits: vec![PbLit {
                    var: hi,
                    negated: false,
                }],
            },
            PbTerm {
                coeff: -1,
                lits: vec![PbLit {
                    var: lo,
                    negated: false,
                }],
            },
        ],
        rel: PbRel::Ge,
        rhs: 0,
    }
}

/// Maximum vector length for the binary-weighted lex constraint.
///
/// The constraint uses coefficients `2^(k-i)`; with `k` up to 62 the largest
/// coefficient `2^61` fits comfortably in `i128`. Beyond that we bail (add
/// nothing) rather than risk overflow.
const MAX_LEX_VECTOR_LEN: usize = 62;

/// Maximum number of constraints we will scan when searching for verified
/// vector-transposition generators. The candidate search is `O(rows^2 * width)`
/// in the worst case; we bound it to keep front-end time negligible.
const MAX_CONSTRAINTS_FOR_GENERATOR_SEARCH: usize = 4_000;

/// Maximum number of verified generators we emit per instance.
const MAX_GENERATORS: usize = 256;

/// A verified variable-vector transposition `σ = (a_1 b_1)(a_2 b_2)…(a_k b_k)`.
///
/// The vectors `a` and `b` are disjoint, equal-length, and `σ` (swapping the
/// two vectors pointwise) has been **exactly verified** to be an automorphism of
/// the instance: applying it to the constraint multiset reproduces the constraint
/// multiset, and the objective is invariant.
#[derive(Debug, Clone, PartialEq, Eq)]
struct VectorTransposition {
    /// First variable vector (the lex-leader side; `binval(a) >= binval(b)`).
    a: Vec<u32>,
    /// Second variable vector.
    b: Vec<u32>,
}

/// Builds the binary-weighted lex-leader constraint `binval(a) >= binval(b)`,
/// encoded as the single PB constraint
/// `Σ 2^(k-i) a_i - Σ 2^(k-i) b_i >= 0` (MSB first).
///
/// Returns `None` if the vectors are empty, mismatched, or too long for the
/// coefficients to fit `i128`.
///
/// # Soundness
///
/// `binval(a) = Σ 2^(k-i) a_i` is the integer with binary digits `a_1…a_k`
/// (most-significant first), and likewise for `b`. Hence `binval(a) >= binval(b)`
/// holds iff the vector `a` is lexicographically greater than or equal to `b`.
/// For *any* assignment, either `binval(a) >= binval(b)` or `binval(b) >
/// binval(a)`; applying the verified automorphism `σ` (which swaps `a` and `b`)
/// turns a violating assignment into a satisfying one with identical objective
/// value. Therefore every orbit retains a representative satisfying the
/// constraint, so satisfiability and the optimum are preserved. (Standard
/// lex-leader symmetry breaking; the single-constraint binary encoding is exact
/// because the weights are a strictly decreasing power-of-two sequence whose
/// suffix sum is always less than the next higher weight.)
fn binary_lex_leader_constraint(a: &[u32], b: &[u32]) -> Option<PbConstraint> {
    let k = a.len();
    if k == 0 || k != b.len() || k > MAX_LEX_VECTOR_LEN {
        return None;
    }
    let mut terms = Vec::with_capacity(2 * k);
    for (i, (&av, &bv)) in a.iter().zip(b.iter()).enumerate() {
        // i = 0 is the most-significant coordinate: weight 2^(k-1).
        let shift = u32::try_from(k - 1 - i).ok()?;
        let weight = 1i128.checked_shl(shift)?;
        terms.push(PbTerm {
            coeff: weight,
            lits: vec![PbLit {
                var: av,
                negated: false,
            }],
        });
        terms.push(PbTerm {
            coeff: weight.checked_neg()?,
            lits: vec![PbLit {
                var: bv,
                negated: false,
            }],
        });
    }
    Some(PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs: 0,
    })
}

/// Builds the lex-leader constraint `x >=_lex σ(x)` for an ARBITRARY verified
/// automorphism `σ` (a general permutation, 1-indexed `var -> var`), as the
/// single binary-weighted PB constraint
///
/// ```text
/// Σ_i 2^(k-i) · (x_{v_i} − x_{σ(v_i)})  >=  0
/// ```
///
/// over the ordered moved support `S = [v_1 < v_2 < … < v_k]` (variables with
/// `σ(v) ≠ v`). Coefficients accumulate per variable (a variable may be both some
/// `v_i` and some `σ(v_j)`), and zero coefficients are dropped.
///
/// # Soundness
///
/// `binval(x) = Σ_i 2^(k-i) x_{v_i}` reads the support as a binary number
/// (MSB first); the constraint asserts `binval(x) >= binval(σ(x))`, i.e.
/// `x >=_lex σ(x)`. For the lexicographically largest representative `x*` of each
/// orbit under the group generated by the verified automorphisms, `x* >=_lex
/// σ(x*)` holds for every generator `σ`, so `x*` survives. Hence the augmented
/// instance is equisatisfiable with the original and has the same optimum
/// (objective invariant on each orbit, since every emitted `σ` passed the
/// objective-invariance check in `is_automorphism`). This is the standard
/// lex-leader argument for a generating set; restricting `S` to a length-`k`
/// PREFIX of the full support is still SOUND (the lex-min still satisfies the
/// prefix comparison) — only weaker. We bail (return `None`) when the prefix
/// would need weights beyond `i128`.
fn permutation_lex_leader_constraint(perm: &BTreeMap<u32, u32>) -> Option<PbConstraint> {
    // Ordered moved support.
    let mut support: Vec<u32> = perm
        .iter()
        .filter(|&(v, sv)| v != sv)
        .map(|(&v, _)| v)
        .collect();
    support.sort_unstable();
    if support.is_empty() {
        return None;
    }
    // Prefix-cap to keep 2^(k-1) inside i128.
    if support.len() > MAX_LEX_VECTOR_LEN {
        support.truncate(MAX_LEX_VECTOR_LEN);
    }
    let k = support.len();

    let mut coeff: BTreeMap<u32, i128> = BTreeMap::new();
    for (i, &v) in support.iter().enumerate() {
        let shift = u32::try_from(k - 1 - i).ok()?;
        let weight = 1i128.checked_shl(shift)?;
        let sv = *perm.get(&v).unwrap_or(&v);
        // KEEP-MAX convention `binval(x) >= binval(sigma(x))`: +weight on x_v, -weight on
        // x_{sigma(v)}. This MUST agree with the always-on single-variable chains
        // (`lex_ge_constraint`, x_hi >= x_lo) and the legacy `binary_lex_leader_constraint`,
        // which are both keep-max. The previous keep-MIN form (`binval(sigma(x)) >= binval(x)`)
        // clashed with a single-variable chain on a shared interchangeable pair: keep-max
        // forbids (x_a=0,x_b=1) while keep-min forbids (x_a=1,x_b=0), so together they force
        // x_a == x_b and DELETE the whole orbit -- UNSAT on a SAT instance, a false UNSAT the
        // model-only Verified Incumbent Gate cannot catch (C3-1).
        *coeff.entry(v).or_insert(0) = coeff.get(&v).copied().unwrap_or(0).checked_add(weight)?;
        *coeff.entry(sv).or_insert(0) = coeff.get(&sv).copied().unwrap_or(0).checked_sub(weight)?;
    }

    let mut terms: Vec<PbTerm> = coeff
        .into_iter()
        .filter(|&(_, c)| c != 0)
        .map(|(var, c)| PbTerm {
            coeff: c,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        })
        .collect();
    if terms.is_empty() {
        return None;
    }
    terms.sort_by_key(|t| t.lits[0].var);
    Some(PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs: 0,
    })
}

/// Detects maximal groups of mutually interchangeable variables.
///
/// Each returned group is sorted ascending by variable index and has length at
/// least two. Groups are formed by bucketing variables with identical column
/// signatures: signature equality is exactly the condition under which every
/// pairwise transposition within the bucket is an automorphism.
#[must_use]
pub fn detect_interchangeable_groups(instance: &PbInstance) -> Vec<Vec<u32>> {
    let num_vars = instance.num_vars as usize;
    if !(2..=MAX_VARS_FOR_DETECTION).contains(&num_vars) {
        return Vec::new();
    }

    // Build per-variable signatures. Index 0 corresponds to variable 1.
    let mut outcomes: Vec<SignatureOutcome> = (0..num_vars)
        .map(|_| {
            SignatureOutcome::Linear(ColumnSignature {
                rows: Vec::new(),
                objective: None,
            })
        })
        .collect();

    // Accumulate constraint occurrences.
    for (ci, constraint) in instance.constraints.iter().enumerate() {
        accumulate_terms(&constraint.terms, &mut outcomes, |sig, coeff, negated| {
            sig.rows.push((ci, coeff, negated));
        });
    }

    // Accumulate objective occurrences.
    if let Some(objective) = &instance.objective {
        accumulate_objective(objective, &mut outcomes);
    }

    // Bucket linear, present variables by signature. We finalize each signature
    // (sort its rows) before bucketing so equality is order-independent.
    let mut buckets: BTreeMap<ColumnSignature, Vec<u32>> = BTreeMap::new();
    for (idx, outcome) in outcomes.into_iter().enumerate() {
        let var = u32::try_from(idx + 1).unwrap_or(u32::MAX);
        let SignatureOutcome::Linear(mut sig) = outcome else {
            continue;
        };
        if sig.rows.is_empty() && sig.objective.is_none() {
            // Absent variable: occurs nowhere. Skip.
            continue;
        }
        sig.rows.sort_unstable();
        buckets.entry(sig).or_default().push(var);
    }

    let mut groups: Vec<Vec<u32>> = buckets
        .into_values()
        .filter(|g| g.len() >= 2)
        .map(|mut g| {
            g.sort_unstable();
            g
        })
        .collect();
    // Deterministic output ordering: by smallest member.
    groups.sort_unstable_by_key(|g| g.first().copied().unwrap_or(u32::MAX));
    groups
}

/// Folds a constraint's terms into per-variable signatures, marking variables
/// that violate the linear/single-occurrence preconditions as excluded.
fn accumulate_terms<F>(terms: &[PbTerm], outcomes: &mut [SignatureOutcome], mut record: F)
where
    F: FnMut(&mut ColumnSignature, i128, bool),
{
    // Track which variables we have already seen *in this constraint* so a
    // repeated occurrence in the same row excludes the variable.
    let mut seen_this_row: BTreeMap<u32, bool> = BTreeMap::new();

    for term in terms {
        if term.lits.len() != 1 {
            // Non-linear (product) term: exclude every variable it mentions.
            for lit in &term.lits {
                exclude_var(outcomes, lit.var);
            }
            continue;
        }
        let lit = term.lits[0];
        let Some(slot) = var_slot(outcomes, lit.var) else {
            continue;
        };
        if seen_this_row.insert(lit.var, true).is_some() {
            // Variable appears more than once in this constraint: ambiguous.
            *slot = SignatureOutcome::Excluded;
            continue;
        }
        if let SignatureOutcome::Linear(sig) = slot {
            record(sig, term.coeff, lit.negated);
        }
    }
}

/// Folds the objective's terms into per-variable signatures.
fn accumulate_objective(objective: &PbObjective, outcomes: &mut [SignatureOutcome]) {
    let mut seen: BTreeMap<u32, bool> = BTreeMap::new();
    for term in &objective.terms {
        if term.lits.len() != 1 {
            for lit in &term.lits {
                exclude_var(outcomes, lit.var);
            }
            continue;
        }
        let lit = term.lits[0];
        let Some(slot) = var_slot(outcomes, lit.var) else {
            continue;
        };
        if seen.insert(lit.var, true).is_some() {
            *slot = SignatureOutcome::Excluded;
            continue;
        }
        if let SignatureOutcome::Linear(sig) = slot {
            sig.objective = Some((term.coeff, lit.negated));
        }
    }
}

/// Returns a mutable reference to the signature slot for a 1-indexed variable,
/// or `None` if the variable index is out of the declared range.
fn var_slot(outcomes: &mut [SignatureOutcome], var: u32) -> Option<&mut SignatureOutcome> {
    let idx = (var as usize).checked_sub(1)?;
    outcomes.get_mut(idx)
}

/// Marks a 1-indexed variable as excluded from symmetry detection.
fn exclude_var(outcomes: &mut [SignatureOutcome], var: u32) {
    if let Some(slot) = var_slot(outcomes, var) {
        *slot = SignatureOutcome::Excluded;
    }
}

// ---------------------------------------------------------------------------
// Verified variable-vector transposition (matrix / row & column) symmetry.
// ---------------------------------------------------------------------------

/// A constraint reduced to a canonical, hashable, permutation-comparable form.
///
/// Linear constraints only: a sorted list of `(var, coeff, negated)` plus
/// `(rel, rhs)`. Non-linear constraints are represented as `None` and disable
/// generator detection entirely (the candidate machinery only reasons about
/// single-literal terms).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct CanonicalConstraint {
    /// `(var, coeff, negated)` sorted by var ascending.
    terms: Vec<(u32, i128, bool)>,
    rel: PbRel,
    rhs: i128,
}

/// A constraint's *shape*: the sorted multiset of `(coeff, negated)` plus
/// `(rel, rhs)`, with variable identities erased. Two constraints can only map
/// to one another under an automorphism if they share a shape.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ConstraintShape {
    coeffs: Vec<(i128, bool)>,
    rel: PbRel,
    rhs: i128,
}

/// Attempts to canonicalize a single linear constraint. Returns `None` if any
/// term is non-linear or a variable repeats within the row.
fn canonicalize_constraint(constraint: &PbConstraint) -> Option<CanonicalConstraint> {
    let mut terms = Vec::with_capacity(constraint.terms.len());
    for term in &constraint.terms {
        if term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        terms.push((lit.var, term.coeff, lit.negated));
    }
    terms.sort_unstable();
    // Reject repeated variables within the row (ambiguous under permutation).
    if terms.windows(2).any(|w| w[0].0 == w[1].0) {
        return None;
    }
    Some(CanonicalConstraint {
        terms,
        rel: constraint.rel,
        rhs: constraint.rhs,
    })
}

impl CanonicalConstraint {
    fn shape(&self) -> ConstraintShape {
        let mut coeffs: Vec<(i128, bool)> = self.terms.iter().map(|&(_, c, n)| (c, n)).collect();
        coeffs.sort_unstable();
        ConstraintShape {
            coeffs,
            rel: self.rel,
            rhs: self.rhs,
        }
    }

    /// Applies a variable permutation `perm` (1-indexed `var -> var`) and returns
    /// the resulting canonical constraint.
    fn apply_permutation(&self, perm: &BTreeMap<u32, u32>) -> Self {
        let mut terms: Vec<(u32, i128, bool)> = self
            .terms
            .iter()
            .map(|&(v, c, n)| (perm.get(&v).copied().unwrap_or(v), c, n))
            .collect();
        terms.sort_unstable();
        Self {
            terms,
            rel: self.rel,
            rhs: self.rhs,
        }
    }
}

/// Detects verified variable-vector transposition generators.
///
/// Each returned generator's permutation is an **exactly verified** automorphism
/// of the instance (constraints as a multiset, plus the objective). The search
/// is conservative and bounded; it returns an empty vector whenever anything is
/// unclear (non-linear terms, oversized instances, inconsistent candidate maps).
fn detect_verified_vector_transpositions(instance: &PbInstance) -> Vec<VectorTransposition> {
    let num_constraints = instance.constraints.len();
    if num_constraints == 0 || num_constraints > MAX_CONSTRAINTS_FOR_GENERATOR_SEARCH {
        return Vec::new();
    }

    // Canonicalize all constraints; bail if any is non-linear / ambiguous.
    let mut canon = Vec::with_capacity(num_constraints);
    for c in &instance.constraints {
        match canonicalize_constraint(c) {
            Some(cc) => canon.push(cc),
            None => return Vec::new(),
        }
    }

    // The exact constraint multiset, for automorphism verification.
    let mut constraint_multiset: BTreeMap<CanonicalConstraint, u32> = BTreeMap::new();
    for cc in &canon {
        *constraint_multiset.entry(cc.clone()).or_insert(0) += 1;
    }

    // Objective as a canonical var -> (coeff, negated) map, for invariance checks.
    let objective_map = canonical_objective(instance.objective.as_ref());
    // If the objective is non-linear/ambiguous, refuse (None signals "unknown").
    let Some(objective_map) = objective_map else {
        return Vec::new();
    };

    // Bucket constraints by shape; only same-shape constraints can be swapped.
    let mut by_shape: BTreeMap<ConstraintShape, Vec<usize>> = BTreeMap::new();
    for (idx, cc) in canon.iter().enumerate() {
        by_shape.entry(cc.shape()).or_default().push(idx);
    }

    let mut generators: Vec<VectorTransposition> = Vec::new();
    let mut used_vars: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();

    // For each pair of same-shape constraints, derive the candidate variable
    // bijection between them, symmetrize it into an involution, and verify.
    'outer: for indices in by_shape.values() {
        for i in 0..indices.len() {
            for j in (i + 1)..indices.len() {
                if generators.len() >= MAX_GENERATORS {
                    break 'outer;
                }
                let ci = &canon[indices[i]];
                let cj = &canon[indices[j]];
                let Some(involution) = candidate_involution(ci, cj) else {
                    continue;
                };
                // Skip if it touches variables already committed to a generator
                // (keep generators on disjoint supports so the emitted lex
                // constraints do not interact in surprising ways).
                if involution.keys().any(|v| used_vars.contains(v)) {
                    continue;
                }
                if !is_automorphism(&canon, &constraint_multiset, &objective_map, &involution) {
                    continue;
                }
                let Some(transposition) = involution_to_vectors(&involution) else {
                    continue;
                };
                for v in involution.keys() {
                    used_vars.insert(*v);
                }
                generators.push(transposition);
            }
        }
    }

    generators
}

/// Builds the objective as a canonical `var -> (coeff, negated)` map, or `None`
/// if the objective is non-linear or has a repeated variable.
fn canonical_objective(objective: Option<&PbObjective>) -> Option<BTreeMap<u32, (i128, bool)>> {
    let mut map = BTreeMap::new();
    let Some(objective) = objective else {
        return Some(map);
    };
    for term in &objective.terms {
        if term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if map.insert(lit.var, (term.coeff, lit.negated)).is_some() {
            return None;
        }
    }
    Some(map)
}

/// Given two same-shape canonical constraints, derives the unique variable
/// bijection mapping one to the other (matching terms by `(coeff, negated)` in
/// canonical order), then symmetrizes it into an involution.
///
/// Returns `None` when the bijection is not well-defined (ambiguous matching),
/// is the identity, or does not symmetrize consistently into an involution.
fn candidate_involution(
    a: &CanonicalConstraint,
    b: &CanonicalConstraint,
) -> Option<BTreeMap<u32, u32>> {
    if a.terms.len() != b.terms.len() {
        return None;
    }
    // Group a-terms and b-terms by (coeff, negated). For an unambiguous bijection
    // each group must have exactly one member on both sides.
    let mut map: BTreeMap<u32, u32> = BTreeMap::new();
    let mut a_groups: BTreeMap<(i128, bool), Vec<u32>> = BTreeMap::new();
    let mut b_groups: BTreeMap<(i128, bool), Vec<u32>> = BTreeMap::new();
    for &(v, c, n) in &a.terms {
        a_groups.entry((c, n)).or_default().push(v);
    }
    for &(v, c, n) in &b.terms {
        b_groups.entry((c, n)).or_default().push(v);
    }
    if a_groups.len() != b_groups.len() {
        return None;
    }
    for (key, avs) in &a_groups {
        let bvs = b_groups.get(key)?;
        // Only accept unambiguous singleton groups; multi-member groups within a
        // single constraint make the row->row bijection non-unique, so we skip
        // (the column detector and other constraint pairs may still cover them).
        if avs.len() != 1 || bvs.len() != 1 {
            return None;
        }
        map.insert(avs[0], bvs[0]);
    }

    // Symmetrize into an involution: for every a->b we also need b->a. Build the
    // closure and verify it is a consistent involution (σ(σ(x)) == x for all x in
    // the support, and σ(x) != x for at least one x).
    let mut involution: BTreeMap<u32, u32> = BTreeMap::new();
    for (&from, &to) in &map {
        if let Some(prev) = involution.insert(from, to) {
            if prev != to {
                return None;
            }
        }
        if let Some(prev) = involution.insert(to, from) {
            if prev != from {
                return None;
            }
        }
    }
    // Validate involution property and non-triviality.
    let mut nontrivial = false;
    for (&x, &sx) in &involution {
        match involution.get(&sx) {
            Some(&ssx) if ssx == x => {}
            _ => return None,
        }
        if sx != x {
            nontrivial = true;
        }
    }
    if !nontrivial {
        return None;
    }
    Some(involution)
}

/// Exactly verifies that the permutation `perm` is an automorphism of the
/// instance: applying it to every constraint reproduces the constraint
/// multiset, and the objective is invariant.
fn is_automorphism(
    canon: &[CanonicalConstraint],
    multiset: &BTreeMap<CanonicalConstraint, u32>,
    objective: &BTreeMap<u32, (i128, bool)>,
    perm: &BTreeMap<u32, u32>,
) -> bool {
    // Constraint-set invariance: the image multiset must equal the original.
    let mut image: BTreeMap<CanonicalConstraint, u32> = BTreeMap::new();
    for cc in canon {
        *image.entry(cc.apply_permutation(perm)).or_insert(0) += 1;
    }
    if &image != multiset {
        return false;
    }

    // Objective invariance: every variable's objective term must be unchanged by
    // the permutation. Since perm is an involution restricted to its support,
    // it suffices to check that for each (x, σx) pair the objective coefficient
    // and polarity agree. A variable absent from the objective has implicit
    // coefficient 0; its image must also be absent (or zero) for invariance.
    for (&x, &sx) in perm {
        let ox = objective.get(&x).copied();
        let osx = objective.get(&sx).copied();
        if ox != osx {
            return false;
        }
    }
    true
}

/// Converts a verified involution into the two parallel variable vectors
/// `(a, b)` with `a_t < b_t` per transposition and the transpositions ordered by
/// `a_t` ascending. Returns `None` if the support is empty.
fn involution_to_vectors(involution: &BTreeMap<u32, u32>) -> Option<VectorTransposition> {
    let mut pairs: Vec<(u32, u32)> = Vec::new();
    let mut seen: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    for (&x, &sx) in involution {
        if x == sx || seen.contains(&x) {
            continue;
        }
        let (lo, hi) = if x < sx { (x, sx) } else { (sx, x) };
        seen.insert(lo);
        seen.insert(hi);
        pairs.push((lo, hi));
    }
    if pairs.is_empty() {
        return None;
    }
    pairs.sort_unstable();
    let a = pairs.iter().map(|&(lo, _)| lo).collect();
    let b = pairs.iter().map(|&(_, hi)| hi).collect();
    Some(VectorTransposition { a, b })
}

// ===========================================================================
// Scalable graph-automorphism candidate-generator detection.
//
// The pairwise generator search above is O(rows^2) and is capped (it is skipped
// on large, highly-symmetric instances such as the "mat" matrix family, which
// have 35k-408k constraints). The functions below provide a SCALABLE detector
// based on colour refinement (1-dimensional Weisfeiler-Leman / equitable
// partition) plus a synchronised INDIVIDUALISE-REFINE step (the core of nauty /
// saucy) that constructs full large-support candidate generators. Every
// candidate is still passed through the exact `is_automorphism` oracle before
// any constraint is emitted, so the feature is SOUND BY CONSTRUCTION: a buggy or
// incomplete detector can only ever MISS a symmetry, never invent an unsound one.
//
// Pipeline:
//   1. Canonicalise all constraints (reuse `canonicalize_constraint`). Bail on
//      any non-linear / ambiguous row.
//   2. Build a dense bipartite variable<->constraint incidence with per-incidence
//      labels `(coeff, negated)` and an initial colouring (constraint = shape,
//      variable = objective + label multiset).
//   3. Run colour refinement to a stable equitable partition (1-WL): this yields
//      variable colour classes; two variables can only be related by an
//      automorphism when they share a final colour.
//   4. For a class anchor `a` and partners `b` in the same class: refine TWO
//      copies of the colouring, one with `a` individualised and one with `b`
//      individualised (same marker). If both refine to a DISCRETE colouring, the
//      map "`v` in copy-A <-> the var with the same final colour in copy-B" is
//      the unique automorphism sending `a -> b`. Restrict it to its moved
//      support to obtain a candidate generator (a product of transpositions).
//   5. VERIFY each candidate with `is_automorphism`; emit a lex-leader
//      constraint for the survivors (disjoint supports).
// ===========================================================================

/// Only run the scalable detector when the instance has at least this many
/// constraints. Below it the legacy pairwise search already runs.
const SCALABLE_DETECTOR_MIN_CONSTRAINTS: usize = 1;

/// Hard ceiling on instance size (constraints) for the scalable detector. Colour
/// refinement is near-linear, but we still cap total work.
const MAX_CONSTRAINTS_FOR_SCALABLE: usize = 4_000_000;

/// Maximum colour-refinement rounds (refinement is monotone and converges; this
/// is a belt-and-braces cap).
const MAX_REFINEMENT_ROUNDS: usize = 64;

/// Maximum number of scalable generators to emit. The de-risk converted mat16
/// with ~25–49 generators; this leaves headroom while bounding the number of
/// added lex rows (and the front-end work to find them).
const MAX_SCALABLE_GENERATORS: usize = 64;

/// A canonical label for one variable<->constraint incidence: `(coeff, negated)`.
type IncidenceLabel = (i128, bool);

/// Dense per-instance index for the scalable detector. Variables are indexed
/// `0..nvars` (0-indexed; variable id = index + 1). Only variables that occur in
/// at least one constraint are "active"; absent variables keep colour 0 and are
/// never moved.
struct ScalableIndex {
    /// Number of declared variables.
    nvars: usize,
    /// Canonical constraints, parallel to `instance.constraints`.
    canon: Vec<CanonicalConstraint>,
    /// Exact constraint multiset for `is_automorphism`.
    multiset: BTreeMap<CanonicalConstraint, u32>,
    /// Canonical objective map for `is_automorphism`.
    objective: BTreeMap<u32, (i128, bool)>,
    /// For each variable index, the `(constraint index, precomputed label hash)`
    /// incidences. The label hash folds `(coeff, negated)` once at build time so
    /// the hot refinement loop combines it with a single `mix64`.
    var_incidence: Vec<Vec<(usize, u64)>>,
    /// For each constraint, the `(variable index, precomputed label hash)`
    /// incidences.
    cons_incidence: Vec<Vec<(usize, u64)>>,
    /// Stable refined colour per variable index. Colours are 64-bit hashes of the
    /// 1-WL refinement history, so equal colour == equal history and colours are
    /// directly COMPARABLE across the two refinement copies used in
    /// individualise-refine (a property the dense renumbering would not preserve).
    base_var_color: Vec<u64>,
    /// Stable refined colour per constraint index (same encoding).
    base_cons_color: Vec<u64>,
}

/// Builds the dense scalable index and the base equitable colouring, or returns
/// `None` if the instance is non-linear / out of range.
fn build_scalable_index(instance: &PbInstance) -> Option<ScalableIndex> {
    let num_constraints = instance.constraints.len();
    if !(SCALABLE_DETECTOR_MIN_CONSTRAINTS..=MAX_CONSTRAINTS_FOR_SCALABLE)
        .contains(&num_constraints)
    {
        return None;
    }
    let nvars = instance.num_vars as usize;
    if nvars == 0 {
        return None;
    }

    let mut canon = Vec::with_capacity(num_constraints);
    for c in &instance.constraints {
        canon.push(canonicalize_constraint(c)?);
    }

    let mut multiset: BTreeMap<CanonicalConstraint, u32> = BTreeMap::new();
    for cc in &canon {
        *multiset.entry(cc.clone()).or_insert(0) += 1;
    }

    let objective = canonical_objective(instance.objective.as_ref())?;

    // Incidence (both directions). Variable ids are 1-indexed in `terms`; we map
    // to 0-indexed slots. A term referencing a var beyond `nvars` is rejected.
    // Each incidence stores a PRECOMPUTED label hash so the hot loop is one mix.
    let mut var_incidence: Vec<Vec<(usize, u64)>> = vec![Vec::new(); nvars];
    let mut cons_incidence: Vec<Vec<(usize, u64)>> = Vec::with_capacity(num_constraints);
    for (ci, cc) in canon.iter().enumerate() {
        let mut row: Vec<(usize, u64)> = Vec::with_capacity(cc.terms.len());
        for &(v, coeff, negated) in &cc.terms {
            let vi = (v as usize).checked_sub(1)?;
            if vi >= nvars {
                return None;
            }
            let lh = label_hash((coeff, negated));
            var_incidence[vi].push((ci, lh));
            row.push((vi, lh));
        }
        cons_incidence.push(row);
    }

    // Initial colours.
    let mut base_var_color = initial_var_colors(nvars, &var_incidence, &objective);
    let mut base_cons_color = initial_cons_colors(&canon);
    refine(
        &mut base_var_color,
        &mut base_cons_color,
        &var_incidence,
        &cons_incidence,
    );

    if std::env::var_os("AY_PB_SYM_DEBUG").is_some() {
        let nv = distinct_count(&base_var_color);
        let nc = distinct_count(&base_cons_color);
        let mut sizes: BTreeMap<u64, usize> = BTreeMap::new();
        for &c in &base_var_color {
            *sizes.entry(c).or_insert(0) += 1;
        }
        let mut sz: Vec<usize> = sizes.values().copied().collect();
        sz.sort_unstable();
        eprintln!(
            "[sym-debug] base colours: var-classes={nv} cons-classes={nc} \
             var-class-sizes min={:?} max={:?}",
            sz.first(),
            sz.last()
        );
    }

    Some(ScalableIndex {
        nvars,
        canon,
        multiset,
        objective,
        var_incidence,
        cons_incidence,
        base_var_color,
        base_cons_color,
    })
}

/// Initial variable colours: objective term `(coeff, negated)` (or sentinel) plus
/// the sorted multiset of incidence label hashes, as a 64-bit colour hash.
fn initial_var_colors(
    nvars: usize,
    var_incidence: &[Vec<(usize, u64)>],
    objective: &BTreeMap<u32, (i128, bool)>,
) -> Vec<u64> {
    let mut colors: Vec<u64> = Vec::with_capacity(nvars);
    for (vi, incid) in var_incidence.iter().enumerate() {
        let mut labels: Vec<u64> = incid.iter().map(|&(_, l)| l).collect();
        labels.sort_unstable();
        let obj = objective.get(&((vi as u32) + 1)).copied();
        // Absent variables (no incidences, no objective) all collapse to one
        // colour and are never seeds (we only seed from occurring variables).
        colors.push(hash64(&(0x7Au8, obj, &labels)));
    }
    colors
}

/// Initial constraint colours from the [`ConstraintShape`], as 64-bit hashes.
fn initial_cons_colors(canon: &[CanonicalConstraint]) -> Vec<u64> {
    canon
        .iter()
        .map(|cc| {
            let shape = cc.shape();
            hash64(&(0xC0u8, &shape.coeffs, shape.rel, shape.rhs))
        })
        .collect()
}

fn distinct_count(colors: &[u64]) -> usize {
    colors
        .iter()
        .copied()
        .collect::<std::collections::HashSet<_>>()
        .len()
}

/// A small, dependency-free 64-bit hash of any `Hash` value. Collisions only ever
/// cause the detector to MISS a colour split (treat two genuinely-different
/// colours as equal), which is sound — every resulting candidate is exactly
/// verified by `is_automorphism`.
fn hash64<T: std::hash::Hash>(value: &T) -> u64 {
    use std::hash::Hasher;
    let mut h = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut h);
    h.finish()
}

/// A fast finalising mix of a 64-bit value (SplitMix64 finaliser). Used as a
/// cheap, well-distributed scramble for colour combination in the hot refinement
/// loop (much faster than `DefaultHasher`/SipHash). Soundness is unaffected:
/// collisions only ever merge colour classes, which can only cause a missed
/// symmetry, never an unsound one.
#[inline]
fn mix64(mut x: u64) -> u64 {
    x ^= x >> 30;
    x = x.wrapping_mul(0xbf58476d1ce4e5b9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94d049bb133111eb);
    x ^ (x >> 31)
}

/// Precomputes the 64-bit hash of an incidence label `(coeff, negated)`, folded
/// once at index-build time so the hot refinement loop is a single `mix64`.
#[inline]
fn label_hash(label: IncidenceLabel) -> u64 {
    let (coeff, negated) = label;
    mix64((coeff as u64).wrapping_mul(0x9e3779b97f4a7c15) ^ (negated as u64).wrapping_shl(1))
}

/// Combines a PRECOMPUTED label hash and a neighbour colour into a scrambled
/// per-incidence value (one `mix64`).
#[inline]
fn incidence_hash(label_hash: u64, neighbour_color: u64) -> u64 {
    mix64(label_hash ^ neighbour_color.rotate_left(17))
}

/// Refines `var_color` / `cons_color` in place to a stable equitable partition
/// (1-WL). Each round recolours each node by `mix(old colour, Σ over neighbours
/// of incidence_hash(label hash, neighbour colour))` — an ORDER-INDEPENDENT
/// multiset hash (sum of scrambled per-incidence values), so no per-node
/// sort/allocation is needed. Colours are 64-bit refinement-history hashes: equal
/// colour == equal history, so colours are comparable across independent copies
/// of the same base graph (required for synchronised individualise-refine). Stops
/// when neither side gains classes.
fn refine(
    var_color: &mut [u64],
    cons_color: &mut [u64],
    var_incidence: &[Vec<(usize, u64)>],
    cons_incidence: &[Vec<(usize, u64)>],
) {
    let mut new_cons: Vec<u64> = vec![0; cons_color.len()];
    let mut new_var: Vec<u64> = vec![0; var_color.len()];
    let mut old_cons_distinct = distinct_count(cons_color);
    let mut old_var_distinct = distinct_count(var_color);
    for _ in 0..MAX_REFINEMENT_ROUNDS {
        // Recolour constraints from neighbour-variable colours (multiset sum).
        for (ci, row) in cons_incidence.iter().enumerate() {
            let mut acc = 0u64;
            for &(vi, label) in row {
                acc = acc.wrapping_add(incidence_hash(label, var_color[vi]));
            }
            new_cons[ci] = mix64(cons_color[ci].rotate_left(7) ^ acc);
        }

        // Recolour variables from the new constraint colours (multiset sum).
        for (vi, incid) in var_incidence.iter().enumerate() {
            let mut acc = 0u64;
            for &(ci, label) in incid {
                acc = acc.wrapping_add(incidence_hash(label, new_cons[ci]));
            }
            new_var[vi] = mix64(var_color[vi].rotate_left(7) ^ acc);
        }

        let new_cons_distinct = distinct_count(&new_cons);
        let new_var_distinct = distinct_count(&new_var);
        let stable = new_cons_distinct == old_cons_distinct && new_var_distinct == old_var_distinct;
        cons_color.copy_from_slice(&new_cons);
        var_color.copy_from_slice(&new_var);
        old_cons_distinct = new_cons_distinct;
        old_var_distinct = new_var_distinct;
        if stable {
            break;
        }
    }
}

/// A ROUND-SYNCHRONISED, DIRTY-NODE colour refiner used during individualisation.
///
/// It runs ordinary 1-WL (each round's new colour depends on the PREVIOUS round's
/// neighbour colours, so refinement is monotone and always converges), but only
/// recomputes the nodes whose neighbourhood actually changed in the previous
/// round. After individualising a single variable, only a small frontier is dirty
/// each round, so a full re-individualise-to-discreteness costs far less than the
/// O(graph)-per-step dense `refine` — this is what makes the largest "mat"
/// instances tractable. Colours remain 64-bit refinement-history hashes, so
/// equal colour == equal history and colours are comparable across the anchor (A)
/// and partner (B) refiners.
#[derive(Clone)]
struct Refiner<'a> {
    index: &'a ScalableIndex,
    /// Per-variable PIN colour: base colour, or a marker once individualised. A
    /// node's colour is `mix64(pin ^ acc)`; pinning permanently separates a
    /// variable's class, which is exactly individualisation.
    var_pin: Vec<u64>,
    var_color: Vec<u64>,
    cons_color: Vec<u64>,
    /// Generation stamp per node, used for O(1) deduped frontier membership in
    /// `individualize` (avoids per-round sort/dedup of candidate lists).
    var_stamp: Vec<u32>,
    cons_stamp: Vec<u32>,
    stamp: u32,
}

impl<'a> Refiner<'a> {
    fn new(index: &'a ScalableIndex) -> Self {
        Refiner {
            index,
            var_pin: index.base_var_color.clone(),
            var_color: index.base_var_color.clone(),
            cons_color: index.base_cons_color.clone(),
            var_stamp: vec![0; index.nvars],
            cons_stamp: vec![0; index.canon.len()],
            stamp: 0,
        }
    }

    /// Recomputes one constraint's colour from current variable colours.
    #[inline]
    fn recompute_cons(&self, ci: usize) -> u64 {
        let mut acc = 0u64;
        for &(v2, label) in &self.index.cons_incidence[ci] {
            acc = acc.wrapping_add(incidence_hash(label, self.var_color[v2]));
        }
        mix64(self.index.base_cons_color[ci] ^ acc)
    }

    /// Recomputes one variable's colour from current constraint colours and pin.
    #[inline]
    fn recompute_var(&self, vi: usize) -> u64 {
        let mut acc = 0u64;
        for &(ci, label) in &self.index.var_incidence[vi] {
            acc = acc.wrapping_add(incidence_hash(label, self.cons_color[ci]));
        }
        mix64(self.var_pin[vi] ^ acc)
    }

    /// Individualises variable `vi` to `marker`, then runs DIRTY-FRONTIER 1-WL to
    /// a fixpoint, but FALLS BACK to a dense full-graph pass whenever the frontier
    /// grows large. Half-round structure (constraints read current variable
    /// colours, then variables read the just-updated constraint colours) keeps the
    /// recomputation well-defined and monotone (a pinned vertex never re-merges).
    ///
    /// The hybrid is what makes deep individualisation fast on the largest "mat"
    /// instances: the FIRST (anchor) split propagates to much of the graph and is
    /// handled by the cache-friendly dense pass; the many SUBSEQUENT splits of an
    /// already-refined partition touch only a small frontier and are handled
    /// sparsely (deduped in O(1) via a generation stamp). Either way the result is
    /// the same fixpoint (and every downstream candidate is exactly verified).
    fn individualize(&mut self, vi: usize, marker: u64) {
        self.var_pin[vi] = marker;
        let nc = self.recompute_var(vi);
        if nc == self.var_color[vi] {
            return;
        }
        self.var_color[vi] = nc;
        // Only fall back to a dense full-graph pass when the frontier is a LARGE
        // fraction of the variables; for moderate frontiers the sparse
        // dirty-frontier (O(frontier·degree) per round) is much cheaper than a
        // dense O(constraints) pass, especially on instances with far more
        // constraints than variables (mat16: 408k constraints, 5.5k vars).
        let dense_threshold = (self.index.nvars * 3 / 4).max(64);
        let mut frontier_vars: Vec<usize> = vec![vi];
        let mut next_cons: Vec<usize> = Vec::new();
        let mut next_vars: Vec<usize> = Vec::new();

        for _ in 0..MAX_REFINEMENT_ROUNDS {
            if frontier_vars.is_empty() {
                break;
            }
            if frontier_vars.len() > dense_threshold {
                self.dense_to_fixpoint();
                return;
            }
            // Collect constraints incident to changed variables (deduped).
            self.stamp = self.stamp.wrapping_add(1);
            let s = self.stamp;
            next_cons.clear();
            for &v in &frontier_vars {
                for &(ci, _) in &self.index.var_incidence[v] {
                    if self.cons_stamp[ci] != s {
                        self.cons_stamp[ci] = s;
                        next_cons.push(ci);
                    }
                }
            }
            let mut changed_cons: Vec<usize> = Vec::new();
            for &ci in &next_cons {
                let v = self.recompute_cons(ci);
                if v != self.cons_color[ci] {
                    self.cons_color[ci] = v;
                    changed_cons.push(ci);
                }
            }
            if changed_cons.is_empty() {
                break;
            }
            // Collect variables incident to changed constraints (deduped).
            self.stamp = self.stamp.wrapping_add(1);
            let s = self.stamp;
            next_vars.clear();
            for &ci in &changed_cons {
                for &(v2, _) in &self.index.cons_incidence[ci] {
                    if self.var_stamp[v2] != s {
                        self.var_stamp[v2] = s;
                        next_vars.push(v2);
                    }
                }
            }
            frontier_vars.clear();
            for &v2 in &next_vars {
                let v = self.recompute_var(v2);
                if v != self.var_color[v2] {
                    self.var_color[v2] = v;
                    frontier_vars.push(v2);
                }
            }
        }
    }

    /// Dense round-synchronised WL to a fixpoint over the WHOLE graph.
    ///
    /// Convergence is by PARTITION stability (the number of distinct colours stops
    /// growing), NOT by value equality: the colour update folds in the node's own
    /// previous colour, so values keep changing every round even after the induced
    /// equivalence partition is stable — checking value equality would loop to the
    /// round cap (~10× slower). The combined distinct-colour count is monotone
    /// non-decreasing and bounded, so this always terminates.
    fn dense_to_fixpoint(&mut self) {
        let mut new_cons = vec![0u64; self.cons_color.len()];
        let mut new_var = vec![0u64; self.var_color.len()];
        let mut prev_distinct = self.combined_distinct();
        for _ in 0..MAX_REFINEMENT_ROUNDS {
            for ci in 0..self.cons_color.len() {
                new_cons[ci] = self.recompute_cons(ci);
            }
            self.cons_color.copy_from_slice(&new_cons);
            for v in 0..self.var_color.len() {
                new_var[v] = self.recompute_var(v);
            }
            self.var_color.copy_from_slice(&new_var);
            let distinct = self.combined_distinct();
            if distinct == prev_distinct {
                break; // partition stable
            }
            prev_distinct = distinct;
        }
    }

    /// Number of distinct colours across variables and constraints combined (the
    /// partition's cell count; tagged so var/cons colours never collide).
    fn combined_distinct(&self) -> usize {
        let mut set: std::collections::HashSet<u64> = std::collections::HashSet::new();
        for &c in &self.var_color {
            set.insert(c ^ 0x5555_5555_5555_5555);
        }
        for &c in &self.cons_color {
            set.insert(c);
        }
        set.len()
    }

    /// Returns the active-variable colour classes as `colour -> members`.
    fn var_classes(&self) -> BTreeMap<u64, Vec<usize>> {
        let mut classes: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
        for vi in 0..self.index.nvars {
            if !self.index.var_incidence[vi].is_empty() {
                classes.entry(self.var_color[vi]).or_default().push(vi);
            }
        }
        classes
    }

    /// Finds the smallest non-singleton active-variable cell as `(colour, sorted
    /// members)`, ties broken by colour value (deterministic). `None` if discrete.
    fn smallest_nonsingleton(&self) -> Option<(u64, Vec<usize>)> {
        self.var_classes()
            .into_iter()
            .filter(|(_, m)| m.len() > 1)
            .min_by(|(ca, ma), (cb, mb)| ma.len().cmp(&mb.len()).then(ca.cmp(cb)))
            .map(|(c, mut m)| {
                m.sort_unstable();
                (c, m)
            })
    }
}

/// Finds SMALL-SUPPORT generators (nauty-style automorphisms) by sibling swaps in
/// the individualisation search tree.
///
/// Method: refine to the base partition, then repeatedly individualise the
/// smallest-id member of the smallest non-singleton cell, descending a single
/// path. At each level, the current cell `C` has the smallest-id member `u`
/// already chosen for the descent; for each OTHER member `w` of `C`, the
/// automorphism that swaps `u`'s subtree with `w`'s subtree (fixing everything
/// individualised ABOVE this level) is found by individualising `u` in one copy
/// and `w` in another (both from the SAME parent state, same marker) and refining
/// both to discreteness, then reading off. Because the parent state is identical
/// in both copies, all variables fixed above stay fixed → the resulting
/// automorphism has SMALL support (only `C`'s subtree moves). These minimal-support
/// generators prune far more effectively than full-graph coset maps, matching the
/// clean row/column/symbol swaps a dedicated tool (nauty) would return.
///
/// Every candidate is exactly verified by `is_automorphism` before being kept.
fn extract_sibling_generators(
    index: &ScalableIndex,
    generators: &mut Vec<BTreeMap<u32, u32>>,
    seen: &mut std::collections::HashSet<u64>,
    deadline: Option<std::time::Instant>,
    dbg: bool,
) {
    // A single descent path harvests siblings of ONE chain of cells — which on a
    // multi-axis symmetric structure (mat is a 3-D row/column/symbol cube) tends
    // to find generators of only ONE axis (a weak, redundant set, like the
    // de-risk's generators 1–24). To get a DIVERSE generating set spanning the
    // whole group we run SEVERAL descents, each forced to individualise a DIFFERENT
    // first variable (a different element of the first orbit), exploring different
    // parts of the group. A shared `refine_budget` bounds total work.
    let mut budget = SIBLING_REFINE_BUDGET;

    // First descent: canonical (smallest-id) choices.
    harvest_one_descent(index, None, generators, seen, &mut budget, deadline, dbg);

    // Additional descents seeded by individualising different first-cell members.
    // The first cell's members are an orbit; forcing different roots yields
    // generators of different axes.
    let root = Refiner::new(index);
    let first_cell = root
        .smallest_nonsingleton()
        .map(|(_, m)| m)
        .unwrap_or_default();
    for &seed in first_cell.iter().take(MAX_DESCENT_SEEDS) {
        if generators.len() >= MAX_SCALABLE_GENERATORS || budget == 0 {
            break;
        }
        if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
            break;
        }
        harvest_one_descent(
            index,
            Some(seed),
            generators,
            seen,
            &mut budget,
            deadline,
            dbg,
        );
    }
}

/// Runs ONE individualisation descent (optionally forcing the first
/// individualised variable to `forced_root`) and harvests small-support sibling
/// generators along it. Appends verified generators to `generators`.
fn harvest_one_descent(
    index: &ScalableIndex,
    forced_root: Option<usize>,
    generators: &mut Vec<BTreeMap<u32, u32>>,
    seen: &mut std::collections::HashSet<u64>,
    budget: &mut usize,
    deadline: Option<std::time::Instant>,
    dbg: bool,
) {
    // PHASE 1 — descend to discreteness, recording a SNAPSHOT at each level (the
    // refiner state before the split, the cell members, the chosen member, the
    // marker). The descent is ~one refine-to-discreteness; snapshots are cheap.
    let mut snapshots: Vec<LevelSnapshot<'_>> = Vec::new();
    let mut refiner = Refiner::new(index);
    let mut marker_seq: u64 = 0;
    let fresh = |seq: &mut u64| -> u64 {
        *seq += 1;
        hash64(&(0xEEu8, *seq))
    };
    let mut first = true;
    while let Some((_color, members)) = refiner.smallest_nonsingleton() {
        if snapshots.len() >= MAX_INDIVIDUALISE_DEPTH {
            break;
        }
        // Choose the descent member: forced root on the first split (if it is a
        // member of the first cell), else the canonical smallest-id member.
        let u = if first {
            match forced_root {
                Some(r) if members.contains(&r) => r,
                _ => members[0],
            }
        } else {
            members[0]
        };
        first = false;
        let marker = fresh(&mut marker_seq);
        snapshots.push(LevelSnapshot {
            state: refiner.clone(),
            members,
            u,
            marker,
        });
        refiner.individualize(u, marker);
    }

    // PHASE 2 — harvest sibling generators (shallowest harvestable level first).
    // The SMALL-support (clean) generators live at shallow levels: swapping two
    // members of an early moderate cell moves only that cell's local subtree
    // (mat16: support ~306–648), whereas a deep swap forces a large realignment
    // (rejected by the support cap). A and B are BOTH computed from the SAME shared
    // parent snapshot (same deterministic per-step markers) so their colour values
    // are comparable and `read_off_map` aligns them into a permutation.
    for (level, snap) in snapshots.iter().enumerate() {
        if generators.len() >= MAX_SCALABLE_GENERATORS || *budget == 0 {
            return;
        }
        if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
            return;
        }
        // At the FIRST few (shallow) levels harvest from ALL moderate non-singleton
        // cells of the partition, not only the descent cell. On a multi-axis
        // structure (mat is a row × column × symbol cube) the different cells of a
        // shallow partition correspond to the DIFFERENT axes, so this is what
        // produces a CROSS-axis generating set (the strong set) instead of the
        // single-axis adjacent swaps a one-cell descent yields. Deeper levels only
        // harvest the descent cell (cheap incremental coverage).
        let harvest_cells: Vec<(usize, Vec<usize>)> = if level < SHALLOW_MULTI_CELL_LEVELS {
            snap.state
                .var_classes()
                .into_values()
                .filter(|m| m.len() >= 2 && m.len() <= SIBLING_HARVEST_MAX_CELL)
                .map(|mut m| {
                    m.sort_unstable();
                    (m[0], m)
                })
                .collect()
        } else if snap.members.len() <= SIBLING_HARVEST_MAX_CELL {
            vec![(snap.u, snap.members.clone())]
        } else {
            Vec::new()
        };

        for (u, members) in harvest_cells {
            if generators.len() >= MAX_SCALABLE_GENERATORS || *budget == 0 {
                return;
            }
            if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
                return;
            }
            // A side: individualise the cell anchor `u` from the shared parent.
            let mut copy_u = snap.state.clone();
            copy_u.individualize(u, snap.marker);
            let Some(a_var) = refine_to_discrete(&mut copy_u) else {
                *budget = budget.saturating_sub(1);
                continue;
            };
            *budget = budget.saturating_sub(1);

            // Partners SPREAD across the cell so sibling swaps span near AND far
            // elements (the de-risk's strong set mixes adjacent and distant swaps).
            let partners = spread_partners(&members, u, MAX_PARTNERS_PER_ANCHOR);
            for &w in &partners {
                if generators.len() >= MAX_SCALABLE_GENERATORS || *budget == 0 {
                    return;
                }
                if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
                    return;
                }
                let mut copy_w = snap.state.clone();
                copy_w.individualize(w, snap.marker);
                let Some(b_var) = refine_to_discrete(&mut copy_w) else {
                    *budget = budget.saturating_sub(1);
                    continue;
                };
                *budget = budget.saturating_sub(1);
                let Some(perm) = read_off_map(index, &a_var, &b_var, u, w) else {
                    continue;
                };
                let map = perm_to_map(&perm);
                if map.is_empty() || map.len() > SIBLING_SUPPORT_CAP {
                    continue;
                }
                let key = {
                    let pairs: Vec<(u32, u32)> = map.iter().map(|(&k, &v)| (k, v)).collect();
                    hash64(&pairs)
                };
                if !seen.insert(key) {
                    continue;
                }
                if !is_automorphism(&index.canon, &index.multiset, &index.objective, &map) {
                    continue;
                }
                if dbg {
                    eprintln!(
                        "[sym-debug] sibling generator (u={u},w={w}) support {}",
                        map.len()
                    );
                }
                generators.push(map);
            }
        }
    }
}

/// Number of shallow individualisation levels at which sibling generators are
/// harvested from ALL moderate cells (for cross-axis diversity), not just the
/// descent cell.
const SHALLOW_MULTI_CELL_LEVELS: usize = 6;

/// Number of additional descent seeds (different first-cell roots) tried for
/// generator diversity, beyond the canonical descent.
const MAX_DESCENT_SEEDS: usize = 4;

/// Selects up to `k` partners for `u` SPREAD evenly across the sorted cell
/// `members` (excluding `u`), so the resulting sibling swaps mix near and far
/// elements rather than only adjacent ones.
fn spread_partners(members: &[usize], u: usize, k: usize) -> Vec<usize> {
    let others: Vec<usize> = members.iter().copied().filter(|&m| m != u).collect();
    if others.len() <= k {
        return others;
    }
    let mut out = Vec::with_capacity(k);
    for i in 0..k {
        // Evenly spaced indices across `others`.
        let idx = (i * (others.len() - 1)) / (k - 1).max(1);
        out.push(others[idx]);
    }
    out.dedup();
    out
}

/// A recorded individualisation level: the refiner state BEFORE the level's
/// split, the cell members at that level, the chosen descent member `u`, and the
/// marker used. Used to harvest sibling-swap generators deepest-first.
struct LevelSnapshot<'a> {
    state: Refiner<'a>,
    members: Vec<usize>,
    u: usize,
    marker: u64,
}

/// Upper bound on the support (moved-variable count) of a sibling-swap generator
/// we will HARVEST. Sibling swaps at shallow tree levels move huge subtrees and
/// prune poorly (and are expensive); we descend past them and only harvest once
/// the remaining non-singleton count — which bounds the support — is small. The
/// de-risk's effective mat generators had support ~110–650, so this cap keeps the
/// clean, strong ones.
const SIBLING_SUPPORT_CAP: usize = 1400;

/// Budget on the number of discreteness refinements (the relatively expensive
/// per-sibling step) the sibling search may perform. Bounds the front-end time on
/// the largest instances while leaving room to harvest a strong generating set.
const SIBLING_REFINE_BUDGET: usize = 800;

/// Maximum cell size at which we HARVEST sibling generators. Larger cells live
/// near the root and their sibling swaps move huge subtrees (rejected by the
/// support cap and expensive to compute), so we descend past them rather than
/// harvest them. Moderate cells produce the clean small-support generators.
const SIBLING_HARVEST_MAX_CELL: usize = 64;

/// Refines `refiner` to a discrete (all-singleton on the active support)
/// colouring by individualising the smallest non-singleton cell's smallest
/// member repeatedly. Returns the discrete `var_color`, or `None` if discreteness
/// is not reached within the depth budget.
fn refine_to_discrete(refiner: &mut Refiner<'_>) -> Option<Vec<u64>> {
    refine_to_discrete_bounded(refiner, None)
}

/// Like [`refine_to_discrete`] but aborts early (returning `None`) once `deadline`
/// passes, so a single member that does not discretise (a symmetric residual cell
/// that never splits under canonical individualisation) cannot burn a large slice
/// of the detection budget on the largest instances. The deadline is checked every
/// few individualisations to keep the clock reads negligible.
fn refine_to_discrete_bounded(
    refiner: &mut Refiner<'_>,
    deadline: Option<std::time::Instant>,
) -> Option<Vec<u64>> {
    let mut marker_seq: u64 = 1 << 40; // disjoint marker namespace from descent
    for step in 0..MAX_INDIVIDUALISE_DEPTH {
        if step % 8 == 0 && deadline.is_some_and(|d| std::time::Instant::now() >= d) {
            return None;
        }
        match refiner.smallest_nonsingleton() {
            None => return Some(refiner.var_color.clone()),
            Some((_c, members)) => {
                // Stop early at small cells (positional completion in read_off_map).
                if members.len() <= SMALL_CLASS_LIMIT.max(1) {
                    return Some(refiner.var_color.clone());
                }
                marker_seq += 1;
                let m = hash64(&(0xEEu8, marker_seq));
                refiner.individualize(members[0], m);
            }
        }
    }
    None
}

/// Maximum number of sibling partners to harvest at each individualisation level.
/// A few per level keeps the generating set diverse without spending the whole
/// budget on one cell's siblings.
const MAX_PARTNERS_PER_ANCHOR: usize = 8;

/// Largest base-colour variable cell from which the ADJACENT-SIBLING harvest will
/// try to read off generators. The "mat" matrix family puts the whole matrix
/// (n·m cells) into one base-colour class (mat16: 306; mat20: 380), so this must
/// admit those moderate-but-not-tiny cells — far above the descent harvest's
/// `SIBLING_HARVEST_MAX_CELL` (which deliberately skips them). It still excludes
/// the huge auxiliary cell (mat16: 5202) whose adjacent swaps are not generators.
const ADJ_HARVEST_MAX_CELL: usize = 2_048;

/// Index distances (within a sorted base-colour cell) at which an anchor `u` is
/// paired with a partner in the adjacent-sibling harvest. For a row-major matrix
/// orbit, distance `+1` is the adjacent-COLUMN swap and `+row_width` the
/// adjacent-ROW swap; we try a small spread of near distances so BOTH axes' clean
/// adjacent transpositions are captured regardless of the (unknown) row width.
/// These yield the de-risk's fast-converging fine "column/row swap" family.
///
/// Distance `1` is the adjacent-COLUMN swap (the n−1 of these generate the whole
/// column-permutation group). The larger distances are candidate matrix ROW widths
/// — the one matching the true width yields the adjacent-ROW swap; others yield
/// either nothing or a higher-support PRODUCT (filtered by the support cap). We do
/// NOT include intermediate distances such as `2` (a non-adjacent "double" column
/// swap): it is a redundant product already generated by two distance-`1` swaps,
/// and including it would only dilute the early-stop generator count with
/// redundant rows. Covers the koops mat row widths (18, 20, …).
const ADJ_PARTNER_DISTANCES: &[usize] = &[1, 16, 17, 18, 19, 20, 21, 22];

/// Size of the DENSE prefix of cell members the adjacent-sibling harvest always
/// refines. This must span the first matrix ROW (so every column gets an anchor
/// for the adjacent-COLUMN swaps); a couple of rows' worth is generous for the
/// koops mat family (row widths ≤ 20). The per-distance progressions cover the
/// rest of the cell (row swaps) sparsely.
const ADJ_DENSE_PREFIX: usize = 48;

/// Partner distances below this are covered by the dense prefix and are NOT
/// expanded into arithmetic progressions (a small-`d` progression would refine
/// almost the whole cell). Distances at/above it (candidate matrix row widths) get
/// a progression so every ROW gets an anchor for the adjacent-row swaps.
const ADJ_PROGRESSION_MIN_DISTANCE: usize = 8;

/// Per-member wall-clock cap for the discreteness refinement in the adjacent
/// harvest. Most members discretise in well under this; the cap stops a member
/// whose canonical individualisation never splits a symmetric residual cell from
/// consuming the whole detection budget (it is simply skipped — sound).
const ADJ_PER_MEMBER_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(3);

/// Target number of generators to harvest from ONE base-colour cell before
/// stopping its refinement. A chain of (k−1) adjacent transpositions already
/// generates the symmetric group S_k on a k-element axis, so once a cell has
/// yielded this many adjacent swaps its symmetry is (over-)covered; stopping saves
/// the costly refinements of the remaining members. Sized above the koops mat
/// column/row counts (≤ 20) with headroom.
const ADJ_GENS_PER_CELL_TARGET: usize = 24;

/// Upper bound on the support of a CLEAN adjacent-swap generator we keep. These
/// are single-axis row/column swaps whose support grows with the matrix dimension
/// (mat16: 648–1122; mat20: 800–1406; larger matrices proportionally more), so the
/// cap is more generous than the descent harvest's [`SIBLING_SUPPORT_CAP`] — it
/// must admit the genuine adjacent swaps while still excluding double-axis products
/// (which a pair of adjacent swaps already generates). Only a harvest filter; the
/// emitted lex constraint is prefix-capped at [`MAX_LEX_VECTOR_LEN`] regardless.
const ADJ_SUPPORT_CAP: usize = 2_000;

/// Refinement budget (the relatively expensive discreteness refinements) the
/// adjacent-sibling harvest may spend. With caching + the sparse per-distance
/// member selection, the cost is ~`cell/min_distance + cell/row_width` refinements
/// per cell — a few hundred suffices to gather the full row+column adjacent-swap
/// family of the koops mat instances within the detection deadline.
const ADJ_REFINE_BUDGET: usize = 400;

/// Harvests CLEAN, FINE, small-support generators by swapping ADJACENT members of
/// the (large) base-colour variable cells.
///
/// Motivation: the descent harvest [`extract_sibling_generators`] deliberately
/// SKIPS large cells (`SIBLING_HARVEST_MAX_CELL = 64`) and SPREADS its partners,
/// which on the "mat" family yields a few LARGE-support coset maps that do not
/// prune the refutation in time. The de-risk pinned the fast-converging set as the
/// FINE "column-swap" generators (offset-1, support ≈ matrix dim) — i.e. swaps of
/// ADJACENT cells of the matrix orbit. This pass targets exactly those: for each
/// of a few anchors `u` in a moderate base-colour cell, it individualises `u`,
/// refines to discreteness once, then for each consecutive (adjacent) partner `w`
/// it individualises `w`, refines, and reads off the bijection `u ↦ w`. Every
/// candidate is exactly verified by `is_automorphism` before being kept, so the
/// pass is SOUND BY CONSTRUCTION (a wrong adjacency guess is simply rejected).
fn harvest_orbit_adjacent_generators(
    index: &ScalableIndex,
    generators: &mut Vec<BTreeMap<u32, u32>>,
    seen: &mut std::collections::HashSet<u64>,
    deadline: Option<std::time::Instant>,
    dbg: bool,
) {
    // Base-colour cells of moderate size (skip singletons and the huge aux cell).
    let mut cells: Vec<Vec<usize>> = {
        let mut by_color: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
        for vi in 0..index.nvars {
            if !index.var_incidence[vi].is_empty() {
                by_color
                    .entry(index.base_var_color[vi])
                    .or_default()
                    .push(vi);
            }
        }
        by_color
            .into_values()
            .filter(|m| (2..=ADJ_HARVEST_MAX_CELL).contains(&m.len()))
            .collect()
    };
    // Smallest harvestable cells first (cheapest, and on mat these are the matrix
    // orbit whose adjacent swaps are the fine generators).
    cells.sort_by_key(Vec::len);

    // ALL individualisations use ONE shared marker so any two members' discrete
    // colourings are directly comparable in `read_off_map` (the bijection between
    // copy-`u` and copy-`w` is the automorphism sending u→w). This lets us refine
    // each candidate member ONCE (cached) and then read off EVERY adjacent pair
    // from the cache — turning an anchors×distances refinement count into a single
    // pass over the candidate members.
    let shared_marker = hash64(&0xADD1u16);

    let mut budget = ADJ_REFINE_BUDGET;
    for members in &cells {
        if generators.len() >= MAX_SCALABLE_GENERATORS || budget == 0 {
            break;
        }
        let mut sorted = members.clone();
        sorted.sort_unstable();
        let n = sorted.len();

        // Choose the cell-member INDICES to refine. We want every adjacent pair
        // `(i, i+d)` for each partner distance `d` to have BOTH endpoints refined,
        // across the WHOLE cell — so the matrix's adjacent COLUMN swaps (small `d`)
        // and adjacent ROW swaps (`d ≈ row_width`) are all reachable regardless of
        // the (unknown) grid dimensions. Two sparse generators cover this:
        //   • a DENSE prefix `0..P` — gives the first row's adjacent COLUMN swaps
        //     (small `d`) at every column;
        //   • for each LARGE partner distance `d` (a candidate row width), the
        //     arithmetic progression `0, d, 2d, …` — gives the adjacent ROW swap at
        //     every row.
        // Small distances are intentionally NOT expanded into full progressions
        // (`d=1` would be the entire cell); the dense prefix already covers them, so
        // the refined set stays O(P + Σ cell/d) and the harvest fits the deadline.
        let mut want: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
        for i in 0..ADJ_DENSE_PREFIX.min(n) {
            want.insert(i);
        }
        for &d in ADJ_PARTNER_DISTANCES {
            if d < ADJ_PROGRESSION_MIN_DISTANCE {
                continue; // covered by the dense prefix; avoid near-full progressions
            }
            let mut i = 0;
            while i < n {
                want.insert(i);
                i += d;
            }
        }

        // Refine wanted members ONE AT A TIME (smallest index first, so the dense
        // prefix — the adjacent COLUMN swaps — comes first), and read off each new
        // member's adjacent pairs immediately. This lets us STOP EARLY once a cell
        // has yielded enough generators (a full chain of adjacent column swaps
        // already generates the whole column-permutation group), saving the costly
        // refinements of the remaining (row-progression) members on the largest
        // instances. Refinement is the dominant detection cost, so early-stop is the
        // main speed lever for converting the biggest matrices inside the budget.
        let mut discrete: BTreeMap<usize, Vec<u64>> = BTreeMap::new();
        let t_refine = std::time::Instant::now();
        let cell_start_gens = generators.len();
        for &ai in &want {
            if budget == 0 || deadline.is_some_and(|d| std::time::Instant::now() >= d) {
                break;
            }
            // Enough generators from THIS cell? A long chain of adjacent swaps
            // already generates the cell's symmetric group; stop refining it.
            if generators.len() - cell_start_gens >= ADJ_GENS_PER_CELL_TARGET {
                break;
            }
            let mut copy = Refiner::new(index);
            copy.individualize(sorted[ai], shared_marker);
            // Per-member abort: a member that does not discretise quickly is skipped
            // (sound — just no generator from it) so it cannot starve the others.
            let per_member = std::time::Instant::now() + ADJ_PER_MEMBER_TIMEOUT;
            let member_deadline = match deadline {
                Some(d) => Some(d.min(per_member)),
                None => Some(per_member),
            };
            let Some(a_var) = refine_to_discrete_bounded(&mut copy, member_deadline) else {
                budget = budget.saturating_sub(1);
                continue;
            };
            budget = budget.saturating_sub(1);
            discrete.insert(ai, a_var);

            // Read off this member's adjacent pairs against ALREADY-refined members
            // (both directions: ai is the larger or smaller endpoint).
            for &step in ADJ_PARTNER_DISTANCES {
                // (ai, ai+step) and (ai-step, ai): try both so a newly refined member
                // pairs with earlier ones regardless of which side it sits on.
                for (lo, hi) in [(ai, ai + step), (ai.wrapping_sub(step), ai)] {
                    if hi >= n || lo >= n || lo >= hi {
                        continue;
                    }
                    if generators.len() >= MAX_SCALABLE_GENERATORS {
                        return;
                    }
                    let (Some(a_var), Some(b_var)) = (discrete.get(&lo), discrete.get(&hi)) else {
                        continue;
                    };
                    let (u, w) = (sorted[lo], sorted[hi]);
                    let Some(perm) = read_off_map(index, a_var, b_var, u, w) else {
                        if dbg && step <= 2 {
                            eprintln!("[sym-debug] adj read_off FAILED (u={u},w={w},step={step})");
                        }
                        continue;
                    };
                    let map = perm_to_map(&perm);
                    if map.is_empty() || map.len() > ADJ_SUPPORT_CAP {
                        if dbg && step <= 2 {
                            eprintln!(
                                "[sym-debug] adj map dropped size={} (u={u},w={w},step={step})",
                                map.len()
                            );
                        }
                        continue;
                    }
                    let key = {
                        let pairs: Vec<(u32, u32)> = map.iter().map(|(&k, &v)| (k, v)).collect();
                        hash64(&pairs)
                    };
                    if !seen.insert(key) {
                        continue;
                    }
                    if !is_automorphism(&index.canon, &index.multiset, &index.objective, &map) {
                        if dbg && step <= 2 {
                            eprintln!(
                                "[sym-debug] adj NOT-AUTO (u={u},w={w},step={step},size={})",
                                map.len()
                            );
                        }
                        continue;
                    }
                    if dbg {
                        eprintln!(
                            "[sym-debug] adjacent generator (u={u},w={w}) support {}",
                            map.len()
                        );
                    }
                    generators.push(map);
                }
            }
        }
        if dbg {
            eprintln!(
                "[sym-debug] adj-harvest cell size {n}: refined {} members, {} gens, {:.1}s",
                discrete.len(),
                generators.len() - cell_start_gens,
                t_refine.elapsed().as_secs_f64()
            );
        }
    }
}

/// Scalable detection of verified candidate generators via colour refinement +
/// synchronised individualise-refine. Returns general (possibly non-involution)
/// permutations, each EXACTLY VERIFIED by `is_automorphism` before inclusion.
/// Supports may overlap (a generating SET, like the de-risk's 25–49 generators);
/// the emitter adds one sound lex-leader constraint per generator.
fn detect_scalable_generators(
    instance: &PbInstance,
    deadline: Option<std::time::Instant>,
) -> Vec<BTreeMap<u32, u32>> {
    let Some(index) = build_scalable_index(instance) else {
        return Vec::new();
    };
    let dbg = std::env::var_os("AY_PB_SYM_DEBUG").is_some();

    // Candidate orbit classes: variables sharing a base colour, size >= 2.
    let mut classes: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
    for (vi, &c) in index.base_var_color.iter().enumerate() {
        // Only variables that actually occur are useful seeds.
        if !index.var_incidence[vi].is_empty() {
            classes.entry(c).or_default().push(vi);
        }
    }

    let _ = &classes; // class structure is informational; the search uses the tree

    let mut generators: Vec<BTreeMap<u32, u32>> = Vec::new();
    let mut seen: std::collections::HashSet<u64> = std::collections::HashSet::new();

    // PRIMARY strategy: CLEAN, FINE, small-support generators from swapping
    // ADJACENT members of the (large) base-colour matrix orbit. The de-risk pinned
    // this fine "column-swap" family (offset-1, support ≈ matrix dimension) as the
    // fast-converging generating set that proves the hard "mat" refutations in
    // seconds, where the coarse/large-support coset maps below do not. It runs
    // first so these fine generators are gathered (and emitted) within the
    // detection deadline.
    harvest_orbit_adjacent_generators(&index, &mut generators, &mut seen, deadline, dbg);

    if dbg {
        let sizes: Vec<usize> = generators.iter().map(BTreeMap::len).collect();
        eprintln!(
            "[sym-debug] adjacent generators: {} (supports min={:?} max={:?})",
            generators.len(),
            sizes.iter().min(),
            sizes.iter().max()
        );
    }

    // SECONDARY strategy: SMALL-SUPPORT generators from sibling swaps in the
    // individualisation search tree (nauty-style). These complement the adjacent
    // family with cross-axis / coarser generators (clean row/column/symbol swaps).
    extract_sibling_generators(&index, &mut generators, &mut seen, deadline, dbg);

    if dbg {
        let sizes: Vec<usize> = generators.iter().map(BTreeMap::len).collect();
        eprintln!(
            "[sym-debug] sibling generators (cumulative): {} (supports min={:?} max={:?})",
            generators.len(),
            sizes.iter().min(),
            sizes.iter().max()
        );
    }

    generators
}

/// Converts a dense 0-indexed permutation into a 1-indexed `var -> var` map
/// restricted to its moved support (entries where `σ(v) != v`).
fn perm_to_map(perm: &[u32]) -> BTreeMap<u32, u32> {
    let mut map = BTreeMap::new();
    for (vi, &img) in perm.iter().enumerate() {
        if img as usize != vi {
            map.insert((vi as u32) + 1, img + 1);
        }
    }
    map
}

/// Maximum individualisation depth (target-cell refinements) per seed before
/// giving up. Highly symmetric structures need a chain of individualisations to
/// reach a discrete colouring; this bounds that chain.
const MAX_INDIVIDUALISE_DEPTH: usize = 256;

/// Largest residual colour-class size at which `refine_to_discrete` stops
/// individualising and `read_off_map` completes the bijection positionally. The
/// resulting map is a heuristic guess inside small cells but is always exactly
/// verified, so a wrong guess merely costs one (cheap) rejected candidate. Kept
/// at 1 (full discreteness) for the matrix family, where positional completion of
/// larger cells does not yield automorphisms.
const SMALL_CLASS_LIMIT: usize = 1;

/// Reads the variable bijection off two colourings (copy A domain, copy B range)
/// that share colour ids. For each colour, the A-members and B-members must have
/// equal count; SINGLETON colours map directly, and SMALL non-singleton colours
/// (allowed by `SMALL_CLASS_LIMIT`) are paired POSITIONALLY (A-members sorted by
/// id <-> B-members sorted by id). The positional pairing is a heuristic guess,
/// but the result is exactly verified by `is_automorphism`, so a wrong guess is
/// simply rejected. Returns `None` on a count mismatch (structures diverged) or
/// if the map does not send `anchor -> partner`.
fn read_off_map(
    index: &ScalableIndex,
    a_var: &[u64],
    b_var: &[u64],
    anchor: usize,
    partner: usize,
) -> Option<Vec<u32>> {
    // Group active variables by colour on each side.
    let mut a_groups: std::collections::HashMap<u64, Vec<usize>> = std::collections::HashMap::new();
    let mut b_groups: std::collections::HashMap<u64, Vec<usize>> = std::collections::HashMap::new();
    for vi in 0..index.nvars {
        if index.var_incidence[vi].is_empty() {
            continue;
        }
        a_groups.entry(a_var[vi]).or_default().push(vi);
        b_groups.entry(b_var[vi]).or_default().push(vi);
    }
    if a_groups.len() != b_groups.len() {
        return None;
    }

    let mut perm: Vec<u32> = (0..index.nvars as u32).collect();
    for (color, a_members) in &a_groups {
        let b_members = b_groups.get(color)?;
        // Structural divergence, or a class too large to complete by positional
        // pairing — bail (sound: just no generator from this seed).
        if a_members.len() != b_members.len() {
            return None;
        }
        if a_members.len() > SMALL_CLASS_LIMIT.max(1) {
            return None;
        }
        // Pair sorted-by-id members positionally (singletons: the only choice).
        let mut a_sorted = a_members.clone();
        a_sorted.sort_unstable();
        let mut b_sorted = b_members.clone();
        b_sorted.sort_unstable();
        for (&av, &bv) in a_sorted.iter().zip(b_sorted.iter()) {
            perm[av] = bv as u32;
        }
    }

    if perm[anchor] as usize != partner {
        return None;
    }
    Some(perm)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::eval_constraint;

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn neg(var: u32) -> PbLit {
        PbLit { var, negated: true }
    }

    fn term(coeff: i128, l: PbLit) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![l],
        }
    }

    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn eq(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Eq,
            rhs,
        }
    }

    /// Brute-force check that an augmented instance is equisatisfiable with the
    /// original over all `2^num_vars` assignments, and (when an objective is
    /// present) that the minimum feasible objective value is identical.
    fn assert_verdict_preserved(original: &PbInstance, augmented: &PbInstance) {
        let n = original.num_vars as usize;
        assert!(n <= 20, "brute force only for small instances");

        let feasible = |inst: &PbInstance, assign: &[bool]| -> bool {
            inst.constraints.iter().all(|c| eval_constraint(c, assign))
        };

        let mut orig_sat = false;
        let mut aug_sat = false;
        let mut orig_best: Option<i128> = None;
        let mut aug_best: Option<i128> = None;

        for mask in 0u32..(1u32 << n) {
            let assign: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
            let o = feasible(original, &assign);
            let a = feasible(augmented, &assign);
            if o {
                orig_sat = true;
                if let Some(obj) = &original.objective {
                    let v = crate::solver::eval_objective(obj, &assign);
                    orig_best = Some(orig_best.map_or(v, |b| b.min(v)));
                }
            }
            if a {
                aug_sat = true;
                if let Some(obj) = &augmented.objective {
                    let v = crate::solver::eval_objective(obj, &assign);
                    aug_best = Some(aug_best.map_or(v, |b| b.min(v)));
                }
            }
        }

        assert_eq!(orig_sat, aug_sat, "SAT/UNSAT verdict changed");
        assert_eq!(orig_best, aug_best, "optimum changed");
    }

    #[test]
    fn detects_three_interchangeable_columns() {
        // x1, x2, x3 each appear identically: +1 in two cardinality rows.
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 2,
            constraints: vec![
                ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 2),
                ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1),
            ],
            objective: None,
        };
        let groups = detect_interchangeable_groups(&instance);
        assert_eq!(groups, vec![vec![1, 2, 3]]);

        let (aug, res) = break_symmetries(&instance);
        assert_eq!(res.interchangeable_groups, 1);
        assert_eq!(res.lex_constraints_added, 2);
        assert_verdict_preserved(&instance, &aug);
    }

    #[test]
    fn distinct_coefficients_are_not_interchangeable() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(3, lit(1)), term(2, lit(2))], 4)],
            objective: None,
        };
        assert!(detect_interchangeable_groups(&instance).is_empty());
        let (aug, res) = break_symmetries(&instance);
        assert!(!res.changed_instance());
        assert_eq!(aug, instance);
    }

    #[test]
    fn distinct_polarity_breaks_interchangeability() {
        // x1 appears positive, x2 appears negated in the same row -> not a
        // sound transposition (swapping columns would not map the row to
        // itself), so the signatures must differ.
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, lit(1)), term(1, neg(2))], 1)],
            objective: None,
        };
        assert!(detect_interchangeable_groups(&instance).is_empty());
    }

    #[test]
    fn same_negated_polarity_is_interchangeable() {
        // Both negated with the same coefficient in the same row: swapping is an
        // automorphism.
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, neg(1)), term(1, neg(2))], 1)],
            objective: None,
        };
        assert_eq!(detect_interchangeable_groups(&instance), vec![vec![1, 2]]);
        let (aug, _) = break_symmetries(&instance);
        assert_verdict_preserved(&instance, &aug);
    }

    #[test]
    fn different_rows_break_interchangeability() {
        // x1 in row 0, x2 in row 1 only: signatures differ by row index.
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 2,
            constraints: vec![ge(vec![term(1, lit(1))], 1), ge(vec![term(1, lit(2))], 1)],
            objective: None,
        };
        assert!(detect_interchangeable_groups(&instance).is_empty());
    }

    #[test]
    fn objective_coefficients_must_match() {
        // x1, x2 identical in constraints but different objective coefficients
        // -> the swap is not objective-invariant, so reject.
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 1)],
            objective: Some(PbObjective {
                terms: vec![term(1, lit(1)), term(2, lit(2))],
            }),
        };
        assert!(detect_interchangeable_groups(&instance).is_empty());
    }

    #[test]
    fn objective_coefficients_match_allows_group() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 1)],
            objective: Some(PbObjective {
                terms: vec![term(5, lit(1)), term(5, lit(2))],
            }),
        };
        assert_eq!(detect_interchangeable_groups(&instance), vec![vec![1, 2]]);
        let (aug, _) = break_symmetries(&instance);
        assert_verdict_preserved(&instance, &aug);
    }

    #[test]
    fn nonlinear_term_excludes_variables() {
        // x1 appears in a product term -> excluded; x2,x3 are linear and equal.
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![PbConstraint {
                terms: vec![
                    PbTerm {
                        coeff: 1,
                        lits: vec![lit(1), lit(2)],
                    },
                    term(1, lit(2)),
                    term(1, lit(3)),
                ],
                rel: PbRel::Ge,
                rhs: 1,
            }],
            objective: None,
        };
        // x2 occurs in the product term AND a linear term -> excluded (it is
        // mentioned by a non-linear term). x1 excluded too. x3 alone -> no group.
        let groups = detect_interchangeable_groups(&instance);
        assert!(groups.is_empty(), "got {groups:?}");
    }

    #[test]
    fn repeated_variable_in_row_is_excluded() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(
                vec![term(1, lit(1)), term(1, lit(1)), term(1, lit(2))],
                1,
            )],
            objective: None,
        };
        // x1 appears twice in the same row -> excluded; x2 alone -> no group.
        assert!(detect_interchangeable_groups(&instance).is_empty());
    }

    #[test]
    fn pigeonhole_3_2_groups_preserve_unsat() {
        // Pigeonhole 3 pigeons / 2 holes. x_{i,j}: pigeon i in hole j.
        // x1=p1h1 x2=p1h2 x3=p2h1 x4=p2h2 x5=p3h1 x6=p3h2.
        // Each pigeon placed: x1+x2>=1, x3+x4>=1, x5+x6>=1.
        // Each hole <=1 pigeon: -x1-x3-x5>=-1, -x2-x4-x6>=-1.
        let instance = PbInstance {
            num_vars: 6,
            num_constraints: 5,
            constraints: vec![
                ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
                ge(vec![term(1, lit(3)), term(1, lit(4))], 1),
                ge(vec![term(1, lit(5)), term(1, lit(6))], 1),
                ge(
                    vec![term(-1, lit(1)), term(-1, lit(3)), term(-1, lit(5))],
                    -1,
                ),
                ge(
                    vec![term(-1, lit(2)), term(-1, lit(4)), term(-1, lit(6))],
                    -1,
                ),
            ],
            objective: None,
        };
        // No two columns share an identical signature here (each variable lives
        // in a unique pigeon-row), so the column test finds nothing — and that
        // is correct: this encoding's symmetry is a row/hole symmetry, not a
        // raw interchangeable-column symmetry. The key property we assert is
        // that whatever we add never flips the verdict.
        let (aug, _res) = break_symmetries(&instance);
        assert_verdict_preserved(&instance, &aug);
    }

    #[test]
    fn matrix_column_symmetry_preserves_verdict() {
        // 2x3 matrix-style: rows are cardinality over columns; all three
        // columns appear identically in both rows -> {x1,x2,x3} interchangeable.
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 2,
            constraints: vec![
                ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1),
                ge(
                    vec![term(-1, lit(1)), term(-1, lit(2)), term(-1, lit(3))],
                    -2,
                ),
            ],
            objective: None,
        };
        let groups = detect_interchangeable_groups(&instance);
        assert_eq!(groups, vec![vec![1, 2, 3]]);
        let (aug, res) = break_symmetries(&instance);
        assert_eq!(res.lex_constraints_added, 2);
        assert_verdict_preserved(&instance, &aug);
    }

    #[test]
    fn eq_constraints_are_handled() {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![eq(
                vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))],
                2,
            )],
            objective: None,
        };
        assert_eq!(
            detect_interchangeable_groups(&instance),
            vec![vec![1, 2, 3]]
        );
        let (aug, _) = break_symmetries(&instance);
        assert_verdict_preserved(&instance, &aug);
    }

    #[test]
    fn no_vars_no_groups() {
        let instance = PbInstance {
            num_vars: 0,
            num_constraints: 0,
            constraints: vec![],
            objective: None,
        };
        assert!(detect_interchangeable_groups(&instance).is_empty());
        let (aug, res) = break_symmetries(&instance);
        assert!(!res.changed_instance());
        assert_eq!(aug, instance);
    }

    #[test]
    fn lex_constraint_shape() {
        let c = lex_ge_constraint(2, 5);
        assert_eq!(c.rel, PbRel::Ge);
        assert_eq!(c.rhs, 0);
        assert_eq!(c.terms.len(), 2);
        assert_eq!(c.terms[0].coeff, 1);
        assert_eq!(c.terms[0].lits, vec![lit(2)]);
        assert_eq!(c.terms[1].coeff, -1);
        assert_eq!(c.terms[1].lits, vec![lit(5)]);
    }

    #[test]
    fn header_num_constraints_updated() {
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 1,
            constraints: vec![ge(
                vec![
                    term(1, lit(1)),
                    term(1, lit(2)),
                    term(1, lit(3)),
                    term(1, lit(4)),
                ],
                2,
            )],
            objective: None,
        };
        let (aug, res) = break_symmetries(&instance);
        // 4 interchangeable -> 3 lex constraints.
        assert_eq!(res.lex_constraints_added, 3);
        assert_eq!(aug.num_constraints, 4);
        assert_eq!(aug.constraints.len(), 4);
        assert_eq!(aug.num_vars, 4);
        assert_verdict_preserved(&instance, &aug);
    }

    // --- binary lex-leader constraint ---

    #[test]
    fn binary_lex_constraint_shape_and_weights() {
        // a=(1,2), b=(3,4): 2*x1 + 1*x2 - 2*x3 - 1*x4 >= 0.
        let c = binary_lex_leader_constraint(&[1, 2], &[3, 4]).expect("buildable");
        assert_eq!(c.rel, PbRel::Ge);
        assert_eq!(c.rhs, 0);
        // MSB coordinate (index 0) weight 2^1 = 2; LSB weight 2^0 = 1.
        let coeff_of = |var: u32| -> i128 {
            c.terms
                .iter()
                .find(|t| t.lits == vec![lit(var)])
                .map(|t| t.coeff)
                .unwrap_or(0)
        };
        assert_eq!(coeff_of(1), 2);
        assert_eq!(coeff_of(2), 1);
        assert_eq!(coeff_of(3), -2);
        assert_eq!(coeff_of(4), -1);
    }

    #[test]
    fn binary_lex_constraint_rejects_oversized() {
        let a: Vec<u32> = (1..=70).collect();
        let b: Vec<u32> = (71..=140).collect();
        assert!(binary_lex_leader_constraint(&a, &b).is_none());
    }

    #[test]
    fn binary_lex_constraint_rejects_mismatched() {
        assert!(binary_lex_leader_constraint(&[1, 2], &[3]).is_none());
        assert!(binary_lex_leader_constraint(&[], &[]).is_none());
    }

    // --- verified vector transposition (matrix) detection ---

    #[test]
    fn weighted_matrix_row_swap_detected_and_sound() {
        // Two rows with DISTINCT coefficients so the row->row bijection is
        // unambiguous. Row A over x1,x2 ; row B over x3,x4 with identical shape.
        // A coupling constraint links them symmetrically.
        //   3 x1 + 2 x2 >= 1     (row A)
        //   3 x3 + 2 x4 >= 1     (row B)
        //   1 x1 + 1 x3 >= 1     (couples x1<->x3)
        //   1 x2 + 1 x4 >= 1     (couples x2<->x4)
        // sigma = (x1 x3)(x2 x4) maps A<->B and each coupling row to itself.
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 4,
            constraints: vec![
                ge(vec![term(3, lit(1)), term(2, lit(2))], 1),
                ge(vec![term(3, lit(3)), term(2, lit(4))], 1),
                ge(vec![term(1, lit(1)), term(1, lit(3))], 1),
                ge(vec![term(1, lit(2)), term(1, lit(4))], 1),
            ],
            objective: None,
        };
        let gens = detect_verified_vector_transpositions(&instance);
        assert_eq!(
            gens.len(),
            1,
            "expected one verified generator, got {gens:?}"
        );
        assert_eq!(gens[0].a, vec![1, 2]);
        assert_eq!(gens[0].b, vec![3, 4]);

        let (aug, res) = break_symmetries(&instance);
        assert_eq!(res.vector_transposition_generators, 1);
        assert_verdict_preserved(&instance, &aug);
    }

    #[test]
    fn non_automorphism_candidate_is_rejected() {
        // Same two weighted rows, but the coupling constraints are asymmetric so
        // sigma=(x1 x3)(x2 x4) is NOT an automorphism. Detection must add nothing.
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 3,
            constraints: vec![
                ge(vec![term(3, lit(1)), term(2, lit(2))], 1),
                ge(vec![term(3, lit(3)), term(2, lit(4))], 1),
                // Couples x1 with x4 (cross), breaking the (x1 x3)(x2 x4) swap.
                ge(vec![term(5, lit(1)), term(7, lit(4))], 1),
            ],
            objective: None,
        };
        let gens = detect_verified_vector_transpositions(&instance);
        assert!(
            gens.is_empty(),
            "unsound generator slipped through: {gens:?}"
        );
        let (aug, res) = break_symmetries(&instance);
        // No interchangeable columns either here.
        assert_eq!(res.vector_transposition_generators, 0);
        assert_verdict_preserved(&instance, &aug);
    }

    #[test]
    fn matrix_swap_with_objective_invariance() {
        // Row swap is sound only if the objective is invariant under it.
        // Objective gives x1,x3 weight 4 and x2,x4 weight 6, which IS invariant
        // under (x1 x3)(x2 x4).
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 3,
            constraints: vec![
                ge(vec![term(3, lit(1)), term(2, lit(2))], 1),
                ge(vec![term(3, lit(3)), term(2, lit(4))], 1),
                ge(vec![term(1, lit(1)), term(1, lit(3))], 1),
            ],
            objective: Some(PbObjective {
                terms: vec![
                    term(4, lit(1)),
                    term(6, lit(2)),
                    term(4, lit(3)),
                    term(6, lit(4)),
                ],
            }),
        };
        let gens = detect_verified_vector_transpositions(&instance);
        assert_eq!(gens.len(), 1, "got {gens:?}");
        let (aug, _) = break_symmetries(&instance);
        assert_verdict_preserved(&instance, &aug);
    }

    #[test]
    fn matrix_swap_rejected_when_objective_not_invariant() {
        // Objective weights differ across the swap: x1=4 but x3=9. Reject.
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 3,
            constraints: vec![
                ge(vec![term(3, lit(1)), term(2, lit(2))], 1),
                ge(vec![term(3, lit(3)), term(2, lit(4))], 1),
                ge(vec![term(1, lit(1)), term(1, lit(3))], 1),
            ],
            objective: Some(PbObjective {
                terms: vec![
                    term(4, lit(1)),
                    term(6, lit(2)),
                    term(9, lit(3)),
                    term(6, lit(4)),
                ],
            }),
        };
        let gens = detect_verified_vector_transpositions(&instance);
        assert!(
            gens.is_empty(),
            "objective-breaking swap accepted: {gens:?}"
        );
        let (aug, _) = break_symmetries(&instance);
        assert_verdict_preserved(&instance, &aug);
    }

    #[test]
    fn nonlinear_constraint_disables_generator_search() {
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 2,
            constraints: vec![
                PbConstraint {
                    terms: vec![PbTerm {
                        coeff: 1,
                        lits: vec![lit(1), lit(2)],
                    }],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
                ge(vec![term(3, lit(3)), term(2, lit(4))], 1),
            ],
            objective: None,
        };
        assert!(detect_verified_vector_transpositions(&instance).is_empty());
    }

    #[test]
    fn matrix_swap_unsat_preserved_brute() {
        // A small UNSAT weighted matrix with a verified swap: ensure UNSAT holds
        // after augmentation (verdict preserved across all assignments).
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 5,
            constraints: vec![
                ge(vec![term(3, lit(1)), term(2, lit(2))], 6), // needs both x1,x2
                ge(vec![term(3, lit(3)), term(2, lit(4))], 6), // needs both x3,x4
                // upper bound forcing contradiction with the >=6 rows
                ge(vec![term(-1, lit(1)), term(-1, lit(3))], 0), // x1+x3 <= 0
                ge(vec![term(1, lit(1)), term(1, lit(3))], 1),   // x1+x3 >= 1 (contradiction)
                ge(vec![term(1, lit(2)), term(1, lit(4))], 1),
            ],
            objective: None,
        };
        // Whatever generators fire, the verdict must not change.
        let (aug, _) = break_symmetries(&instance);
        assert_verdict_preserved(&instance, &aug);
    }

    // --- randomized soundness fuzz ---

    /// Tiny deterministic LCG (no external rng dependency).
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
            self.0
        }
        fn range(&mut self, lo: i128, hi: i128) -> i128 {
            let span = (hi - lo + 1) as u64;
            lo + (self.next() % span) as i128
        }
    }

    /// Generates a random small linear PB instance with a deliberate bias toward
    /// repeated columns/rows so symmetry detection frequently fires.
    fn random_instance(rng: &mut Lcg, with_objective: bool) -> PbInstance {
        let num_vars = rng.range(2, 8) as u32;
        let num_cons = rng.range(1, 5) as usize;
        let mut constraints = Vec::with_capacity(num_cons);
        for _ in 0..num_cons {
            let mut terms = Vec::new();
            // Each variable included with some probability; coefficient from a
            // small set so equal columns are common.
            for v in 1..=num_vars {
                if rng.range(0, 2) == 0 {
                    continue;
                }
                let coeff = [-2i128, -1, 1, 2][(rng.range(0, 3)) as usize];
                let negated = rng.range(0, 1) == 1;
                terms.push(PbTerm {
                    coeff,
                    lits: vec![PbLit { var: v, negated }],
                });
            }
            if terms.is_empty() {
                terms.push(PbTerm {
                    coeff: 1,
                    lits: vec![lit(1)],
                });
            }
            let rel = if rng.range(0, 3) == 0 {
                PbRel::Eq
            } else {
                PbRel::Ge
            };
            let rhs = rng.range(-3, 3);
            constraints.push(PbConstraint { terms, rel, rhs });
        }
        let objective = if with_objective {
            let mut terms = Vec::new();
            for v in 1..=num_vars {
                if rng.range(0, 1) == 1 {
                    terms.push(PbTerm {
                        coeff: rng.range(1, 3),
                        lits: vec![lit(v)],
                    });
                }
            }
            Some(PbObjective { terms })
        } else {
            None
        };
        PbInstance {
            num_vars,
            num_constraints: constraints.len() as u32,
            constraints,
            objective,
        }
    }

    #[test]
    fn fuzz_verdict_preserved_decision() {
        let mut rng = Lcg(0x1234_5678_9abc_def0);
        for _ in 0..4000 {
            let inst = random_instance(&mut rng, false);
            let (aug, _res) = break_symmetries(&inst);
            assert_verdict_preserved(&inst, &aug);
        }
    }

    #[test]
    fn fuzz_verdict_preserved_optimization() {
        let mut rng = Lcg(0x0fed_cba9_8765_4321);
        for _ in 0..4000 {
            let inst = random_instance(&mut rng, true);
            let (aug, _res) = break_symmetries(&inst);
            assert_verdict_preserved(&inst, &aug);
        }
    }

    // ----------------------------------------------------------------------
    // Scalable detector (colour refinement + individualise-refine).
    // ----------------------------------------------------------------------

    /// Builds an `n x n` Boolean-matrix decision instance with row-sum and
    /// column-sum cardinality constraints `>= 1`. Variable `x_{i,j}` has id
    /// `i*n + j + 1`. This construction has the full S_n x S_n row/column
    /// interchange symmetry — a textbook scalable-symmetry target.
    fn matrix_grid(n: u32, rhs: i128) -> PbInstance {
        let var = |i: u32, j: u32| -> u32 { i * n + j + 1 };
        let mut constraints = Vec::new();
        for i in 0..n {
            let terms: Vec<PbTerm> = (0..n).map(|j| term(1, lit(var(i, j)))).collect();
            constraints.push(ge(terms, rhs));
        }
        for j in 0..n {
            let terms: Vec<PbTerm> = (0..n).map(|i| term(1, lit(var(i, j)))).collect();
            constraints.push(ge(terms, rhs));
        }
        PbInstance {
            num_vars: n * n,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: None,
        }
    }

    #[test]
    fn scalable_detects_verified_matrix_generators() {
        // A 4x4 grid: row/column interchange symmetry. The scalable detector must
        // find at least one generator, and EVERY generator must be a verified
        // automorphism (constraint-multiset invariant).
        let instance = matrix_grid(4, 1);
        let gens = detect_scalable_generators(&instance, None);
        assert!(
            !gens.is_empty(),
            "scalable detector found no generators on a symmetric grid"
        );
        // Re-verify each returned generator independently against the oracle.
        let canon: Vec<CanonicalConstraint> = instance
            .constraints
            .iter()
            .map(|c| canonicalize_constraint(c).unwrap())
            .collect();
        let mut multiset: BTreeMap<CanonicalConstraint, u32> = BTreeMap::new();
        for cc in &canon {
            *multiset.entry(cc.clone()).or_insert(0) += 1;
        }
        let objective = canonical_objective(None).unwrap();
        for g in &gens {
            assert!(
                is_automorphism(&canon, &multiset, &objective, g),
                "scalable detector returned a NON-automorphism: {g:?}"
            );
            // Each generator must move at least two variables.
            assert!(g.iter().any(|(k, v)| k != v));
        }
    }

    #[test]
    fn scalable_generators_preserve_verdict_brute() {
        // 3x3 grid (9 vars): emit lex-leader rows from the scalable generators and
        // brute-force-check the augmented instance is equisatisfiable.
        let instance = matrix_grid(3, 1);
        let gens = detect_scalable_generators(&instance, None);
        assert!(!gens.is_empty());
        let mut augmented = instance.clone();
        for g in &gens {
            if let Some(c) = permutation_lex_leader_constraint(g) {
                augmented.constraints.push(c);
            }
        }
        assert_verdict_preserved(&instance, &augmented);
    }

    #[test]
    fn scalable_generators_preserve_unsat_brute() {
        // A 3x3 grid demanding every row AND column sum to 3 (all ones) is SAT;
        // make it UNSAT by also forbidding a particular cell, then check the
        // scalable lex rows do not flip the verdict.
        let mut instance = matrix_grid(3, 3); // forces all x=1 -> SAT (all ones)
                                              // Add `x_{0,0} <= 0` (i.e. -x1 >= 0) -> now UNSAT (cannot have row 0 sum 3).
        instance.constraints.push(ge(vec![term(-1, lit(1))], 0));
        instance.num_constraints += 1;
        let gens = detect_scalable_generators(&instance, None);
        let mut augmented = instance.clone();
        for g in &gens {
            if let Some(c) = permutation_lex_leader_constraint(g) {
                augmented.constraints.push(c);
            }
        }
        assert_verdict_preserved(&instance, &augmented);
    }

    #[test]
    fn c3_1_single_var_and_scalable_conventions_agree() {
        // C3-1 regression: the always-on single-variable chain (`lex_ge_constraint`,
        // keep-max) and the scalable permutation lex-leader
        // (`permutation_lex_leader_constraint`) MUST emit the SAME convention. For the
        // transposition (1 2) both must encode `x_1 >= x_2`. A mismatch (keep-max chain
        // vs keep-min scalable) on a shared interchangeable pair forces x_1 == x_2 and
        // can delete an entire orbit -> false UNSAT the model-only VIG cannot catch.
        let mut perm = BTreeMap::new();
        perm.insert(1u32, 2u32);
        perm.insert(2u32, 1u32);
        let scalable = permutation_lex_leader_constraint(&perm).expect("transposition lex row");
        let chain = lex_ge_constraint(1, 2);
        let as_map = |c: &PbConstraint| -> BTreeMap<u32, i128> {
            c.terms
                .iter()
                .map(|t| {
                    assert_eq!(t.lits.len(), 1, "single-literal term expected");
                    assert!(!t.lits[0].negated, "positive literal expected");
                    (t.lits[0].var, t.coeff)
                })
                .collect()
        };
        assert_eq!(scalable.rel, PbRel::Ge);
        assert_eq!(chain.rel, PbRel::Ge);
        assert_eq!(
            as_map(&scalable),
            as_map(&chain),
            "scalable lex-leader must match the single-variable keep-max convention (C3-1)"
        );
    }

    #[test]
    fn c3_1_combined_lex_rows_do_not_delete_orbit() {
        // C3-1 regression (end-to-end at the constraint level): an instance SAT only via
        // x1 != x2, augmented with BOTH the single-variable chain AND the scalable
        // transposition lex row for the SAME pair, must stay SAT. Before the fix the two
        // opposite conventions forced x1 == x2 and yielded a false UNSAT.
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 2,
            // x1 + x2 == 1 (two Ge rows): SAT iff exactly one of x1, x2 is true.
            constraints: vec![
                ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
                ge(vec![term(-1, lit(1)), term(-1, lit(2))], -1),
            ],
            objective: None,
        };
        let mut perm = BTreeMap::new();
        perm.insert(1u32, 2u32);
        perm.insert(2u32, 1u32);
        let mut augmented = instance.clone();
        augmented.constraints.push(lex_ge_constraint(1, 2));
        augmented
            .constraints
            .push(permutation_lex_leader_constraint(&perm).expect("transposition lex row"));
        augmented.num_constraints = u32::try_from(augmented.constraints.len()).unwrap();
        // Original SAT ({(1,0),(0,1)}); augmented must remain SAT (the unified keep-max
        // rows keep (1,0)).  A false UNSAT here is the C3-1 wrong answer.
        assert_verdict_preserved(&instance, &augmented);
    }

    #[test]
    fn scalable_finds_nothing_on_asymmetric_instance() {
        // Distinct coefficients per variable in a single row: no two variables are
        // interchangeable, so no non-trivial automorphism exists.
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 1,
            constraints: vec![ge(
                vec![
                    term(1, lit(1)),
                    term(2, lit(2)),
                    term(4, lit(3)),
                    term(8, lit(4)),
                ],
                3,
            )],
            objective: None,
        };
        let gens = detect_scalable_generators(&instance, None);
        assert!(
            gens.is_empty(),
            "asymmetric instance yielded generators: {gens:?}"
        );
    }

    #[test]
    fn highly_symmetric_gate_excludes_small_and_diverse() {
        // Small instance: gate is false (below the scalable cap).
        assert!(!is_highly_symmetric_candidate(&matrix_grid(3, 1)));
        // Empty: false.
        assert!(!is_highly_symmetric_candidate(&PbInstance {
            num_vars: 0,
            num_constraints: 0,
            constraints: vec![],
            objective: None,
        }));
    }

    #[test]
    fn permutation_lex_leader_is_sound_for_general_perm() {
        // A 3-cycle σ=(1 2 3): the lex-leader x <=_lex σ(x) must not flip the
        // verdict of an instance for which σ is an automorphism. Use a symmetric
        // cardinality row over x1,x2,x3.
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![ge(
                vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))],
                2,
            )],
            objective: None,
        };
        let mut perm = BTreeMap::new();
        perm.insert(1u32, 2u32);
        perm.insert(2u32, 3u32);
        perm.insert(3u32, 1u32);
        let mut augmented = instance.clone();
        augmented
            .constraints
            .push(permutation_lex_leader_constraint(&perm).unwrap());
        assert_verdict_preserved(&instance, &augmented);
    }

    /// Generates a random small `k x k` matrix grid with a random rhs and checks
    /// that scalable symmetry breaking never flips the verdict.
    #[test]
    fn fuzz_scalable_grid_verdict_preserved() {
        let mut rng = Lcg(0xABCD_1234_5678_9F01);
        for _ in 0..200 {
            let n = rng.range(2, 4) as u32; // up to 4x4 = 16 vars (brute <= 2^16)
            let rhs = rng.range(0, i128::from(n));
            let instance = matrix_grid(n, rhs);
            let gens = detect_scalable_generators(&instance, None);
            let mut augmented = instance.clone();
            for g in &gens {
                if let Some(c) = permutation_lex_leader_constraint(g) {
                    augmented.constraints.push(c);
                }
            }
            assert_verdict_preserved(&instance, &augmented);
        }
    }
}
