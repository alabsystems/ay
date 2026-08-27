// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array-read elimination for the ABVFP lane.
//!
//! # What this does
//!
//! Replaces every `(select A i)` — `A` a declared
//! `(Array (_ BitVec w) <non-array>)` symbol, `i` any bitvector term — by a
//! fresh constant of the element sort, keyed by **(array symbol, index)**. The
//! result is an array-free QF_BVFP formula, which the existing FP/BV
//! bit-blaster decides.
//!
//! # Symbolic indices: the congruence closure is what makes this exact
//!
//! For a *literal* index the cell key is the numeric value, so two reads at the
//! same address are literally the same variable and the array's functionality
//! is free. A *symbolic* index has no such luxury: `(select A i)` and
//! `(select A j)` become two independent variables `r_i`, `r_j`, and nothing
//! stops a model from setting `i = j` while `r_i ≠ r_j` — an array that is not
//! a function, i.e. a false `sat`.
//!
//! The fix is the classical Ackermann reduction: for EVERY pair of distinct
//! cells on the SAME array, assert
//!
//! ```text
//! (=> (= i j) (= r_i r_j))
//! ```
//!
//! * **Forward (`φ` sat ⟹ `φ'` sat).** Set `r_i := M(A)[M(i)]`. Every axiom
//!   holds because `M(A)` is a function: `M(i) = M(j)` forces the same cell.
//! * **Backward (`φ'` sat ⟹ `φ` sat).** Given values for the `r`s satisfying
//!   every axiom, define `M(A)[v] := r_i` for any cell whose index evaluates to
//!   `v`. That is WELL-DEFINED exactly because the axioms make all such `r`s
//!   agree — this is the step that fails without them — and arbitrary at
//!   addresses no read mentions.
//!
//! Both directions need *all* pairs, which is why a pair budget overrun
//! ([`FlattenAbstain::TooManyReadPairs`]) abstains instead of emitting a prefix.
//! Pairs of two literal cells are skipped: distinct literal keys have distinct
//! values, so `(= i j)` is `false` and the axiom is a tautology.
//!
//! This is exactly the transformation the SMT-LIB `20170428-Liew-KLEE`
//! benchmark authors performed themselves: every QF_ABVFP file in that family
//! carries
//!
//! ```text
//! Corresponding query: An equisatisfiable query (arrays replaced with
//! bitvectors) is available at QF_BVFP/.../query.NN.smt2
//! ```
//!
//! and AY already decides that QF_BVFP encoding. This pre-pass closes the gap
//! between the two encodings of the same benchmark.
//!
//! # Soundness: this is an EQUIVALENCE, not an approximation
//!
//! Let `φ` be the assertions and `φ'` the rewrite, `fresh_{A,k}` the constant
//! introduced for cell `(A, k)`.
//!
//! * **Forward (`φ` sat ⟹ `φ'` sat).** Take any model `M` of `φ`. `M`
//!   interprets `A` as a total function; set `fresh_{A,k} := M(A)[k]` and keep
//!   every other symbol. Each rewritten atom is *syntactically* the original
//!   atom under that substitution, so it evaluates identically.
//! * **Backward (`φ'` sat ⟹ `φ` sat) — the direction that matters.** Arrays
//!   are TOTAL functions, so for any assignment to the finitely many fresh
//!   constants that satisfies the congruence axioms above (which is what makes
//!   "the cell at address `v`" well defined when two symbolic indices collide)
//!   there EXISTS an array agreeing with it at those indices and arbitrary
//!   elsewhere. The array's behaviour off those indices is unobservable
//!   *because the side conditions enforce it*:
//!   - no `store` anywhere ⇒ no positional dependence on other cells;
//!   - no array-sorted `=` / `distinct` / `ite` ⇒ no extensional comparison;
//!   - every array symbol occurs ONLY as `args[0]` of a `select` ⇒ there is no
//!     other way to observe it;
//!   - no quantifier ⇒ no universal claim over indices.
//!
//! Remove any one of those conditions and the backward direction fails, which
//! is why each is *checked on the term DAG* (where array structure is still
//! visible) rather than assumed. Both directions hold, so `sat ↔ sat` and
//! `unsat ↔ unsat`: nothing is relaxed and nothing is degraded.
//!
//! # Why this is not the #8728 shape
//!
//! #8728 was a *routing* decision: DT+FP was sent to a solver that could not
//! see the FP theory, the FP constraints were silently DROPPED, and the
//! resulting `sat` was published. Dropping a theory enlarges the model set —
//! sound for `unsat`, unsound for `sat` — and it had no side conditions to stop
//! it. Here (a) the FP theory is untouched: nothing FP-sorted is abstracted,
//! only the ARRAY theory is affected and it is *eliminated by a validated
//! rewrite*; (b) the validity conditions are checked on the term DAG, where
//! array structure is still visible (a `select` arm inside the bit-blaster
//! could not see them); (c) anything outside the conditions ABSTAINS, keeping
//! today's `unknown`.
//!
//! If a side condition is ever loosened into an approximation it may only be
//! loosened in the direction that keeps *refutation* sound, and `sat` must then
//! degrade — see the existing template at the `congruence_incomplete && Sat`
//! site in `fp.rs`.

mod congruence;
mod rewrite;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use congruence::congruence_axioms;
use num_bigint::BigInt;
use rewrite::{is_array_free, rewrite};

/// What identifies a read cell within one array.
///
/// Two reads share a cell iff they are the same `(array, index)` pair. For a
/// literal index the key is the NUMERIC VALUE, so `(_ bv4 64)` and `#x04`
/// collapse to one cell; for a symbolic index the key is the interned index
/// TERM, and any two distinct keys are related by an explicit congruence axiom
/// instead (see [`congruence`]).
#[derive(Debug, Clone, PartialEq, Eq)]
enum CellKey {
    /// A bitvector-literal index, keyed by value.
    Literal(BigInt),
    /// A symbolic index, keyed by its interned term.
    Symbolic(TermId),
}

/// Why the pre-pass declined to fire. Each variant maps to a DISTINCT
/// `unknown.detail` string so the abstaining population is attributable
/// instead of joining the "no specific reason" bucket.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FlattenAbstain {
    /// No array-sorted term occurs at all — nothing for this pass to do.
    NoArrays,
    /// A `store` occurs somewhere: cells become positionally dependent.
    Store,
    /// A quantifier occurs: a universal claim over indices is not covered.
    Quantifier,
    /// A `let` binding survived elaboration; its body is not walked here.
    LetBinding,
    /// An array sort this pass cannot eliminate: the index must be a bitvector
    /// (the cell key is a bitvector value) and the element sort must not itself
    /// be an array (a nested array would need its own elimination round).
    ArraySortUnsupported,
    /// More read pairs on one array than [`congruence::MAX_CONGRUENCE_PAIRS`].
    /// The closure is exact only when EVERY pair is asserted, so an overrun
    /// abstains outright — a prefix would under-constrain the cells and
    /// manufacture a false `sat`.
    TooManyReadPairs,
    /// An array-sorted term that is not a declared symbol (`ite`, `store`,
    /// const-array, array-valued UF application, ...).
    ArrayTermNotSymbol,
    /// An array symbol occurs somewhere other than `args[0]` of a `select`
    /// (array `=` / `distinct` / `ite`, or an array passed to a UF).
    ArrayNotOnlySelected,
    /// FAIL-CLOSED BACKSTOP: the rewrite left array structure behind.
    ResidualArray,
}

impl FlattenAbstain {
    /// The `unknown.detail` text for this abstention (abstention telemetry).
    pub(super) fn detail(self) -> &'static str {
        match self {
            Self::NoArrays => {
                "ABVFP constant-index read elimination: no eliminable array read in the assertions"
            }
            Self::Store => {
                "ABVFP constant-index read elimination abstained: the assertions contain `store`, \
                 so array cells are positionally dependent"
            }
            Self::Quantifier => {
                "ABVFP constant-index read elimination abstained: the assertions are quantified, \
                 so an index claim need not be finite"
            }
            Self::LetBinding => {
                "ABVFP constant-index read elimination abstained: a `let` binding survived \
                 elaboration"
            }
            Self::ArraySortUnsupported => {
                "ABVFP array read elimination abstained: array sort is not \
                 (Array (_ BitVec i) <non-array>)"
            }
            Self::TooManyReadPairs => {
                "ABVFP array read elimination abstained: too many distinct read indices on one \
                 array for an exact congruence closure within budget"
            }
            Self::ArrayTermNotSymbol => {
                "ABVFP constant-index read elimination abstained: an array-sorted term is not a \
                 declared array symbol"
            }
            Self::ArrayNotOnlySelected => {
                "ABVFP constant-index read elimination abstained: an array symbol occurs outside \
                 `select` position (extensional `=`/`distinct`/`ite` or a UF argument)"
            }
            Self::ResidualArray => {
                "ABVFP constant-index read elimination abstained: the rewrite left array \
                 structure behind (fail-closed backstop)"
            }
        }
    }
}

/// One eliminated array cell: which symbol, which numeric index, and the fresh
/// constant standing for it. Retained so a `sat` can be published against the
/// ORIGINAL array symbol rather than the internal cell constants.
#[derive(Debug, Clone)]
pub(super) struct FlatCell {
    /// The declared array symbol's term.
    pub(super) array: TermId,
    /// The index's numeric value when it is a literal. `(_ bv4 64)` and
    /// `#x0000000000000004` must collapse to ONE cell; keying on index SYNTAX
    /// would split a single array cell into two independent variables and
    /// manufacture a false `sat`.
    ///
    /// `None` for a symbolic index, whose address is only known once a model
    /// exists — the model builder resolves it through [`Self::index_term`].
    pub(super) index_value: Option<BigInt>,
    /// The index TERM as written. For a literal cell this is a literal; for a
    /// symbolic cell it is the representative index term, and it is both what
    /// the congruence axioms compare and what the model builder evaluates.
    pub(super) index_term: TermId,
    /// The fresh element-sorted constant substituted for the read.
    pub(super) fresh: TermId,
}

/// A successful plan: the rewritten assertions plus the cell map needed to
/// reconstitute the arrays in the published model.
#[derive(Debug, Clone)]
pub(super) struct FlattenPlan {
    /// Rewritten, array-free assertions.
    pub(super) assertions: Vec<TermId>,
    /// The eliminated cells, in deterministic discovery order.
    pub(super) cells: Vec<FlatCell>,
}

/// What `plan_cells` collected before any term is built.
struct CellScan {
    /// Unique cells in discovery order: (array symbol, key, index term).
    cells: Vec<(TermId, CellKey, TermId)>,
    /// Every qualifying `select` term paired with its cell index. Keyed by the
    /// ORIGINAL interned `select` TermId — never by a reconstructed one, since
    /// `mk_select` is allowed to simplify and could hand back a different term.
    reads: Vec<(TermId, usize)>,
}

/// Numeric value of a bitvector literal, or `None` for anything symbolic.
fn bv_literal_value(terms: &TermStore, term: TermId) -> Option<BigInt> {
    match terms.get(term) {
        TermData::Const(Constant::BitVec { value, .. }) => Some(value.clone()),
        _ => None,
    }
}

/// Is `sort` an array this pass can eliminate in one round?
///
/// The index must be a bitvector: cell keys are bitvector values and the
/// congruence axioms compare bitvector terms. The element sort may be anything
/// EXCEPT another array — a nested array would leave `select` terms of array
/// sort behind, which `is_array_free` (correctly) rejects as residue.
fn is_eliminable_array(sort: &Sort) -> bool {
    match sort {
        Sort::Array(arr) => {
            matches!(arr.index_sort, Sort::BitVec(_)) && !matches!(arr.element_sort, Sort::Array(_))
        }
        _ => false,
    }
}

/// A `(select A i)` application, if `term` is one.
fn as_select(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "select" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Everything mutated while scanning one `(select A i)` occurrence.
struct ScanState {
    cells: Vec<(TermId, CellKey, TermId)>,
    reads: Vec<(TermId, usize)>,
    /// (array term, tagged cell key) -> cell slot.
    cell_index: HashMap<(TermId, Vec<u8>), usize>,
}

/// Validate one `(select array index)` and record its cell.
///
/// Returns the index term the caller must still push onto the scan stack: it is
/// an arbitrary BV term that can itself contain a `select`, a `store`, or an
/// array-sorted subterm, and skipping it would let exactly the shapes this pass
/// refuses slip through unchecked. (`array` is deliberately NOT returned — that
/// is the one legal array occurrence.)
fn scan_select(
    terms: &TermStore,
    select_term: TermId,
    array: TermId,
    index: TermId,
    state: &mut ScanState,
) -> Result<TermId, FlattenAbstain> {
    let array_sort = terms.sort(array).clone();
    if !matches!(array_sort, Sort::Array(_)) {
        return Err(FlattenAbstain::ArrayTermNotSymbol);
    }
    if !is_eliminable_array(&array_sort) {
        return Err(FlattenAbstain::ArraySortUnsupported);
    }
    if !matches!(terms.get(array), TermData::Var(_, _)) {
        return Err(FlattenAbstain::ArrayTermNotSymbol);
    }
    // Key a literal index on its NUMERIC VALUE, never on index syntax; key a
    // symbolic index on its interned term. The leading tag byte keeps the two
    // namespaces disjoint so a term id can never collide with a numeric value's
    // encoding.
    let (cell_key, key_bytes) = match bv_literal_value(terms, index) {
        Some(value) => {
            let mut bytes = vec![0u8];
            bytes.extend_from_slice(&value.to_signed_bytes_le());
            (CellKey::Literal(value), bytes)
        }
        None => {
            let mut bytes = vec![1u8];
            bytes.extend_from_slice(&index.index().to_le_bytes());
            (CellKey::Symbolic(index), bytes)
        }
    };
    let key = (array, key_bytes);
    let slot = match state.cell_index.get(&key) {
        Some(&slot) => slot,
        None => {
            let slot = state.cells.len();
            state.cells.push((array, cell_key, index));
            state.cell_index.insert(key, slot);
            slot
        }
    };
    state.reads.push((select_term, slot));
    Ok(index)
}

/// Validate the side conditions and collect the qualifying cells.
///
/// Walks the whole DAG reachable from `assertions`. Every array-sorted term
/// must be a declared symbol of a supported sort, and must occur ONLY as
/// `args[0]` of a `select`. Any other shape is an abstention, never a guess.
fn plan_cells(terms: &TermStore, assertions: &[TermId]) -> Result<CellScan, FlattenAbstain> {
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut state = ScanState {
        cells: Vec::new(),
        reads: Vec::new(),
        cell_index: HashMap::default(),
    };
    let mut saw_array = false;

    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if matches!(terms.sort(term), Sort::Array(_)) {
            // An array-sorted term reached NOT through the `select` arm below,
            // i.e. used in a position that can observe cells other than the
            // eliminated ones (array `=`/`distinct`/`ite`, a UF argument, a
            // `store` base). The backward direction of the equivalence needs
            // the array to be unobservable off the eliminated cells, so refuse.
            let sort = terms.sort(term).clone();
            if !is_eliminable_array(&sort) {
                return Err(FlattenAbstain::ArraySortUnsupported);
            }
            if !matches!(terms.get(term), TermData::Var(_, _)) {
                return Err(FlattenAbstain::ArrayTermNotSymbol);
            }
            return Err(FlattenAbstain::ArrayNotOnlySelected);
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                if sym.name() == "store" {
                    return Err(FlattenAbstain::Store);
                }
                if let Some((array, index)) = as_select(terms, term) {
                    saw_array = true;
                    stack.push(scan_select(terms, term, array, index, &mut state)?);
                    continue;
                }
                stack.extend_from_slice(args);
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                if !bindings.is_empty() {
                    return Err(FlattenAbstain::LetBinding);
                }
                stack.push(*body);
            }
            TermData::Forall(..) | TermData::Exists(..) => {
                return Err(FlattenAbstain::Quantifier);
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            // `TermData` is `#[non_exhaustive]`: an unclassified future variant
            // could hide an array occurrence, so refuse rather than guess.
            _ => return Err(FlattenAbstain::ArrayTermNotSymbol),
        }
    }

    if !saw_array || state.cells.is_empty() {
        return Err(FlattenAbstain::NoArrays);
    }
    Ok(CellScan {
        cells: state.cells,
        reads: state.reads,
    })
}

/// Build the flattening plan for `assertions`, or say why not.
///
/// Verdict-neutral on `Err`: the caller leaves `ctx.assertions` untouched and
/// behaves exactly as before this pass existed.
pub(super) fn plan(
    terms: &mut TermStore,
    assertions: &[TermId],
) -> Result<FlattenPlan, FlattenAbstain> {
    let scan = plan_cells(terms, assertions)?;

    let mut cells: Vec<FlatCell> = Vec::with_capacity(scan.cells.len());
    for (array, cell_key, index_term) in scan.cells {
        let Sort::Array(arr) = terms.sort(array).clone() else {
            return Err(FlattenAbstain::ArraySortUnsupported);
        };
        // Name the cell constant by the array's INTERNED TERM ID, not by its
        // visible name: two distinct array symbols may share a user-facing name
        // (`mk_fresh_named_var` after a `pop`), and keying by name would alias
        // two independent arrays into one variable — a false `sat`. The `__ay_`
        // prefix cannot collide with a user symbol (the frontend rejects it).
        //
        // A symbolic cell is named by the index TERM ID for the same reason: two
        // different index terms are different cells until a congruence axiom
        // relates them, and sharing a name would silently merge them.
        let (name, index_value) = match &cell_key {
            CellKey::Literal(v) => (
                format!("__ay_arrflat!{}_{}", array.index(), v),
                Some(v.clone()),
            ),
            CellKey::Symbolic(i) => (
                format!("__ay_arrflat!{}_t{}", array.index(), i.index()),
                None,
            ),
        };
        // `mk_var` returns the EXISTING term when name+sort already exist, which
        // makes the pass idempotent across repeated `check-sat` calls.
        let fresh = terms.mk_var(name, arr.element_sort.clone());
        cells.push(FlatCell {
            array,
            index_value,
            index_term,
            fresh,
        });
    }

    let mut subst: HashMap<TermId, TermId> = HashMap::default();
    for (select_term, slot) in scan.reads {
        subst.insert(select_term, cells[slot].fresh);
    }

    let mut memo: HashMap<TermId, TermId> = HashMap::default();
    let mut rewritten: Vec<TermId> = assertions
        .iter()
        .map(|&a| rewrite(terms, a, &subst, &mut memo))
        .collect();

    // The congruence closure that makes symbolic indices exact. See the module
    // docs: WITHOUT these the cells are independent variables and a model may
    // set `i = j` while `r_i != r_j`, which is an array that is not a function
    // — a false `sat`. They are appended AFTER the rewrite so they cannot be
    // rewritten themselves (their `select`s were never there to begin with).
    let axioms = congruence_axioms(terms, &cells)?;
    rewritten.extend(axioms);

    if !is_array_free(terms, &rewritten) {
        return Err(FlattenAbstain::ResidualArray);
    }
    Ok(FlattenPlan {
        assertions: rewritten,
        cells,
    })
}

/// Ackermann congruence axioms: `(=> (= i j) (= r_i r_j))` for every pair of
/// distinct cells on the SAME array.
///
/// Two LITERAL cells are skipped: distinct literal keys have distinct numeric
/// values, so `(= i j)` is `false` and the implication is a tautology. Every
/// other pair — symbolic/symbolic and symbolic/literal — gets an axiom.
///
/// Returns [`FlattenAbstain::TooManyReadPairs`] rather than a truncated list.
/// A PREFIX of these axioms is not a weaker-but-sound encoding: the omitted
/// pairs are exactly the ones left free to disagree, so truncation is a
#[cfg(test)]
mod tests;
