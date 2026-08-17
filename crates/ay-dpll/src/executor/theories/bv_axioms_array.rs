// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array-related BV axiom generation for combined theories (ABV, AUFBV).
//!
//! Generates array read-over-write (ROW) and functional consistency axioms
//! as CNF clauses for eager bit-blasting combined theory solving.
//! Uses normalized BV index keys to detect semantically equal indices.
//!
//! Split from `bv_axioms.rs` for code health (#7006, #5970).

// #8529: Use deterministic hash maps in all builds.
use ay_bv::BvSolver;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::collections::BTreeMap;

use super::super::Executor;
use super::ArrayAxiomResult;

fn debug_abv_packed_lookup() -> bool {
    ay_core::misc_cli_flags().debug_abv_packed_lookup
}

/// Read an eager array functional-consistency (FC) pair budget from `name`,
/// falling back to `default`. Lowering a budget sheds eager FC clauses to the
/// lazy Phase 10.7 CEGAR loop (#dt-array-fc-lazy) — sound either way (FC axioms
/// are theory tautologies; the lazy loop refines on demand and fail-closes to
/// Unknown on exhaustion).
fn fc_budget_env(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .unwrap_or(default)
}

const PACKED_MUX_BRIDGE_CANDIDATE_LIMIT: usize = 50_000;
const PACKED_MUX_BRIDGE_CLAUSE_LIMIT: usize = 100_000;

#[derive(Clone, Debug)]
struct PackedArrayWord {
    array: TermId,
    index_width: u32,
    elem_width: u32,
    lane_selects: Vec<TermId>,
}

#[derive(Clone, Debug)]
struct PackedLeafBit {
    array: TermId,
    index_width: u32,
    elem_width: u32,
    lane: usize,
    bit_pos: usize,
    lane_select: TermId,
}

#[derive(Clone, Debug)]
struct MuxBitGuard {
    source: TermId,
    bit_pos: u32,
    bit_term: TermId,
    want_one: bool,
}

#[derive(Clone, Debug)]
struct MuxEqConstGuard {
    index: TermId,
    width: u32,
    value: BigInt,
    cond: TermId,
    cond_is_true: bool,
}

#[derive(Clone, Debug)]
struct MuxTargetCoverage {
    source: TermId,
    target_bit: i32,
    symbolic_bit: i32,
    index_width: u32,
    lanes_mask: u128,
}

#[derive(Clone, Debug)]
struct MuxOutputLeafBridge {
    bit_guards: Vec<MuxBitGuard>,
    eq_guards: Vec<MuxEqConstGuard>,
    output: TermId,
    leaf: PackedLeafBit,
}

#[derive(Clone, Debug)]
struct MuxOutputTermCoverage {
    source: TermId,
    output_width: u32,
    index_width: u32,
    bit_lane_masks: Vec<u128>,
}

#[derive(Default)]
struct PackedMuxPreDebugStats {
    positive_eqs: usize,
    wide_width_pairs: usize,
    concat_attempts: usize,
    concat_flat_bit_ok: usize,
    bit_ite_nodes: usize,
    bit_ite_parsed_true: usize,
    bit_ite_parsed_false: usize,
    bit_ite_unparsed: usize,
    packed_leaf_hits: usize,
    dead_bit_leaves: usize,
    sample_unparsed_ite: Option<TermId>,
    sample_dead_leaf: Option<TermId>,
}

#[derive(Clone, Debug)]
struct PackedWordSlice {
    word: TermId,
    array: TermId,
    index_width: u32,
    elem_width: u32,
    lane: usize,
    lane_select: TermId,
}

fn offset_bv_bit(bit: i32, bv_offset: u32) -> i32 {
    if bit > 0 {
        bit + bv_offset as i32
    } else {
        bit - bv_offset as i32
    }
}

fn push_guarded_bit_eq(
    result: &mut ArrayAxiomResult,
    bv_offset: u32,
    guard_neg_lits: &[i32],
    lhs_bit: i32,
    rhs_bit: i32,
    emitted_clauses: &mut usize,
) {
    let ob_lhs = offset_bv_bit(lhs_bit, bv_offset);
    let ob_rhs = offset_bv_bit(rhs_bit, bv_offset);

    let mut clause = guard_neg_lits.to_vec();
    clause.push(-ob_lhs);
    clause.push(ob_rhs);
    result.clauses.push(ay_core::CnfClause::new(clause));
    *emitted_clauses += 1;

    let mut clause = guard_neg_lits.to_vec();
    clause.push(ob_lhs);
    clause.push(-ob_rhs);
    result.clauses.push(ay_core::CnfClause::new(clause));
    *emitted_clauses += 1;
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum NormalizedBvIndexKey {
    Raw(TermId),
    Const {
        width: u32,
        value: BigInt,
    },
    ZeroExtend {
        extra_bits: u32,
        inner: Box<Self>,
    },
    BvAdd {
        width: u32,
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    BvSub {
        width: u32,
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
}

impl NormalizedBvIndexKey {
    /// Check if two normalized index keys are provably distinct.
    ///
    /// Catches the common byte-load pattern: `bvadd(base, 0)` vs
    /// `bvadd(base, 1)` vs `bvadd(base, 2)` etc. — same symbolic base
    /// but different constant offsets.
    fn are_provably_distinct(a: &Self, b: &Self) -> bool {
        match (a, b) {
            // Two different constants at the same width
            (
                Self::Const {
                    width: w1,
                    value: v1,
                },
                Self::Const {
                    width: w2,
                    value: v2,
                },
            ) => w1 == w2 && v1 != v2,

            // base + c1 vs base + c2 where c1 != c2
            (
                Self::BvAdd {
                    width: w1,
                    lhs: l1,
                    rhs: r1,
                },
                Self::BvAdd {
                    width: w2,
                    lhs: l2,
                    rhs: r2,
                },
            ) if w1 == w2 && l1 == l2 => Self::are_provably_distinct(r1, r2),

            // base - c1 vs base - c2 where c1 != c2
            (
                Self::BvSub {
                    width: w1,
                    lhs: l1,
                    rhs: r1,
                },
                Self::BvSub {
                    width: w2,
                    lhs: l2,
                    rhs: r2,
                },
            ) if w1 == w2 && l1 == l2 => Self::are_provably_distinct(r1, r2),

            // base + nonzero_const vs base (after zero-folding, bare base = offset 0)
            (
                Self::BvAdd {
                    lhs, rhs: offset, ..
                },
                other,
            )
            | (
                other,
                Self::BvAdd {
                    lhs, rhs: offset, ..
                },
            ) if lhs.as_ref() == other => {
                matches!(offset.as_ref(), Self::Const { value, .. } if *value != BigInt::from(0u8))
            }

            // base - nonzero_const vs base (symmetric with BvAdd case)
            (
                Self::BvSub {
                    lhs, rhs: offset, ..
                },
                other,
            )
            | (
                other,
                Self::BvSub {
                    lhs, rhs: offset, ..
                },
            ) if lhs.as_ref() == other => {
                matches!(offset.as_ref(), Self::Const { value, .. } if *value != BigInt::from(0u8))
            }

            // base + c vs base - c' where both offsets are constants
            // base + c1 and base - c2 are distinct when c1 + c2 != 0 (mod 2^w)
            // Simplified: always distinct when c1 > 0 and c2 > 0
            (
                Self::BvAdd {
                    width: w1,
                    lhs: l1,
                    rhs: r1,
                },
                Self::BvSub {
                    width: w2,
                    lhs: l2,
                    rhs: r2,
                },
            )
            | (
                Self::BvSub {
                    width: w2,
                    lhs: l2,
                    rhs: r2,
                },
                Self::BvAdd {
                    width: w1,
                    lhs: l1,
                    rhs: r1,
                },
            ) if w1 == w2 && l1 == l2 => {
                match (r1.as_ref(), r2.as_ref()) {
                    (
                        Self::Const {
                            value: v1,
                            width: cw1,
                        },
                        Self::Const {
                            value: v2,
                            width: cw2,
                        },
                    ) if cw1 == cw2 => {
                        // base + v1 vs base - v2 => distinct when v1 + v2 != 0 mod 2^w
                        let sum = v1 + v2;
                        let modulus = BigInt::from(1u8) << *w1;
                        (sum % modulus) != BigInt::from(0u8)
                    }
                    _ => false,
                }
            }

            // ZeroExtend with same extra bits — compare inner keys
            (
                Self::ZeroExtend {
                    extra_bits: e1,
                    inner: i1,
                },
                Self::ZeroExtend {
                    extra_bits: e2,
                    inner: i2,
                },
            ) if e1 == e2 => Self::are_provably_distinct(i1, i2),

            _ => false,
        }
    }

    /// Extract the "symbolic base" of a normalized index key (#8286).
    ///
    /// Used to group indices by their base expression for FC axiom generation.
    /// Indices with different bases are less likely to alias, so FC axioms
    /// between them can be deprioritized when the per-array FC budget is
    /// exhausted.
    ///
    /// Examples:
    /// - `base + 0` → base is `Raw(base_id)`
    /// - `base + 3` → base is `Raw(base_id)`
    /// - `base - 1` → base is `Raw(base_id)`
    /// - `x` (raw variable) → base is `Raw(x_id)`
    /// - `#x05` (constant) → base is `None` (constants are their own group)
    /// - `zext(inner + c)` → base is the base of `inner + c`
    fn symbolic_base(&self) -> Option<&Self> {
        match self {
            Self::Const { .. } => None, // Constants form their own equivalence class
            Self::Raw(_) => Some(self),
            Self::BvAdd { lhs, .. } | Self::BvSub { lhs, .. } => {
                // For base + offset or base - offset, the base is the lhs
                // after recursing (in case lhs is itself a compound expression)
                match lhs.as_ref() {
                    Self::Const { .. } => Some(self), // const + something: the whole thing is the base
                    _ => lhs.symbolic_base().or(Some(lhs.as_ref())),
                }
            }
            Self::ZeroExtend { inner, .. } => inner.symbolic_base(),
        }
    }

    /// Check if two normalized keys share the same symbolic base (#8286).
    ///
    /// Indices with different bases (e.g., `p0 + 1` vs `p1 + 2`) are unlikely
    /// to be equal unless by coincidence. FC axioms between such pairs are
    /// lower priority than between indices sharing a base (e.g., `p0 + 1` vs
    /// `p0 + 2`, which are only distinct by offset).
    fn shares_base_with(&self, other: &Self) -> bool {
        match (self.symbolic_base(), other.symbolic_base()) {
            (Some(b1), Some(b2)) => b1 == b2,
            (None, None) => true, // Both constants — compare them directly
            _ => false,
        }
    }
}

impl Executor {
    fn collect_all_terms(
        &self,
        term: TermId,
        terms: &mut Vec<TermId>,
        visited: &mut HashSet<TermId>,
    ) {
        if !visited.insert(term) {
            return;
        }
        terms.push(term);
        for child in self.ctx.terms.children(term) {
            self.collect_all_terms(child, terms, visited);
        }
    }

    fn term_contains(&self, root: TermId, needle: TermId) -> bool {
        if root == needle {
            return true;
        }
        self.ctx
            .terms
            .children(root)
            .iter()
            .copied()
            .any(|child| self.term_contains(child, needle))
    }

    fn ite_parts(&self, term: TermId) -> Option<(TermId, TermId, TermId)> {
        match self.ctx.terms.get(term) {
            TermData::Ite(cond, then_term, else_term) => Some((*cond, *then_term, *else_term)),
            TermData::App(sym, args) if sym.name() == "ite" && args.len() == 3 => {
                Some((args[0], args[1], args[2]))
            }
            _ => None,
        }
    }

    fn flatten_concat_high_to_low(&self, term: TermId, leaves: &mut Vec<TermId>) {
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "concat" && args.len() == 2 => {
                self.flatten_concat_high_to_low(args[0], leaves);
                self.flatten_concat_high_to_low(args[1], leaves);
            }
            _ => leaves.push(term),
        }
    }

    fn flatten_concat_high_to_low_with_definitions(
        &self,
        term: TermId,
        definitions: Option<&HashMap<TermId, TermId>>,
        leaves: &mut Vec<TermId>,
        seen: &mut HashSet<TermId>,
    ) {
        let term = self.resolve_positive_bv_definition(term, definitions);
        if !seen.insert(term) {
            leaves.push(term);
            return;
        }
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "concat" && args.len() == 2 => {
                self.flatten_concat_high_to_low_with_definitions(
                    args[0],
                    definitions,
                    leaves,
                    seen,
                );
                self.flatten_concat_high_to_low_with_definitions(
                    args[1],
                    definitions,
                    leaves,
                    seen,
                );
            }
            _ => leaves.push(term),
        }
        seen.remove(&term);
    }

    fn bv_const_value(&self, term: TermId) -> Option<(u32, BigInt)> {
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::BitVec { value, width }) => {
                Some((*width, Self::normalize_bv_const(value, *width)))
            }
            _ => None,
        }
    }

    fn bv_const_value_with_definitions(
        &self,
        term: TermId,
        definitions: Option<&HashMap<TermId, TermId>>,
    ) -> Option<(u32, BigInt)> {
        self.bv_const_value_with_definitions_inner(term, definitions, &mut HashSet::default())
    }

    fn bv_const_value_with_definitions_inner(
        &self,
        term: TermId,
        definitions: Option<&HashMap<TermId, TermId>>,
        seen: &mut HashSet<TermId>,
    ) -> Option<(u32, BigInt)> {
        let term = self.resolve_positive_bv_definition(term, definitions);
        if !seen.insert(term) {
            return None;
        }

        let result = (|| match self.ctx.terms.get(term) {
            TermData::Const(Constant::BitVec { value, width }) => {
                Some((*width, Self::normalize_bv_const(value, *width)))
            }
            TermData::App(sym, args) if sym.name() == "zero_extend" && args.len() == 1 => {
                let (_arg_width, value) =
                    self.bv_const_value_with_definitions_inner(args[0], definitions, seen)?;
                let width = self.bitvec_width(term)?;
                Some((width, Self::normalize_bv_const(&value, width)))
            }
            TermData::App(sym, args) if sym.name() == "bvneg" && args.len() == 1 => {
                let (_arg_width, value) =
                    self.bv_const_value_with_definitions_inner(args[0], definitions, seen)?;
                let width = self.bitvec_width(term)?;
                Some((width, Self::normalize_bv_const(&(-value), width)))
            }
            TermData::App(sym, args) if sym.name() == "bvnot" && args.len() == 1 => {
                let (_arg_width, value) =
                    self.bv_const_value_with_definitions_inner(args[0], definitions, seen)?;
                let width = self.bitvec_width(term)?;
                let mask = (BigInt::from(1u8) << width) - BigInt::from(1u8);
                Some((width, Self::normalize_bv_const(&(mask - value), width)))
            }
            TermData::App(sym, args) if sym.name() == "concat" && args.len() == 2 => {
                let (hi_width, hi_value) =
                    self.bv_const_value_with_definitions_inner(args[0], definitions, seen)?;
                let (lo_width, lo_value) =
                    self.bv_const_value_with_definitions_inner(args[1], definitions, seen)?;
                let width = hi_width.checked_add(lo_width)?;
                Some((
                    width,
                    Self::normalize_bv_const(&((hi_value << lo_width) + lo_value), width),
                ))
            }
            _ => None,
        })();

        seen.remove(&term);
        result
    }

    fn strip_zero_extend(&self, mut term: TermId) -> TermId {
        loop {
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) if sym.name() == "zero_extend" && args.len() == 1 => {
                    term = args[0];
                }
                _ => return term,
            }
        }
    }

    fn decode_packed_lookup_index(
        &self,
        shift_term: TermId,
        array_index_width: u32,
    ) -> Option<TermId> {
        let index = self.strip_zero_extend(shift_term);
        if self.bitvec_width(index) == Some(array_index_width) {
            return Some(index);
        }
        None
    }

    fn detect_packed_array_lookup(&self, term: TermId) -> Option<(TermId, TermId, Vec<TermId>)> {
        let TermData::App(extract_sym, extract_args) = self.ctx.terms.get(term) else {
            return None;
        };
        if extract_sym.name() != "extract" || extract_args.len() != 1 {
            return None;
        }
        let Symbol::Indexed(_, extract_indices) = extract_sym else {
            return None;
        };
        if extract_indices.len() != 2 || extract_indices[1] != 0 {
            return None;
        }

        let TermData::App(shift_sym, shift_args) = self.ctx.terms.get(extract_args[0]) else {
            return None;
        };
        if shift_sym.name() != "bvlshr" || shift_args.len() != 2 {
            return None;
        }

        let mut leaves = Vec::new();
        self.flatten_concat_high_to_low(shift_args[0], &mut leaves);
        if leaves.len() < 2 {
            return None;
        }

        let mut array = None;
        let mut lane_selects = vec![None; leaves.len()];
        let mut elem_width = None;
        let mut index_width = None;

        for (pos, &leaf) in leaves.iter().enumerate() {
            let TermData::App(sel_sym, sel_args) = self.ctx.terms.get(leaf) else {
                return None;
            };
            if sel_sym.name() != "select" || sel_args.len() != 2 {
                return None;
            }
            let leaf_array = sel_args[0];
            if let Some(expected_array) = array {
                if expected_array != leaf_array {
                    return None;
                }
            } else {
                let Sort::Array(arr_sort) = self.ctx.terms.sort(leaf_array) else {
                    return None;
                };
                let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
                    return None;
                };
                index_width = Some(idx_bv.width);
                array = Some(leaf_array);
            }

            let Sort::BitVec(value_bv) = self.ctx.terms.sort(leaf) else {
                return None;
            };
            if let Some(width) = elem_width {
                if width != value_bv.width {
                    return None;
                }
            } else {
                elem_width = Some(value_bv.width);
            }

            let (const_width, const_value) = self.bv_const_value(sel_args[1])?;
            let index_width = index_width?;
            if const_width != index_width {
                return None;
            }
            let lane = leaves.len() - 1 - pos;
            if const_value != BigInt::from(lane) {
                return None;
            }
            lane_selects[lane] = Some(leaf);
        }

        let elem_width = elem_width?;
        if extract_indices[0] + 1 != elem_width {
            return None;
        }
        let array = array?;
        let index = self.decode_packed_lookup_index(shift_args[1], index_width?)?;
        let lane_selects = lane_selects.into_iter().collect::<Option<Vec<_>>>()?;
        Some((array, index, lane_selects))
    }

    fn detect_packed_array_shift_lookup(
        &self,
        term: TermId,
    ) -> Option<(TermId, TermId, Vec<TermId>)> {
        let TermData::App(shift_sym, shift_args) = self.ctx.terms.get(term) else {
            return None;
        };
        if shift_sym.name() != "bvlshr" || shift_args.len() != 2 {
            return None;
        }

        let mut leaves = Vec::new();
        self.flatten_concat_high_to_low(shift_args[0], &mut leaves);
        if leaves.len() < 2 {
            return None;
        }

        let mut array = None;
        let mut lane_selects = vec![None; leaves.len()];
        let mut index_width = None;

        for (pos, &leaf) in leaves.iter().enumerate() {
            let TermData::App(sel_sym, sel_args) = self.ctx.terms.get(leaf) else {
                return None;
            };
            if sel_sym.name() != "select" || sel_args.len() != 2 {
                return None;
            }
            let leaf_array = sel_args[0];
            if let Some(expected_array) = array {
                if expected_array != leaf_array {
                    return None;
                }
            } else {
                let Sort::Array(arr_sort) = self.ctx.terms.sort(leaf_array) else {
                    return None;
                };
                let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
                    return None;
                };
                index_width = Some(idx_bv.width);
                array = Some(leaf_array);
            }

            let (const_width, const_value) = self.bv_const_value(sel_args[1])?;
            let index_width = index_width?;
            if const_width != index_width {
                return None;
            }
            let lane = leaves.len() - 1 - pos;
            if const_value != BigInt::from(lane) {
                return None;
            }
            lane_selects[lane] = Some(leaf);
        }

        let array = array?;
        let index = self.decode_packed_lookup_index(shift_args[1], index_width?)?;
        let lane_selects = lane_selects.into_iter().collect::<Option<Vec<_>>>()?;
        Some((array, index, lane_selects))
    }

    fn detect_packed_array_word(&self, term: TermId) -> Option<PackedArrayWord> {
        let mut leaves = Vec::new();
        self.flatten_concat_high_to_low(term, &mut leaves);
        if leaves.len() < 2 {
            return None;
        }

        let mut array = None;
        let mut lane_selects = vec![None; leaves.len()];
        let mut elem_width = None;
        let mut index_width = None;

        for (pos, &leaf) in leaves.iter().enumerate() {
            let TermData::App(sel_sym, sel_args) = self.ctx.terms.get(leaf) else {
                return None;
            };
            if sel_sym.name() != "select" || sel_args.len() != 2 {
                return None;
            }

            let leaf_array = sel_args[0];
            if let Some(expected_array) = array {
                if expected_array != leaf_array {
                    return None;
                }
            } else {
                let Sort::Array(arr_sort) = self.ctx.terms.sort(leaf_array) else {
                    return None;
                };
                let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
                    return None;
                };
                index_width = Some(idx_bv.width);
                array = Some(leaf_array);
            }

            let Sort::BitVec(value_bv) = self.ctx.terms.sort(leaf) else {
                return None;
            };
            if let Some(width) = elem_width {
                if width != value_bv.width {
                    return None;
                }
            } else {
                elem_width = Some(value_bv.width);
            }

            let (const_width, const_value) = self.bv_const_value(sel_args[1])?;
            let index_width = index_width?;
            if const_width != index_width {
                return None;
            }
            let lane = leaves.len() - 1 - pos;
            if const_value != BigInt::from(lane) {
                return None;
            }
            lane_selects[lane] = Some(leaf);
        }

        let elem_width = elem_width?;
        if self.bitvec_width(term)? != elem_width.saturating_mul(leaves.len() as u32) {
            return None;
        }

        Some(PackedArrayWord {
            array: array?,
            index_width: index_width?,
            elem_width,
            lane_selects: lane_selects.into_iter().collect::<Option<Vec<_>>>()?,
        })
    }

    fn collect_positive_equality_facts(&self, term: TermId, out: &mut Vec<TermId>) {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return;
        };
        match sym.name() {
            "=" if args.len() == 2 => out.push(term),
            "and" => {
                for &arg in args {
                    self.collect_positive_equality_facts(arg, out);
                }
            }
            _ => {}
        }
    }

    fn positive_bool_definition_side(&self, term: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        for (var, replacement) in [(args[0], args[1]), (args[1], args[0])] {
            if matches!(self.ctx.terms.get(var), TermData::Var(_, _))
                && matches!(self.ctx.terms.sort(var), Sort::Bool)
                && matches!(self.ctx.terms.sort(replacement), Sort::Bool)
                && !self.term_contains(replacement, var)
            {
                return Some((var, replacement));
            }
        }
        None
    }

    fn insert_positive_bv_definition(
        &self,
        out: &mut HashMap<TermId, TermId>,
        var: TermId,
        replacement: TermId,
    ) {
        let replacement_is_var = matches!(self.ctx.terms.get(replacement), TermData::Var(_, _));
        if replacement_is_var {
            out.entry(var).or_insert(replacement);
            return;
        }

        let should_insert = match out.get(&var) {
            Some(&existing) => matches!(self.ctx.terms.get(existing), TermData::Var(_, _)),
            None => true,
        };
        if should_insert {
            out.insert(var, replacement);
        }
    }

    fn build_positive_bool_definitions(&self) -> HashMap<TermId, TermId> {
        let mut equality_facts = Vec::new();
        for &assertion in &self.ctx.assertions {
            self.collect_positive_equality_facts(assertion, &mut equality_facts);
        }

        let mut definitions = HashMap::default();
        for fact in equality_facts {
            if let Some((var, replacement)) = self.positive_bool_definition_side(fact) {
                definitions.entry(var).or_insert(replacement);
            }
        }
        definitions
    }

    fn collect_positive_bv_var_definitions(
        &mut self,
        term: TermId,
        out: &mut HashMap<TermId, TermId>,
    ) {
        if let Some((cond, then_term, else_term)) = self.ite_parts(term) {
            if let Some((var, then_value, else_value)) =
                self.same_var_bv_branch_equalities(then_term, else_term)
            {
                if !self.term_contains(then_value, var) && !self.term_contains(else_value, var) {
                    let replacement = self.ctx.terms.mk_ite(cond, then_value, else_value);
                    self.insert_positive_bv_definition(out, var, replacement);
                }
            }
            return;
        }

        let TermData::App(sym, args) = self.ctx.terms.get(term).clone() else {
            return;
        };
        match sym.name() {
            "=" if args.len() == 2 => {
                for (var, replacement) in [(args[0], args[1]), (args[1], args[0])] {
                    if matches!(self.ctx.terms.get(var), TermData::Var(_, _))
                        && self.bitvec_width(var).is_some()
                        && self.bitvec_width(var) == self.bitvec_width_for_definition(replacement)
                        && !self.term_contains(replacement, var)
                    {
                        self.insert_positive_bv_definition(out, var, replacement);
                    }
                }
            }
            "and" => {
                for arg in args {
                    self.collect_positive_bv_var_definitions(arg, out);
                }
            }
            _ => {}
        }
    }

    fn same_var_bv_branch_equalities(
        &self,
        then_term: TermId,
        else_term: TermId,
    ) -> Option<(TermId, TermId, TermId)> {
        let then_eq = self.bv_var_equality_side(then_term)?;
        let else_eq = self.bv_var_equality_side(else_term)?;
        if then_eq.0 != else_eq.0 {
            return None;
        }
        if self.bitvec_width_for_definition(then_eq.1)
            != self.bitvec_width_for_definition(else_eq.1)
        {
            return None;
        }
        Some((then_eq.0, then_eq.1, else_eq.1))
    }

    fn bv_var_equality_side(&self, term: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        for (var, value) in [(args[0], args[1]), (args[1], args[0])] {
            if matches!(self.ctx.terms.get(var), TermData::Var(_, _))
                && self.bitvec_width(var).is_some()
                && self.bitvec_width(var) == self.bitvec_width_for_definition(value)
            {
                return Some((var, value));
            }
        }
        None
    }

    fn collect_positive_fact_terms(
        &self,
        term: TermId,
        bool_definitions: &HashMap<TermId, TermId>,
        seen_bool_defs: &mut HashSet<TermId>,
        out: &mut Vec<TermId>,
    ) {
        if matches!(self.ctx.terms.get(term), TermData::Var(_, _))
            && matches!(self.ctx.terms.sort(term), Sort::Bool)
        {
            if let Some(&replacement) = bool_definitions.get(&term) {
                if seen_bool_defs.insert(term) {
                    self.collect_positive_fact_terms(
                        replacement,
                        bool_definitions,
                        seen_bool_defs,
                        out,
                    );
                    seen_bool_defs.remove(&term);
                    return;
                }
            }
        }

        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            out.push(term);
            return;
        };
        match sym.name() {
            "and" => {
                for &arg in args {
                    self.collect_positive_fact_terms(arg, bool_definitions, seen_bool_defs, out);
                }
            }
            "not" if args.len() == 1 => {
                let TermData::App(inner_sym, inner_args) = self.ctx.terms.get(args[0]) else {
                    out.push(term);
                    return;
                };
                match inner_sym.name() {
                    "=>" if inner_args.len() == 2 => {
                        self.collect_positive_fact_terms(
                            inner_args[0],
                            bool_definitions,
                            seen_bool_defs,
                            out,
                        );
                    }
                    "not" if inner_args.len() == 1 => {
                        self.collect_positive_fact_terms(
                            inner_args[0],
                            bool_definitions,
                            seen_bool_defs,
                            out,
                        );
                    }
                    _ => out.push(term),
                }
            }
            _ => out.push(term),
        }
    }

    fn build_nonnegative_upper_bounds(&self) -> HashMap<TermId, usize> {
        let bool_definitions = self.build_positive_bool_definitions();
        let mut positive_facts = Vec::new();
        for &assertion in &self.ctx.assertions {
            self.collect_positive_fact_terms(
                assertion,
                &bool_definitions,
                &mut HashSet::default(),
                &mut positive_facts,
            );
        }

        let mut signed_nonnegative = HashSet::default();
        let mut signed_upper: HashMap<TermId, usize> = HashMap::default();
        let mut unsigned_upper: HashMap<TermId, usize> = HashMap::default();

        for fact in positive_facts {
            let TermData::App(sym, args) = self.ctx.terms.get(fact) else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }

            match sym.name() {
                "bvsle" => {
                    if let Some((zero_width, zero_value)) = self.bv_const_value(args[0]) {
                        if zero_value == BigInt::from(0u8)
                            && self.bitvec_width(args[1]) == Some(zero_width)
                        {
                            signed_nonnegative.insert(args[1]);
                        }
                    }

                    let Some(source_width) = self.bitvec_width(args[0]) else {
                        continue;
                    };
                    let Some((const_width, value)) = self.bv_const_value(args[1]) else {
                        continue;
                    };
                    if source_width != const_width || value < BigInt::from(0u8) {
                        continue;
                    }
                    let signed_positive_limit = BigInt::from(1u8) << (source_width - 1);
                    if value >= signed_positive_limit {
                        continue;
                    }
                    let Some(value) = value.to_usize() else {
                        continue;
                    };
                    signed_upper
                        .entry(args[0])
                        .and_modify(|existing| *existing = (*existing).min(value))
                        .or_insert(value);
                }
                "bvule" => {
                    let Some(source_width) = self.bitvec_width(args[0]) else {
                        continue;
                    };
                    let Some((const_width, value)) = self.bv_const_value(args[1]) else {
                        continue;
                    };
                    if source_width != const_width {
                        continue;
                    }
                    let Some(value) = value.to_usize() else {
                        continue;
                    };
                    unsigned_upper
                        .entry(args[0])
                        .and_modify(|existing| *existing = (*existing).min(value))
                        .or_insert(value);
                }
                _ => {}
            }
        }

        for (source, upper) in signed_upper {
            if signed_nonnegative.contains(&source) {
                unsigned_upper
                    .entry(source)
                    .and_modify(|existing| *existing = (*existing).min(upper))
                    .or_insert(upper);
            }
        }

        unsigned_upper
    }

    fn build_packed_array_word_map(
        &self,
        all_terms: &[TermId],
    ) -> HashMap<TermId, PackedArrayWord> {
        let mut words = HashMap::default();
        for &term in all_terms {
            if let Some(word) = self.detect_packed_array_word(term) {
                words.insert(term, word);
            }
        }

        let mut equality_facts = Vec::new();
        for &assertion in &self.ctx.assertions {
            self.collect_positive_equality_facts(assertion, &mut equality_facts);
        }

        for &root in &equality_facts {
            let TermData::App(sym, args) = self.ctx.terms.get(root) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }

            for (alias, packed) in [(args[0], args[1]), (args[1], args[0])] {
                if !matches!(self.ctx.terms.get(alias), TermData::Var(_, _)) {
                    continue;
                }
                let Some(word) = words
                    .get(&packed)
                    .cloned()
                    .or_else(|| self.detect_packed_array_word(packed))
                else {
                    continue;
                };
                if self.bitvec_width(alias) == self.bitvec_width(packed) {
                    words.insert(alias, word);
                }
            }
        }

        let mut sliced_words: HashMap<TermId, (TermId, u32, u32, Vec<Option<TermId>>)> =
            HashMap::default();
        let mut invalid_sliced_words: HashSet<TermId> = HashSet::default();
        for &term in &equality_facts {
            let Some(slice) = self.detect_packed_word_slice_eq(term) else {
                continue;
            };
            if invalid_sliced_words.contains(&slice.word) {
                continue;
            }
            let Some(word_width) = self.bitvec_width(slice.word) else {
                continue;
            };
            if slice.elem_width == 0 || word_width % slice.elem_width != 0 {
                continue;
            }
            let expected_lanes = (word_width / slice.elem_width) as usize;
            let entry = sliced_words.entry(slice.word).or_insert_with(|| {
                (
                    slice.array,
                    slice.index_width,
                    slice.elem_width,
                    vec![None; expected_lanes],
                )
            });
            if entry.0 != slice.array
                || entry.1 != slice.index_width
                || entry.2 != slice.elem_width
                || entry.3.len() != expected_lanes
            {
                invalid_sliced_words.insert(slice.word);
                sliced_words.remove(&slice.word);
                continue;
            }
            if let Some(slot) = entry.3.get_mut(slice.lane) {
                if slot.is_some_and(|existing| existing != slice.lane_select) {
                    invalid_sliced_words.insert(slice.word);
                    sliced_words.remove(&slice.word);
                    continue;
                }
                *slot = Some(slice.lane_select);
            }
        }

        for (word, (array, index_width, elem_width, lane_selects)) in sliced_words {
            if invalid_sliced_words.contains(&word) {
                continue;
            }
            let Some(lane_selects) = lane_selects.into_iter().collect::<Option<Vec<_>>>() else {
                continue;
            };
            if lane_selects.len() < 2 {
                continue;
            }
            words.insert(
                word,
                PackedArrayWord {
                    array,
                    index_width,
                    elem_width,
                    lane_selects,
                },
            );
        }

        words
    }

    fn single_bit_extract(&self, term: TermId) -> Option<(TermId, u32)> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "extract" || args.len() != 1 {
            return None;
        }
        let Symbol::Indexed(_, indices) = sym else {
            return None;
        };
        if indices.len() != 2 || indices[0] != indices[1] {
            return None;
        }
        Some((args[0], indices[0]))
    }

    fn slice_extract(&self, term: TermId) -> Option<(TermId, u32, u32)> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "extract" || args.len() != 1 {
            return None;
        }
        let Symbol::Indexed(_, indices) = sym else {
            return None;
        };
        if indices.len() != 2 || indices[0] < indices[1] {
            return None;
        }
        Some((args[0], indices[0], indices[1]))
    }

    fn detect_constant_array_select(&self, term: TermId) -> Option<(TermId, u32, u32, usize)> {
        let TermData::App(sel_sym, sel_args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sel_sym.name() != "select" || sel_args.len() != 2 {
            return None;
        }
        let Sort::Array(arr_sort) = self.ctx.terms.sort(sel_args[0]) else {
            return None;
        };
        let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
            return None;
        };
        let Sort::BitVec(value_bv) = self.ctx.terms.sort(term) else {
            return None;
        };
        let (const_width, const_value) = self.bv_const_value(sel_args[1])?;
        if const_width != idx_bv.width {
            return None;
        }
        Some((
            sel_args[0],
            idx_bv.width,
            value_bv.width,
            const_value.to_usize()?,
        ))
    }

    fn detect_packed_word_slice_eq(&self, term: TermId) -> Option<PackedWordSlice> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }

        for (select_term, slice_term) in [(args[0], args[1]), (args[1], args[0])] {
            let (array, index_width, elem_width, lane) =
                self.detect_constant_array_select(select_term)?;
            let (word, hi, lo) = self.slice_extract(slice_term)?;
            if hi + 1 - lo != elem_width {
                continue;
            }
            let Some(word_width) = self.bitvec_width(word) else {
                continue;
            };
            if elem_width == 0 || word_width % elem_width != 0 {
                continue;
            }
            let expected_lanes = (word_width / elem_width) as usize;
            if lane >= expected_lanes {
                continue;
            }
            if lo != elem_width.saturating_mul(lane as u32)
                || hi + 1 != elem_width.saturating_mul(lane as u32 + 1)
            {
                continue;
            }
            return Some(PackedWordSlice {
                word,
                array,
                index_width,
                elem_width,
                lane,
                lane_select: select_term,
            });
        }

        None
    }

    fn detect_constant_select_leaf_bit_with_definitions(
        &self,
        term: TermId,
        definitions: Option<&HashMap<TermId, TermId>>,
    ) -> Option<PackedLeafBit> {
        let term = self.resolve_positive_bv_definition(term, definitions);
        let (inner, bit_pos) = self.single_bit_extract(term)?;
        let inner = self.resolve_positive_bv_definition(inner, definitions);
        let TermData::App(sel_sym, sel_args) = self.ctx.terms.get(inner) else {
            return None;
        };
        if sel_sym.name() != "select" || sel_args.len() != 2 {
            return None;
        }
        let Sort::Array(arr_sort) = self.ctx.terms.sort(sel_args[0]) else {
            return None;
        };
        let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
            return None;
        };
        let Sort::BitVec(value_bv) = self.ctx.terms.sort(inner) else {
            return None;
        };
        if bit_pos >= value_bv.width {
            return None;
        }

        let (const_width, const_value) = self.bv_const_value(sel_args[1])?;
        if const_width != idx_bv.width {
            return None;
        }
        let lane = const_value.to_usize()?;
        Some(PackedLeafBit {
            array: sel_args[0],
            index_width: idx_bv.width,
            elem_width: value_bv.width,
            lane,
            bit_pos: bit_pos as usize,
            lane_select: inner,
        })
    }

    fn detect_packed_leaf_bit_with_definitions(
        &self,
        term: TermId,
        packed_words: &HashMap<TermId, PackedArrayWord>,
        definitions: Option<&HashMap<TermId, TermId>>,
    ) -> Option<PackedLeafBit> {
        let term = self.resolve_positive_bv_definition(term, definitions);
        if let Some(leaf) = self.detect_constant_select_leaf_bit_with_definitions(term, definitions)
        {
            return Some(leaf);
        }

        let (inner, packed_bit) = self.single_bit_extract(term)?;
        let (inner, packed_bit) =
            self.resolve_constant_lshr_bit_source(inner, packed_bit, definitions)?;
        let word = packed_words.get(&inner)?;
        if word.elem_width == 0 {
            return None;
        }
        let lane = (packed_bit / word.elem_width) as usize;
        let bit_pos = (packed_bit % word.elem_width) as usize;
        let lane_select = *word.lane_selects.get(lane)?;
        Some(PackedLeafBit {
            array: word.array,
            index_width: word.index_width,
            elem_width: word.elem_width,
            lane,
            bit_pos,
            lane_select,
        })
    }

    fn detect_packed_leaf_value_bits(
        &self,
        term: TermId,
        packed_words: &HashMap<TermId, PackedArrayWord>,
    ) -> Option<Vec<PackedLeafBit>> {
        if let Some((array, index_width, elem_width, lane)) =
            self.detect_constant_array_select(term)
        {
            if elem_width == 0 {
                return None;
            }
            return Some(
                (0..elem_width as usize)
                    .map(|bit_pos| PackedLeafBit {
                        array,
                        index_width,
                        elem_width,
                        lane,
                        bit_pos,
                        lane_select: term,
                    })
                    .collect(),
            );
        }

        let (word_term, hi, lo) = self.slice_extract(term)?;
        let word = packed_words.get(&word_term)?;
        if word.elem_width == 0 || hi + 1 - lo != word.elem_width {
            return None;
        }
        let lane = (lo / word.elem_width) as usize;
        if lo != word.elem_width.saturating_mul(lane as u32)
            || hi + 1 != word.elem_width.saturating_mul(lane as u32 + 1)
        {
            return None;
        }
        let lane_select = *word.lane_selects.get(lane)?;
        Some(
            (0..word.elem_width as usize)
                .map(|bit_pos| PackedLeafBit {
                    array: word.array,
                    index_width: word.index_width,
                    elem_width: word.elem_width,
                    lane,
                    bit_pos,
                    lane_select,
                })
                .collect(),
        )
    }

    fn resolve_positive_bv_definition(
        &self,
        term: TermId,
        definitions: Option<&HashMap<TermId, TermId>>,
    ) -> TermId {
        let Some(definitions) = definitions else {
            return term;
        };
        let mut current = term;
        let mut seen = HashSet::default();
        while matches!(self.ctx.terms.get(current), TermData::Var(_, _)) && seen.insert(current) {
            let Some(&replacement) = definitions.get(&current) else {
                break;
            };
            current = replacement;
        }
        current
    }

    fn parse_mux_bit_condition_with_definitions(
        &self,
        cond: TermId,
        cond_is_true: bool,
        definitions: Option<&HashMap<TermId, TermId>>,
    ) -> Option<MuxBitGuard> {
        let TermData::App(sym, args) = self.ctx.terms.get(cond) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }

        for (bit_term, const_term) in [(args[0], args[1]), (args[1], args[0])] {
            let bit_term = self.resolve_positive_bv_definition(bit_term, definitions);
            let const_term = self.resolve_positive_bv_definition(const_term, definitions);
            let Some((const_width, const_value)) =
                self.bv_const_value_with_definitions(const_term, definitions)
            else {
                continue;
            };
            if const_width != 1 {
                continue;
            }
            let equals_one = const_value == BigInt::from(1u8);
            let (source, bit_pos) = self.single_bit_extract(bit_term)?;
            let (source, bit_pos) =
                self.resolve_constant_lshr_bit_source(source, bit_pos, definitions)?;
            return Some(MuxBitGuard {
                source,
                bit_pos,
                bit_term,
                want_one: if cond_is_true {
                    equals_one
                } else {
                    !equals_one
                },
            });
        }

        None
    }

    fn resolve_constant_lshr_bit_source(
        &self,
        source: TermId,
        bit_pos: u32,
        definitions: Option<&HashMap<TermId, TermId>>,
    ) -> Option<(TermId, u32)> {
        let mut source = self.resolve_positive_bv_definition(source, definitions);
        let mut bit_pos = bit_pos;
        let mut seen = HashSet::default();

        while seen.insert(source) {
            let TermData::App(sym, args) = self.ctx.terms.get(source) else {
                let source_width = self.bitvec_width(source)?;
                if bit_pos >= source_width {
                    return None;
                }
                return Some((source, bit_pos));
            };
            if sym.name() != "bvlshr" || args.len() != 2 {
                if sym.name() == "zero_extend" && args.len() == 1 {
                    let inner_width = self.bitvec_width(args[0])?;
                    if bit_pos >= inner_width {
                        return None;
                    }
                    source = self.resolve_positive_bv_definition(args[0], definitions);
                    continue;
                }
                if sym.name() == "extract" && args.len() == 1 {
                    let Symbol::Indexed(_, indices) = sym else {
                        return None;
                    };
                    if indices.len() != 2 || indices[0] < indices[1] {
                        return None;
                    }
                    let slice_width = indices[0] + 1 - indices[1];
                    if bit_pos >= slice_width {
                        return None;
                    }
                    bit_pos = bit_pos.checked_add(indices[1])?;
                    source = self.resolve_positive_bv_definition(args[0], definitions);
                    continue;
                }
                let source_width = self.bitvec_width(source)?;
                if bit_pos >= source_width {
                    return None;
                }
                return Some((source, bit_pos));
            }

            let (_shift_width, shift_value) =
                self.bv_const_value_with_definitions(args[1], definitions)?;
            let shift = shift_value.to_u32()?;
            bit_pos = bit_pos.checked_add(shift)?;
            source = self.resolve_positive_bv_definition(args[0], definitions);
        }

        None
    }

    fn parse_mux_const_eq_condition_with_definitions(
        &self,
        cond: TermId,
        cond_is_true: bool,
        definitions: Option<&HashMap<TermId, TermId>>,
    ) -> Option<MuxEqConstGuard> {
        let TermData::App(sym, args) = self.ctx.terms.get(cond) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }

        for (index, const_term) in [(args[0], args[1]), (args[1], args[0])] {
            let index = self.resolve_positive_bv_definition(index, definitions);
            let const_term = self.resolve_positive_bv_definition(const_term, definitions);
            let (width, value) = self.bv_const_value_with_definitions(const_term, definitions)?;
            if self.bitvec_width(index) != Some(width) {
                continue;
            }
            return Some(MuxEqConstGuard {
                index,
                width,
                value,
                cond,
                cond_is_true,
            });
        }

        None
    }

    fn decode_packed_mux_offset_source(
        &self,
        source: TermId,
        index_width: u32,
        elem_width: u32,
        definitions: Option<&HashMap<TermId, TermId>>,
    ) -> Option<(TermId, u32)> {
        if elem_width == 0 || !elem_width.is_power_of_two() {
            return None;
        }
        let shift = elem_width.trailing_zeros();
        let source = self.resolve_positive_bv_definition(source, definitions);
        let source_width = self.bitvec_width(source)?;
        if shift + index_width > source_width {
            return None;
        }

        if let Some(index_source) =
            self.decode_concat_zero_lshift_source(source, shift, definitions)
        {
            return Some((index_source, shift));
        }

        let TermData::App(sym, args) = self.ctx.terms.get(source) else {
            return None;
        };
        if sym.name() != "bvmul" || args.len() != 2 {
            return None;
        }

        for (index_source, const_term) in [(args[0], args[1]), (args[1], args[0])] {
            let (const_width, const_value) =
                self.bv_const_value_with_definitions(const_term, definitions)?;
            if const_width != source_width || const_value != BigInt::from(elem_width) {
                continue;
            }
            if self.bitvec_width(index_source).is_some() {
                return Some((index_source, shift));
            }
        }

        None
    }

    fn decode_concat_zero_lshift_source(
        &self,
        source: TermId,
        shift: u32,
        definitions: Option<&HashMap<TermId, TermId>>,
    ) -> Option<TermId> {
        if shift == 0 {
            return Some(source);
        }

        let source_width = self.bitvec_width(source)?;
        if shift >= source_width {
            return None;
        }

        let TermData::App(sym, args) = self.ctx.terms.get(source) else {
            return None;
        };
        if sym.name() != "concat" || args.len() != 2 {
            return None;
        }

        let (zero_width, zero_value) =
            self.bv_const_value_with_definitions(args[1], definitions)?;
        if zero_width != shift || zero_value != BigInt::from(0u8) {
            return None;
        }

        let (index_source, hi, lo) = self.slice_extract(args[0])?;
        if lo != 0 || hi + 1 != source_width - shift {
            return None;
        }
        if self.bitvec_width(index_source)? < hi + 1 {
            return None;
        }

        Some(index_source)
    }

    fn is_low_extract_of(&self, term: TermId, source: TermId, width: u32) -> bool {
        if self.bitvec_width(source) == Some(width) && term == source {
            return true;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        if sym.name() != "extract" || args.len() != 1 || args[0] != source {
            return false;
        }
        let Symbol::Indexed(_, indices) = sym else {
            return false;
        };
        indices.len() == 2 && indices[0] + 1 == width && indices[1] == 0
    }

    fn find_symbolic_select_for_source(
        &self,
        exact_select_index: &HashMap<(TermId, TermId), TermId>,
        array: TermId,
        source: TermId,
        index_width: u32,
    ) -> Option<TermId> {
        exact_select_index
            .iter()
            .find_map(|(&(candidate_array, candidate_index), &select)| {
                if candidate_array == array
                    && self.is_low_extract_of(candidate_index, source, index_width)
                {
                    Some(select)
                } else {
                    None
                }
            })
    }

    fn direct_index_guard_lane_bit(
        &self,
        guard: &MuxBitGuard,
        index_source: TermId,
        index_width: u32,
    ) -> Option<usize> {
        if guard.source == index_source && guard.bit_pos < index_width {
            return Some(guard.bit_pos as usize);
        }
        let (source, hi, lo) = self.slice_extract(guard.source)?;
        if source == index_source && lo == 0 && hi + 1 == index_width && guard.bit_pos < index_width
        {
            Some(guard.bit_pos as usize)
        } else {
            None
        }
    }

    fn scaled_guard_bit_is_implied_by_bound(
        guard: &MuxBitGuard,
        index_source: TermId,
        index_bit_offset: u32,
        elem_width: u32,
        source_upper_bounds: &HashMap<TermId, usize>,
    ) -> bool {
        if guard.bit_pos < index_bit_offset {
            return !guard.want_one;
        }

        let Some(&upper_bound) = source_upper_bounds.get(&index_source) else {
            return false;
        };
        let Some(max_scaled) = u128::try_from(upper_bound)
            .ok()
            .and_then(|bound| bound.checked_mul(u128::from(elem_width)))
        else {
            return false;
        };
        let bit_always_zero = if guard.bit_pos >= u128::BITS {
            true
        } else {
            max_scaled < (1u128 << guard.bit_pos)
        };
        bit_always_zero && !guard.want_one
    }

    fn scaled_index_guard_lane_bit(
        &self,
        guard: &MuxBitGuard,
        index_source: TermId,
        index_bit_offset: u32,
        index_width: u32,
        elem_width: u32,
        source_upper_bounds: &HashMap<TermId, usize>,
        definitions: Option<&HashMap<TermId, TermId>>,
    ) -> Option<Option<usize>> {
        if let Some(lane_bit) = self.direct_index_guard_lane_bit(guard, index_source, index_width) {
            return Some(Some(lane_bit));
        }

        let (guard_index_source, guard_index_bit_offset) = self.decode_packed_mux_offset_source(
            guard.source,
            index_width,
            elem_width,
            definitions,
        )?;
        if guard_index_source != index_source || guard_index_bit_offset != index_bit_offset {
            return None;
        }
        if guard.bit_pos >= index_bit_offset && guard.bit_pos < index_bit_offset + index_width {
            return Some(Some((guard.bit_pos - index_bit_offset) as usize));
        }
        if Self::scaled_guard_bit_is_implied_by_bound(
            guard,
            index_source,
            index_bit_offset,
            elem_width,
            source_upper_bounds,
        ) {
            return Some(None);
        }
        None
    }

    fn eq_guards_are_implied_by_lane(
        &self,
        eq_guards: &[MuxEqConstGuard],
        index: TermId,
        index_width: u32,
        lane: usize,
    ) -> bool {
        eq_guards.iter().all(|guard| {
            guard.index == index
                && guard.width == index_width
                && if guard.cond_is_true {
                    guard.value == BigInt::from(lane)
                } else {
                    guard.value != BigInt::from(lane)
                }
        })
    }

    fn bit_guards_are_implied_by_lane(
        &self,
        bit_guards: &[MuxBitGuard],
        index_source: TermId,
        index_width: u32,
        lane: usize,
    ) -> bool {
        bit_guards.iter().all(|guard| {
            let Some(lane_bit) = self.direct_index_guard_lane_bit(guard, index_source, index_width)
            else {
                return false;
            };
            let lane_want_one = ((lane >> lane_bit) & 1usize) == 1usize;
            guard.want_one == lane_want_one
        })
    }

    fn eq_guards_identify_lane(
        &self,
        eq_guards: &[MuxEqConstGuard],
        index: TermId,
        index_width: u32,
        lane: usize,
    ) -> bool {
        let lane_value = BigInt::from(lane);
        self.eq_guards_are_implied_by_lane(eq_guards, index, index_width, lane)
            && eq_guards.iter().any(|guard| {
                guard.index == index
                    && guard.width == index_width
                    && if guard.cond_is_true {
                        guard.value == lane_value
                    } else {
                        index_width == 1 && guard.value != lane_value
                    }
            })
    }

    fn collect_mux_packed_leaf_bridge_candidates(
        &self,
        term: TermId,
        packed_words: &HashMap<TermId, PackedArrayWord>,
        definitions: Option<&HashMap<TermId, TermId>>,
        asserted_positive: bool,
        bit_guards: &mut Vec<MuxBitGuard>,
        eq_guards: &mut Vec<MuxEqConstGuard>,
        out: &mut Vec<(
            Vec<MuxBitGuard>,
            Vec<MuxEqConstGuard>,
            Option<TermId>,
            PackedLeafBit,
        )>,
    ) {
        if out.len() >= PACKED_MUX_BRIDGE_CANDIDATE_LIMIT {
            return;
        }

        let term = self.resolve_positive_bv_definition(term, definitions);
        if let Some((cond, then_term, else_term)) = self.ite_parts(term) {
            if let Some(guard) =
                self.parse_mux_bit_condition_with_definitions(cond, true, definitions)
            {
                bit_guards.push(guard);
                self.collect_mux_packed_leaf_bridge_candidates(
                    then_term,
                    packed_words,
                    definitions,
                    asserted_positive,
                    bit_guards,
                    eq_guards,
                    out,
                );
                bit_guards.pop();
            } else if let Some(guard) =
                self.parse_mux_const_eq_condition_with_definitions(cond, true, definitions)
            {
                eq_guards.push(guard);
                self.collect_mux_packed_leaf_bridge_candidates(
                    then_term,
                    packed_words,
                    definitions,
                    asserted_positive,
                    bit_guards,
                    eq_guards,
                    out,
                );
                eq_guards.pop();
            } else {
                self.collect_mux_packed_leaf_bridge_candidates(
                    then_term,
                    packed_words,
                    definitions,
                    false,
                    bit_guards,
                    eq_guards,
                    out,
                );
            }

            if let Some(guard) =
                self.parse_mux_bit_condition_with_definitions(cond, false, definitions)
            {
                bit_guards.push(guard);
                self.collect_mux_packed_leaf_bridge_candidates(
                    else_term,
                    packed_words,
                    definitions,
                    asserted_positive,
                    bit_guards,
                    eq_guards,
                    out,
                );
                bit_guards.pop();
            } else if let Some(guard) =
                self.parse_mux_const_eq_condition_with_definitions(cond, false, definitions)
            {
                eq_guards.push(guard);
                self.collect_mux_packed_leaf_bridge_candidates(
                    else_term,
                    packed_words,
                    definitions,
                    asserted_positive,
                    bit_guards,
                    eq_guards,
                    out,
                );
                eq_guards.pop();
            } else {
                self.collect_mux_packed_leaf_bridge_candidates(
                    else_term,
                    packed_words,
                    definitions,
                    false,
                    bit_guards,
                    eq_guards,
                    out,
                );
            }
            return;
        }

        if let TermData::App(sym, args) = self.ctx.terms.get(term) {
            if sym.name() == "=" && args.len() == 2 {
                for (target_term, leaf_term) in [(args[0], args[1]), (args[1], args[0])] {
                    let leaf_term = self.resolve_positive_bv_definition(leaf_term, definitions);
                    let Some(leaf) = self.detect_packed_leaf_bit_with_definitions(
                        leaf_term,
                        packed_words,
                        definitions,
                    ) else {
                        continue;
                    };
                    let target_bit = if asserted_positive
                        && self.bitvec_width(target_term) == Some(1)
                        && !matches!(
                            self.ctx.terms.get(target_term),
                            TermData::Const(Constant::BitVec { .. })
                        ) {
                        Some(target_term)
                    } else {
                        None
                    };
                    out.push((bit_guards.clone(), eq_guards.clone(), target_bit, leaf));
                    return;
                }
            }
        }

        if let Some(leaf) =
            self.detect_packed_leaf_bit_with_definitions(term, packed_words, definitions)
        {
            out.push((bit_guards.clone(), eq_guards.clone(), None, leaf));
            return;
        }

        for child in self.ctx.terms.children(term) {
            let child_asserted_positive = if asserted_positive {
                matches!(
                    self.ctx.terms.get(term),
                    TermData::App(sym, _) if sym.name() == "and"
                )
            } else {
                false
            };
            self.collect_mux_packed_leaf_bridge_candidates(
                child,
                packed_words,
                definitions,
                child_asserted_positive,
                bit_guards,
                eq_guards,
                out,
            );
        }
    }

    fn collect_mux_output_bit_leaf_candidates(
        &self,
        term: TermId,
        packed_words: &HashMap<TermId, PackedArrayWord>,
        definitions: Option<&HashMap<TermId, TermId>>,
        bit_guards: &mut Vec<MuxBitGuard>,
        eq_guards: &mut Vec<MuxEqConstGuard>,
        out: &mut Vec<(Vec<MuxBitGuard>, Vec<MuxEqConstGuard>, PackedLeafBit)>,
    ) {
        if out.len() >= PACKED_MUX_BRIDGE_CANDIDATE_LIMIT {
            return;
        }

        let term = self.resolve_positive_bv_definition(term, definitions);
        if let Some((cond, then_term, else_term)) = self.ite_parts(term) {
            if let Some(guard) =
                self.parse_mux_bit_condition_with_definitions(cond, true, definitions)
            {
                bit_guards.push(guard);
                self.collect_mux_output_bit_leaf_candidates(
                    then_term,
                    packed_words,
                    definitions,
                    bit_guards,
                    eq_guards,
                    out,
                );
                bit_guards.pop();
            } else if let Some(guard) =
                self.parse_mux_const_eq_condition_with_definitions(cond, true, definitions)
            {
                eq_guards.push(guard);
                self.collect_mux_output_bit_leaf_candidates(
                    then_term,
                    packed_words,
                    definitions,
                    bit_guards,
                    eq_guards,
                    out,
                );
                eq_guards.pop();
            }

            if let Some(guard) =
                self.parse_mux_bit_condition_with_definitions(cond, false, definitions)
            {
                bit_guards.push(guard);
                self.collect_mux_output_bit_leaf_candidates(
                    else_term,
                    packed_words,
                    definitions,
                    bit_guards,
                    eq_guards,
                    out,
                );
                bit_guards.pop();
            } else if let Some(guard) =
                self.parse_mux_const_eq_condition_with_definitions(cond, false, definitions)
            {
                eq_guards.push(guard);
                self.collect_mux_output_bit_leaf_candidates(
                    else_term,
                    packed_words,
                    definitions,
                    bit_guards,
                    eq_guards,
                    out,
                );
                eq_guards.pop();
            }

            return;
        }

        let leaf = self.detect_packed_leaf_bit_with_definitions(term, packed_words, definitions);
        if let Some(leaf) = leaf {
            out.push((bit_guards.clone(), eq_guards.clone(), leaf));
        }
    }

    fn collect_mux_output_leaf_candidates(
        &self,
        output: TermId,
        mux: TermId,
        packed_words: &HashMap<TermId, PackedArrayWord>,
        definitions: Option<&HashMap<TermId, TermId>>,
        bit_guards: &mut Vec<MuxBitGuard>,
        eq_guards: &mut Vec<MuxEqConstGuard>,
        out: &mut Vec<MuxOutputLeafBridge>,
    ) {
        if out.len() >= PACKED_MUX_BRIDGE_CANDIDATE_LIMIT {
            return;
        }

        let mux = self.resolve_positive_bv_definition(mux, definitions);
        if let Some((cond, then_term, else_term)) = self.ite_parts(mux) {
            if let Some(guard) =
                self.parse_mux_bit_condition_with_definitions(cond, true, definitions)
            {
                bit_guards.push(guard);
                self.collect_mux_output_leaf_candidates(
                    output,
                    then_term,
                    packed_words,
                    definitions,
                    bit_guards,
                    eq_guards,
                    out,
                );
                bit_guards.pop();
            } else if let Some(guard) =
                self.parse_mux_const_eq_condition_with_definitions(cond, true, definitions)
            {
                eq_guards.push(guard);
                self.collect_mux_output_leaf_candidates(
                    output,
                    then_term,
                    packed_words,
                    definitions,
                    bit_guards,
                    eq_guards,
                    out,
                );
                eq_guards.pop();
            }

            if let Some(guard) =
                self.parse_mux_bit_condition_with_definitions(cond, false, definitions)
            {
                bit_guards.push(guard);
                self.collect_mux_output_leaf_candidates(
                    output,
                    else_term,
                    packed_words,
                    definitions,
                    bit_guards,
                    eq_guards,
                    out,
                );
                bit_guards.pop();
            } else if let Some(guard) =
                self.parse_mux_const_eq_condition_with_definitions(cond, false, definitions)
            {
                eq_guards.push(guard);
                self.collect_mux_output_leaf_candidates(
                    output,
                    else_term,
                    packed_words,
                    definitions,
                    bit_guards,
                    eq_guards,
                    out,
                );
                eq_guards.pop();
            }

            return;
        }

        self.collect_concat_mux_output_leaf_candidates(output, mux, packed_words, definitions, out);
        if out.len() >= PACKED_MUX_BRIDGE_CANDIDATE_LIMIT {
            return;
        }

        let Some(leaves) = self.detect_packed_leaf_value_bits(mux, packed_words) else {
            return;
        };
        if self.bitvec_width(output) != Some(leaves.len() as u32) {
            return;
        }
        if bit_guards.is_empty() && eq_guards.is_empty() {
            return;
        }
        for leaf in leaves {
            if out.len() >= PACKED_MUX_BRIDGE_CANDIDATE_LIMIT {
                break;
            }
            out.push(MuxOutputLeafBridge {
                bit_guards: bit_guards.clone(),
                eq_guards: eq_guards.clone(),
                output,
                leaf,
            });
        }
    }

    fn collect_concat_mux_output_leaf_candidates(
        &self,
        output: TermId,
        mux: TermId,
        packed_words: &HashMap<TermId, PackedArrayWord>,
        definitions: Option<&HashMap<TermId, TermId>>,
        out: &mut Vec<MuxOutputLeafBridge>,
    ) {
        let Some(output_width) = self.bitvec_width(output) else {
            return;
        };
        if output_width <= 1 {
            return;
        }

        let mut leaves = Vec::new();
        self.flatten_concat_high_to_low_with_definitions(
            mux,
            definitions,
            &mut leaves,
            &mut HashSet::default(),
        );
        if leaves.len() <= 1 || leaves.len() != output_width as usize {
            return;
        }
        if leaves
            .iter()
            .any(|&leaf_term| self.bitvec_width_for_definition(leaf_term) != Some(1))
        {
            return;
        }

        for (leaf_index, leaf_term) in leaves.into_iter().enumerate() {
            if out.len() >= PACKED_MUX_BRIDGE_CANDIDATE_LIMIT {
                return;
            }

            let expected_bit_pos = output_width as usize - 1 - leaf_index;
            let mut leaf_candidates = Vec::new();
            self.collect_mux_output_bit_leaf_candidates(
                leaf_term,
                packed_words,
                definitions,
                &mut Vec::new(),
                &mut Vec::new(),
                &mut leaf_candidates,
            );

            for (bit_guards, eq_guards, leaf) in leaf_candidates {
                if out.len() >= PACKED_MUX_BRIDGE_CANDIDATE_LIMIT {
                    return;
                }
                if bit_guards.is_empty() && eq_guards.is_empty() {
                    continue;
                }
                if leaf.bit_pos != expected_bit_pos {
                    continue;
                }
                out.push(MuxOutputLeafBridge {
                    bit_guards,
                    eq_guards,
                    output,
                    leaf,
                });
            }
        }
    }

    fn collect_positive_mux_output_bridge_candidates(
        &self,
        term: TermId,
        packed_words: &HashMap<TermId, PackedArrayWord>,
        definitions: Option<&HashMap<TermId, TermId>>,
        out: &mut Vec<MuxOutputLeafBridge>,
    ) {
        if out.len() >= PACKED_MUX_BRIDGE_CANDIDATE_LIMIT {
            return;
        }

        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return;
        };
        if sym.name() == "and" {
            for &child in args {
                self.collect_positive_mux_output_bridge_candidates(
                    child,
                    packed_words,
                    definitions,
                    out,
                );
                if out.len() >= PACKED_MUX_BRIDGE_CANDIDATE_LIMIT {
                    break;
                }
            }
            return;
        }
        if sym.name() != "=" || args.len() != 2 {
            return;
        }

        for (output, mux) in [(args[0], args[1]), (args[1], args[0])] {
            let Some(output_width) = self.bitvec_width(output) else {
                continue;
            };
            if output_width <= 1
                || self.bitvec_width(mux) != Some(output_width)
                || matches!(
                    self.ctx.terms.get(output),
                    TermData::Const(Constant::BitVec { .. })
                )
            {
                continue;
            }

            self.collect_mux_output_leaf_candidates(
                output,
                mux,
                packed_words,
                definitions,
                &mut Vec::new(),
                &mut Vec::new(),
                out,
            );
        }
    }

    fn collect_packed_mux_pre_debug_stats(
        &self,
        term: TermId,
        packed_words: &HashMap<TermId, PackedArrayWord>,
        definitions: Option<&HashMap<TermId, TermId>>,
        stats: &mut PackedMuxPreDebugStats,
    ) {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return;
        };
        if sym.name() == "and" {
            for &child in args {
                self.collect_packed_mux_pre_debug_stats(child, packed_words, definitions, stats);
            }
            return;
        }
        if sym.name() != "=" || args.len() != 2 {
            return;
        }

        stats.positive_eqs += 1;
        for (output, mux) in [(args[0], args[1]), (args[1], args[0])] {
            let Some(output_width) = self.bitvec_width(output) else {
                continue;
            };
            if output_width <= 1
                || self.bitvec_width(mux) != Some(output_width)
                || matches!(
                    self.ctx.terms.get(output),
                    TermData::Const(Constant::BitVec { .. })
                )
            {
                continue;
            }

            stats.wide_width_pairs += 1;
            self.collect_packed_mux_output_debug_stats(
                output,
                mux,
                packed_words,
                definitions,
                stats,
                &mut HashSet::default(),
            );
        }
    }

    fn collect_packed_mux_output_debug_stats(
        &self,
        output: TermId,
        mux: TermId,
        packed_words: &HashMap<TermId, PackedArrayWord>,
        definitions: Option<&HashMap<TermId, TermId>>,
        stats: &mut PackedMuxPreDebugStats,
        seen: &mut HashSet<TermId>,
    ) {
        let mux = self.resolve_positive_bv_definition(mux, definitions);
        if !seen.insert(mux) {
            return;
        }

        if let Some((cond, then_term, else_term)) = self.ite_parts(mux) {
            stats.bit_ite_nodes += 1;
            if self
                .parse_mux_bit_condition_with_definitions(cond, true, definitions)
                .is_some()
                || self
                    .parse_mux_const_eq_condition_with_definitions(cond, true, definitions)
                    .is_some()
            {
                stats.bit_ite_parsed_true += 1;
                self.collect_packed_mux_output_debug_stats(
                    output,
                    then_term,
                    packed_words,
                    definitions,
                    stats,
                    seen,
                );
            } else {
                stats.bit_ite_unparsed += 1;
                stats.sample_unparsed_ite.get_or_insert(cond);
            }

            if self
                .parse_mux_bit_condition_with_definitions(cond, false, definitions)
                .is_some()
                || self
                    .parse_mux_const_eq_condition_with_definitions(cond, false, definitions)
                    .is_some()
            {
                stats.bit_ite_parsed_false += 1;
                self.collect_packed_mux_output_debug_stats(
                    output,
                    else_term,
                    packed_words,
                    definitions,
                    stats,
                    seen,
                );
            } else {
                stats.bit_ite_unparsed += 1;
                stats.sample_unparsed_ite.get_or_insert(cond);
            }

            seen.remove(&mux);
            return;
        }

        let Some(output_width) = self.bitvec_width(output) else {
            seen.remove(&mux);
            return;
        };
        let mut leaves = Vec::new();
        self.flatten_concat_high_to_low_with_definitions(
            mux,
            definitions,
            &mut leaves,
            &mut HashSet::default(),
        );
        if leaves.len() > 1 {
            stats.concat_attempts += 1;
            if leaves.len() == output_width as usize
                && leaves
                    .iter()
                    .all(|&leaf_term| self.bitvec_width_for_definition(leaf_term) == Some(1))
            {
                stats.concat_flat_bit_ok += 1;
                for leaf_term in leaves {
                    self.collect_packed_mux_bit_debug_stats(
                        leaf_term,
                        packed_words,
                        definitions,
                        stats,
                        &mut HashSet::default(),
                    );
                }
            }
        }

        seen.remove(&mux);
    }

    fn collect_packed_mux_bit_debug_stats(
        &self,
        term: TermId,
        packed_words: &HashMap<TermId, PackedArrayWord>,
        definitions: Option<&HashMap<TermId, TermId>>,
        stats: &mut PackedMuxPreDebugStats,
        seen: &mut HashSet<TermId>,
    ) {
        let term = self.resolve_positive_bv_definition(term, definitions);
        if !seen.insert(term) {
            return;
        }

        if let Some((cond, then_term, else_term)) = self.ite_parts(term) {
            stats.bit_ite_nodes += 1;
            if self
                .parse_mux_bit_condition_with_definitions(cond, true, definitions)
                .is_some()
                || self
                    .parse_mux_const_eq_condition_with_definitions(cond, true, definitions)
                    .is_some()
            {
                stats.bit_ite_parsed_true += 1;
                self.collect_packed_mux_bit_debug_stats(
                    then_term,
                    packed_words,
                    definitions,
                    stats,
                    seen,
                );
            } else {
                stats.bit_ite_unparsed += 1;
                stats.sample_unparsed_ite.get_or_insert(cond);
            }

            if self
                .parse_mux_bit_condition_with_definitions(cond, false, definitions)
                .is_some()
                || self
                    .parse_mux_const_eq_condition_with_definitions(cond, false, definitions)
                    .is_some()
            {
                stats.bit_ite_parsed_false += 1;
                self.collect_packed_mux_bit_debug_stats(
                    else_term,
                    packed_words,
                    definitions,
                    stats,
                    seen,
                );
            } else {
                stats.bit_ite_unparsed += 1;
                stats.sample_unparsed_ite.get_or_insert(cond);
            }

            seen.remove(&term);
            return;
        }

        if self
            .detect_packed_leaf_bit_with_definitions(term, packed_words, definitions)
            .is_some()
        {
            stats.packed_leaf_hits += 1;
        } else {
            stats.dead_bit_leaves += 1;
            stats.sample_dead_leaf.get_or_insert(term);
        }

        seen.remove(&term);
    }

    fn packed_mux_required_lane_mask(
        source: TermId,
        index_width: u32,
        source_upper_bounds: &HashMap<TermId, usize>,
    ) -> Option<u128> {
        if index_width > 7 {
            return None;
        }
        let lane_count = 1u32 << index_width;
        let full_mask = if lane_count == u128::BITS {
            u128::MAX
        } else {
            (1u128 << lane_count) - 1
        };
        let range_mask = source_upper_bounds.get(&source).and_then(|&upper_bound| {
            let lane_count = lane_count as usize;
            (upper_bound < lane_count).then(|| {
                if upper_bound + 1 == u128::BITS as usize {
                    u128::MAX
                } else {
                    (1u128 << (upper_bound + 1)) - 1
                }
            })
        });
        Some(range_mask.unwrap_or(full_mask))
    }

    fn add_mux_output_term_coverage(
        coverage: &mut HashMap<(TermId, TermId, TermId), MuxOutputTermCoverage>,
        output: TermId,
        symbolic_select: TermId,
        source: TermId,
        leaf: &PackedLeafBit,
        output_width: u32,
    ) {
        if leaf.bit_pos >= output_width as usize || leaf.lane >= u128::BITS as usize {
            return;
        }
        let entry = coverage
            .entry((output, symbolic_select, source))
            .or_insert_with(|| MuxOutputTermCoverage {
                source,
                output_width,
                index_width: leaf.index_width,
                bit_lane_masks: vec![0; output_width as usize],
            });
        if entry.output_width == output_width
            && entry.index_width == leaf.index_width
            && entry.bit_lane_masks.len() == output_width as usize
        {
            entry.bit_lane_masks[leaf.bit_pos] |= 1u128 << leaf.lane;
        }
    }

    /// Add asserted-consequence equalities for fully-covered packed mux outputs.
    ///
    /// The late CNF bridge can prove each bit of a BV mux output equal to the
    /// symbolic array select, but that happens after multiplier bit-blasting.
    /// When the same relationship is fully covered syntactically, add
    /// `(= output (select a idx))` before preprocessing so existing variable
    /// substitution can collapse downstream BV users before bit-blast.
    pub(in crate::executor) fn add_packed_mux_output_select_equalities_for_preprocess(
        &mut self,
    ) -> usize {
        let packed_debug = debug_abv_packed_lookup();
        let mut all_terms = Vec::new();
        let mut all_terms_seen = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_all_terms(assertion, &mut all_terms, &mut all_terms_seen);
        }

        let packed_words = self.build_packed_array_word_map(&all_terms);
        if packed_words.is_empty() {
            if packed_debug {
                safe_eprintln!("[abv-packed-pre] skipped: no packed words");
            }
            return 0;
        }

        let mut select_terms: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut store_terms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
        let mut visited = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_array_terms(assertion, &mut select_terms, &mut store_terms, &mut visited);
        }
        if select_terms.is_empty() {
            if packed_debug {
                safe_eprintln!(
                    "[abv-packed-pre] skipped: no select terms packed_words={}",
                    packed_words.len()
                );
            }
            return 0;
        }

        let mut exact_select_index: HashMap<(TermId, TermId), TermId> = HashMap::default();
        for &(select_term, array, index) in &select_terms {
            exact_select_index
                .entry((array, index))
                .or_insert(select_term);
        }

        let mut positive_bv_definitions = HashMap::default();
        let definition_assertions = self.ctx.assertions.clone();
        for assertion in definition_assertions {
            self.collect_positive_bv_var_definitions(assertion, &mut positive_bv_definitions);
        }

        let mut candidates = Vec::new();
        for &assertion in &self.ctx.assertions {
            self.collect_positive_mux_output_bridge_candidates(
                assertion,
                &packed_words,
                Some(&positive_bv_definitions),
                &mut candidates,
            );
        }
        if candidates.is_empty() {
            if packed_debug {
                let mut stats = PackedMuxPreDebugStats::default();
                for &assertion in &self.ctx.assertions {
                    self.collect_packed_mux_pre_debug_stats(
                        assertion,
                        &packed_words,
                        Some(&positive_bv_definitions),
                        &mut stats,
                    );
                }
                safe_eprintln!(
                    "[abv-packed-pre] skipped: no candidates packed_words={} select_terms={} definitions={} positive_eqs={} wide_width_pairs={} concat_attempts={} concat_flat_bit_ok={} bit_ite_nodes={} bit_ite_parsed_true={} bit_ite_parsed_false={} bit_ite_unparsed={} packed_leaf_hits={} dead_bit_leaves={}",
                    packed_words.len(),
                    select_terms.len(),
                    positive_bv_definitions.len(),
                    stats.positive_eqs,
                    stats.wide_width_pairs,
                    stats.concat_attempts,
                    stats.concat_flat_bit_ok,
                    stats.bit_ite_nodes,
                    stats.bit_ite_parsed_true,
                    stats.bit_ite_parsed_false,
                    stats.bit_ite_unparsed,
                    stats.packed_leaf_hits,
                    stats.dead_bit_leaves,
                );
                if let Some(cond) = stats.sample_unparsed_ite {
                    safe_eprintln!(
                        "[abv-packed-pre] sample_unparsed_ite={}",
                        self.format_term(cond)
                    );
                }
                if let Some(leaf) = stats.sample_dead_leaf {
                    safe_eprintln!(
                        "[abv-packed-pre] sample_dead_leaf={}",
                        self.format_term(leaf)
                    );
                }
            }
            return 0;
        }

        let source_upper_bounds = self.build_nonnegative_upper_bounds();
        let mut coverage: HashMap<(TermId, TermId, TermId), MuxOutputTermCoverage> =
            HashMap::default();
        let mut debug_guard_sources = 0usize;
        let mut debug_scaled_sources = 0usize;
        let mut debug_lane_complete = 0usize;
        let mut debug_lane_match = 0usize;
        let mut debug_scaled_select_miss = 0usize;
        let mut debug_sample_source_decode_miss = None;
        let mut debug_sample_scaled_select_miss = None;
        let mut debug_sample_scaled_incomplete = None;
        let mut debug_sample_scaled_conflict = None;

        for candidate in &candidates {
            let leaf = &candidate.leaf;
            let Some(output_width) = self.bitvec_width(candidate.output) else {
                continue;
            };
            if output_width <= 1 || leaf.elem_width != output_width {
                continue;
            }
            if leaf.index_width >= usize::BITS || leaf.lane >= (1usize << leaf.index_width) {
                continue;
            }

            let mut sources = Vec::new();
            for guard in &candidate.bit_guards {
                if !sources.contains(&guard.source) {
                    sources.push(guard.source);
                }
            }
            debug_guard_sources += sources.len();

            for &source in &sources {
                if !self.eq_guards_are_implied_by_lane(
                    &candidate.eq_guards,
                    source,
                    leaf.index_width,
                    leaf.lane,
                ) {
                    continue;
                }
                let mut low_guards = vec![None; leaf.index_width as usize];
                let mut conflicted = false;
                for guard in &candidate.bit_guards {
                    let Some(lane_bit) =
                        self.direct_index_guard_lane_bit(guard, source, leaf.index_width)
                    else {
                        conflicted = true;
                        break;
                    };
                    let slot = &mut low_guards[lane_bit];
                    if let Some(want_one) = slot {
                        if *want_one != guard.want_one {
                            conflicted = true;
                            break;
                        }
                    } else {
                        *slot = Some(guard.want_one);
                    }
                }
                if conflicted || low_guards.iter().any(Option::is_none) {
                    continue;
                }
                let mut lane_matches = true;
                for (bit_pos, guard) in low_guards.into_iter().enumerate() {
                    let want_one = guard.expect("checked complete low guards");
                    let lane_want_one = ((leaf.lane >> bit_pos) & 1usize) == 1usize;
                    if lane_want_one != want_one {
                        lane_matches = false;
                        break;
                    }
                }
                if !lane_matches {
                    continue;
                }

                let Some(symbolic_select) = self.find_symbolic_select_for_source(
                    &exact_select_index,
                    leaf.array,
                    source,
                    leaf.index_width,
                ) else {
                    continue;
                };
                Self::add_mux_output_term_coverage(
                    &mut coverage,
                    candidate.output,
                    symbolic_select,
                    source,
                    leaf,
                    output_width,
                );
            }

            let mut scaled_source_groups = Vec::new();
            for &source in &sources {
                let Some((index_source, index_bit_offset)) = self.decode_packed_mux_offset_source(
                    source,
                    leaf.index_width,
                    leaf.elem_width,
                    Some(&positive_bv_definitions),
                ) else {
                    debug_sample_source_decode_miss.get_or_insert((
                        source,
                        leaf.index_width,
                        leaf.elem_width,
                        candidate.output,
                    ));
                    continue;
                };
                debug_scaled_sources += 1;
                if !scaled_source_groups.iter().any(
                    |&(existing_index_source, existing_index_bit_offset)| {
                        existing_index_source == index_source
                            && existing_index_bit_offset == index_bit_offset
                    },
                ) {
                    scaled_source_groups.push((index_source, index_bit_offset));
                }
            }

            for &(index_source, index_bit_offset) in &scaled_source_groups {
                if !self.eq_guards_are_implied_by_lane(
                    &candidate.eq_guards,
                    index_source,
                    leaf.index_width,
                    leaf.lane,
                ) {
                    continue;
                }
                let mut lane_guards = vec![None; leaf.index_width as usize];
                let mut conflicted = false;
                let mut conflict_detail = None;
                for guard in &candidate.bit_guards {
                    let Some(lane_bit) = self.scaled_index_guard_lane_bit(
                        guard,
                        index_source,
                        index_bit_offset,
                        leaf.index_width,
                        leaf.elem_width,
                        &source_upper_bounds,
                        Some(&positive_bv_definitions),
                    ) else {
                        conflicted = true;
                        break;
                    };
                    let Some(lane_bit) = lane_bit else {
                        continue;
                    };
                    let slot = &mut lane_guards[lane_bit];
                    if let Some(want_one) = slot {
                        if *want_one != guard.want_one {
                            conflicted = true;
                            conflict_detail.get_or_insert((
                                lane_bit,
                                *want_one,
                                guard.want_one,
                                guard.source,
                                guard.bit_pos,
                                guard.bit_term,
                            ));
                            break;
                        }
                    } else {
                        *slot = Some(guard.want_one);
                    }
                }
                if conflicted || lane_guards.iter().any(Option::is_none) {
                    if packed_debug && debug_sample_scaled_incomplete.is_none() {
                        let present_bits: Vec<u32> = candidate
                            .bit_guards
                            .iter()
                            .filter_map(|guard| {
                                if self
                                    .scaled_index_guard_lane_bit(
                                        guard,
                                        index_source,
                                        index_bit_offset,
                                        leaf.index_width,
                                        leaf.elem_width,
                                        &source_upper_bounds,
                                        Some(&positive_bv_definitions),
                                    )
                                    .is_some()
                                {
                                    Some(guard.bit_pos)
                                } else {
                                    None
                                }
                            })
                            .collect();
                        debug_sample_scaled_incomplete.get_or_insert((
                            index_source,
                            index_bit_offset,
                            leaf.index_width,
                            leaf.elem_width,
                            candidate.output,
                            leaf.lane,
                            lane_guards.clone(),
                            present_bits,
                        ));
                    }
                    if packed_debug && conflicted && debug_sample_scaled_conflict.is_none() {
                        if let Some(detail) = conflict_detail {
                            debug_sample_scaled_conflict.get_or_insert(detail);
                        }
                    }
                    continue;
                }
                debug_lane_complete += 1;
                let mut lane_matches = true;
                for (bit_pos, guard) in lane_guards.into_iter().enumerate() {
                    let want_one = guard.expect("checked complete lane guards");
                    let lane_want_one = ((leaf.lane >> bit_pos) & 1usize) == 1usize;
                    if lane_want_one != want_one {
                        lane_matches = false;
                        break;
                    }
                }
                if !lane_matches {
                    continue;
                }
                debug_lane_match += 1;

                let Some(symbolic_select) = self.find_symbolic_select_for_source(
                    &exact_select_index,
                    leaf.array,
                    index_source,
                    leaf.index_width,
                ) else {
                    debug_scaled_select_miss += 1;
                    debug_sample_scaled_select_miss.get_or_insert((
                        leaf.array,
                        index_source,
                        leaf.index_width,
                        candidate.output,
                    ));
                    continue;
                };
                Self::add_mux_output_term_coverage(
                    &mut coverage,
                    candidate.output,
                    symbolic_select,
                    index_source,
                    leaf,
                    output_width,
                );
            }

            for guard in &candidate.eq_guards {
                if !candidate.bit_guards.is_empty()
                    || !self.eq_guards_are_implied_by_lane(
                        &candidate.eq_guards,
                        guard.index,
                        leaf.index_width,
                        leaf.lane,
                    )
                {
                    continue;
                }
                if guard.width != leaf.index_width || guard.value != BigInt::from(leaf.lane) {
                    continue;
                }
                let Some(&symbolic_select) = exact_select_index.get(&(leaf.array, guard.index))
                else {
                    continue;
                };
                Self::add_mux_output_term_coverage(
                    &mut coverage,
                    candidate.output,
                    symbolic_select,
                    guard.index,
                    leaf,
                    output_width,
                );
            }
        }

        let mut existing_assertions: HashSet<TermId> =
            self.ctx.assertions.iter().copied().collect();
        let mut added = 0usize;
        let coverage_terms = coverage.len();
        for ((output, symbolic_select, _source), coverage) in coverage {
            if !matches!(self.ctx.terms.get(output), TermData::Var(_, _)) {
                continue;
            }
            if self.term_contains(symbolic_select, output) {
                continue;
            }
            let Some(required_mask) = Self::packed_mux_required_lane_mask(
                coverage.source,
                coverage.index_width,
                &source_upper_bounds,
            ) else {
                continue;
            };
            if coverage
                .bit_lane_masks
                .iter()
                .any(|&lane_mask| lane_mask & required_mask != required_mask)
            {
                continue;
            }

            let equality = self.ctx.terms.mk_eq_coerce(output, symbolic_select);
            if existing_assertions.insert(equality) {
                self.ctx.assertions.push(equality);
                added += 1;
            }
        }

        if packed_debug {
            safe_eprintln!(
                "[abv-packed-pre] candidates={} coverage_terms={} added_equalities={}",
                candidates.len(),
                coverage_terms,
                added
            );
            safe_eprintln!(
                "[abv-packed-pre] coverage_debug guard_sources={} scaled_sources={} lane_complete={} lane_match={} scaled_select_miss={}",
                debug_guard_sources,
                debug_scaled_sources,
                debug_lane_complete,
                debug_lane_match,
                debug_scaled_select_miss,
            );
            if let Some((source, index_width, elem_width, output)) = debug_sample_source_decode_miss
            {
                safe_eprintln!(
                    "[abv-packed-pre] sample_source_decode_miss source={} index_width={} elem_width={} output={}",
                    self.format_term(source),
                    index_width,
                    elem_width,
                    self.format_term(output),
                );
            }
            if let Some((array, index_source, index_width, output)) =
                debug_sample_scaled_select_miss
            {
                safe_eprintln!(
                    "[abv-packed-pre] sample_scaled_select_miss array={} index_source={} index_width={} output={}",
                    self.format_term(array),
                    self.format_term(index_source),
                    index_width,
                    self.format_term(output),
                );
            }
            if let Some((
                index_source,
                index_bit_offset,
                index_width,
                elem_width,
                output,
                lane,
                lane_guards,
                present_bits,
            )) = debug_sample_scaled_incomplete
            {
                safe_eprintln!(
                    "[abv-packed-pre] sample_scaled_incomplete index_source={} index_bit_offset={} index_width={} elem_width={} output={} lane={} lane_guards={:?} present_bits={:?}",
                    self.format_term(index_source),
                    index_bit_offset,
                    index_width,
                    elem_width,
                    self.format_term(output),
                    lane,
                    lane_guards,
                    present_bits,
                );
            }
            if let Some((lane_bit, existing, incoming, source, bit_pos, bit_term)) =
                debug_sample_scaled_conflict
            {
                safe_eprintln!(
                    "[abv-packed-pre] sample_scaled_conflict lane_bit={} existing={} incoming={} source={} bit_pos={} bit_term={}",
                    lane_bit,
                    existing,
                    incoming,
                    self.format_term(source),
                    bit_pos,
                    self.format_term(bit_term),
                );
            }
        }

        added
    }

    /// Materialize read terms needed by residual array axioms.
    ///
    /// `expand_select_store_all_adaptive` intentionally leaves some
    /// `select(store(a, i, v), j)` terms in large formulas. The bit-level ROW2
    /// encoder can connect such a read to `select(a, j)`, but only if that base
    /// read exists as a term with BV bits. Residual `select(ite(c, a, b), j)`
    /// terms likewise need branch reads for guarded ITE clauses. This helper
    /// creates those reads as extra roots, not assertions, and repeats to cover
    /// nested store chains.
    pub(in crate::executor) fn materialize_array_row2_read_terms(
        &mut self,
        extra_roots: &mut Vec<TermId>,
    ) -> usize {
        const MAX_ROW2_READ_TERMS: usize = 20_000;

        let mut known_roots: HashSet<TermId> = extra_roots.iter().copied().collect();
        let mut seen_obligations: HashSet<(TermId, TermId)> = HashSet::default();
        let mut added = 0usize;

        loop {
            let mut select_terms: Vec<(TermId, TermId, TermId)> = Vec::new();
            let mut store_terms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
            let mut visited = HashSet::default();

            for &assertion in &self.ctx.assertions {
                self.collect_array_terms(
                    assertion,
                    &mut select_terms,
                    &mut store_terms,
                    &mut visited,
                );
            }
            for &term in extra_roots.iter() {
                self.collect_array_terms(term, &mut select_terms, &mut store_terms, &mut visited);
            }

            if select_terms.is_empty() {
                break;
            }

            let mut selects_by_array: HashMap<TermId, Vec<TermId>> = HashMap::default();
            for &(_select_term, array, index) in &select_terms {
                selects_by_array.entry(array).or_default().push(index);
            }

            let mut progress = false;
            for &(_select_term, array, sel_idx) in &select_terms {
                let TermData::Ite(_cond, then_array, else_array) = self.ctx.terms.get(array) else {
                    continue;
                };
                let then_array = *then_array;
                let else_array = *else_array;

                for branch_array in [then_array, else_array] {
                    if !matches!(self.ctx.terms.sort(branch_array), Sort::Array(_)) {
                        continue;
                    }
                    if !seen_obligations.insert((branch_array, sel_idx)) {
                        continue;
                    }
                    let read_term = self.ctx.terms.mk_select(branch_array, sel_idx);
                    if known_roots.insert(read_term) {
                        extra_roots.push(read_term);
                        added += 1;
                        progress = true;
                        if added >= MAX_ROW2_READ_TERMS {
                            return added;
                        }
                    }
                }
            }

            for &(store_term, base_array, store_idx, _store_val) in &store_terms {
                let Some(indices) = selects_by_array.get(&store_term) else {
                    continue;
                };

                for &sel_idx in indices {
                    if store_idx == sel_idx {
                        continue;
                    }
                    if !seen_obligations.insert((base_array, sel_idx)) {
                        continue;
                    }

                    let read_term = self.ctx.terms.mk_select(base_array, sel_idx);
                    if known_roots.insert(read_term) {
                        extra_roots.push(read_term);
                        added += 1;
                        progress = true;
                        if added >= MAX_ROW2_READ_TERMS {
                            return added;
                        }
                    }
                }
            }

            if !progress {
                break;
            }
        }

        added
    }

    /// Ensure array-index/value BV terms are bit-blasted before generating
    /// array axioms. Select terms are opaque to the BV bitblaster, so their
    /// index subterms must be explicitly materialized.
    pub(in crate::executor) fn materialize_array_bv_terms(
        &self,
        bv_solver: &mut BvSolver<'_>,
        extra_terms: &[TermId],
    ) {
        let mut select_terms: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut store_terms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
        let mut visited = HashSet::default();

        for &assertion in &self.ctx.assertions {
            self.collect_array_terms(assertion, &mut select_terms, &mut store_terms, &mut visited);
        }
        for &term in extra_terms {
            self.collect_array_terms(term, &mut select_terms, &mut store_terms, &mut visited);
        }

        for &(select_term, _, select_idx) in &select_terms {
            let _ = bv_solver.ensure_term_bits(select_term);
            let _ = bv_solver.ensure_term_bits(select_idx);
        }

        for &(_, _, store_idx, store_val) in &store_terms {
            let _ = bv_solver.ensure_term_bits(store_idx);
            let _ = bv_solver.ensure_term_bits(store_val);
        }
    }

    fn bitvec_width(&self, term: TermId) -> Option<u32> {
        match self.ctx.terms.sort(term) {
            Sort::BitVec(bv) => Some(bv.width),
            _ => None,
        }
    }

    fn bitvec_width_for_definition(&self, term: TermId) -> Option<u32> {
        self.bitvec_width_for_definition_inner(term, &mut HashSet::default())
    }

    fn bitvec_width_for_definition_inner(
        &self,
        term: TermId,
        seen: &mut HashSet<TermId>,
    ) -> Option<u32> {
        if let Some(width) = self.bitvec_width(term) {
            return Some(width);
        }
        if !seen.insert(term) {
            return None;
        }

        let result = if let Some((_cond, then_term, else_term)) = self.ite_parts(term) {
            let then_width = self.bitvec_width_for_definition_inner(then_term, seen)?;
            let else_width = self.bitvec_width_for_definition_inner(else_term, seen)?;
            (then_width == else_width).then_some(then_width)
        } else {
            None
        };

        seen.remove(&term);
        result
    }

    fn normalize_bv_const(value: &BigInt, width: u32) -> BigInt {
        let modulus = BigInt::from(1u8) << width;
        ((value % &modulus) + &modulus) % modulus
    }

    fn zero_const(width: u32) -> NormalizedBvIndexKey {
        NormalizedBvIndexKey::Const {
            width,
            value: BigInt::from(0u8),
        }
    }

    fn normalize_bv_index_key(&self, term: TermId) -> NormalizedBvIndexKey {
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::BitVec { value, width }) => NormalizedBvIndexKey::Const {
                width: *width,
                value: Self::normalize_bv_const(value, *width),
            },
            TermData::App(sym, args) if args.len() == 1 && sym.name() == "zero_extend" => {
                let Some(arg_width) = self.bitvec_width(args[0]) else {
                    return NormalizedBvIndexKey::Raw(term);
                };
                let Some(result_width) = self.bitvec_width(term) else {
                    return NormalizedBvIndexKey::Raw(term);
                };
                let indexed_extra_bits = match sym {
                    Symbol::Indexed(_, indices) => indices.first().copied(),
                    _ => None,
                };
                let extra_bits =
                    indexed_extra_bits.unwrap_or(result_width.saturating_sub(arg_width));
                if extra_bits == 0 {
                    return self.normalize_bv_index_key(args[0]);
                }
                match self.normalize_bv_index_key(args[0]) {
                    NormalizedBvIndexKey::Const { value, .. } => NormalizedBvIndexKey::Const {
                        width: result_width,
                        value: Self::normalize_bv_const(&value, result_width),
                    },
                    NormalizedBvIndexKey::ZeroExtend {
                        extra_bits: nested_extra,
                        inner: nested_inner,
                    } => NormalizedBvIndexKey::ZeroExtend {
                        extra_bits: nested_extra.saturating_add(extra_bits),
                        inner: nested_inner,
                    },
                    inner => NormalizedBvIndexKey::ZeroExtend {
                        extra_bits,
                        inner: Box::new(inner),
                    },
                }
            }
            TermData::App(sym, args) if args.len() == 2 && sym.name() == "bvadd" => {
                let Some(width) = self.bitvec_width(term) else {
                    return NormalizedBvIndexKey::Raw(term);
                };
                let lhs = self.normalize_bv_index_key(args[0]);
                let rhs = self.normalize_bv_index_key(args[1]);
                if rhs == Self::zero_const(width) {
                    return lhs;
                }
                if lhs == Self::zero_const(width) {
                    return rhs;
                }
                if let (
                    NormalizedBvIndexKey::Const { value: a, .. },
                    NormalizedBvIndexKey::Const { value: b, .. },
                ) = (&lhs, &rhs)
                {
                    return NormalizedBvIndexKey::Const {
                        width,
                        value: Self::normalize_bv_const(&(a + b), width),
                    };
                }
                NormalizedBvIndexKey::BvAdd {
                    width,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }
            TermData::App(sym, args) if args.len() == 2 && sym.name() == "bvsub" => {
                let Some(width) = self.bitvec_width(term) else {
                    return NormalizedBvIndexKey::Raw(term);
                };
                let lhs = self.normalize_bv_index_key(args[0]);
                let rhs = self.normalize_bv_index_key(args[1]);
                if rhs == Self::zero_const(width) {
                    return lhs;
                }
                if lhs == rhs {
                    return Self::zero_const(width);
                }
                if let (
                    NormalizedBvIndexKey::Const { value: a, .. },
                    NormalizedBvIndexKey::Const { value: b, .. },
                ) = (&lhs, &rhs)
                {
                    return NormalizedBvIndexKey::Const {
                        width,
                        value: Self::normalize_bv_const(&(a - b), width),
                    };
                }
                NormalizedBvIndexKey::BvSub {
                    width,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }
            _ => NormalizedBvIndexKey::Raw(term),
        }
    }

    /// Generate array axiom clauses for QF_ABV (#4087)
    ///
    /// Collects all select/store terms and generates bit-level axioms:
    /// - ROW1: `(i == j) → select(store(a, i, v), j) == v`
    /// - ROW2: `(i != j) → select(store(a, i, v), j) == select(a, j)`
    ///   (when `select(a, j)` exists and has bits)
    /// - Functional consistency: i = j → select(a, i) = select(a, j)
    ///   (when syntactically different indices exist)
    ///
    /// Uses the same diff-variable XOR encoding as EUF congruence axioms.
    pub(in crate::executor) fn generate_array_bv_axioms(
        &self,
        bv_solver: &BvSolver<'_>,
        bv_offset: u32,
        var_offset: u32,
        extra_terms: &[TermId],
        tseitin_term_to_var: &BTreeMap<TermId, u32>,
    ) -> ArrayAxiomResult {
        let mut result = ArrayAxiomResult {
            clauses: Vec::new(),
            num_vars: 0,
        };
        // Env-gated per-section clause accounting (`--phase-trace`), matching
        // the solve_bv_core_inner phase trace. Diagnostic-only stderr comments.
        let ptrace = ay_core::misc_cli_flags().phase_trace;
        macro_rules! section_trace {
            ($name:expr) => {
                if ptrace {
                    eprintln!(
                        "c phase-trace array-axioms.{}={}",
                        $name,
                        result.clauses.len()
                    );
                }
            };
        }

        // Collect all select and store terms from assertions and extra terms
        // (e.g., assumptions in check-sat-assuming). Shared visited set prevents
        // duplicate work when an assumption term also appears in assertions.
        let mut select_terms: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut store_terms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
        let mut visited = HashSet::default();

        for &assertion in &self.ctx.assertions {
            self.collect_array_terms(assertion, &mut select_terms, &mut store_terms, &mut visited);
        }
        for &term in extra_terms {
            self.collect_array_terms(term, &mut select_terms, &mut store_terms, &mut visited);
        }

        if select_terms.is_empty() {
            return result;
        }

        let offset_bit = |bit: i32| -> i32 {
            if bit > 0 {
                bit + bv_offset as i32
            } else {
                bit - bv_offset as i32
            }
        };

        // Scalar element literals in FINAL CNF numbering. BitVec elements use
        // their bit-blasted term bits (offset into the combined numbering).
        // Bool elements have NO term bits (`ensure_term_bits` is BitVec-only):
        // their atom is the single literal from the BV solver's `bool_to_var`
        // (offset), else the Tseitin skeleton var (already final; the two are
        // linked by bv_encoding's atom-linking pass). Every consumer site
        // below previously REQUIRED term bits, so Bool-element arrays silently
        // lost their ROW1/ROW2/functional-consistency/select-over-ITE
        // consequents — each Bool select atom stayed an unconstrained fresh
        // SAT var, letting the solver return models violating array
        // congruence: wrong `sat` on UNSAT instances (the model-checker-consumer
        // bogus-Genuine-CTREX source; 8-line min repro in the group_arrays
        // regression added with this fix). A Bool select absent from BOTH
        // maps was never bit-blasted; returning None there preserves the old
        // (axiom-less) behavior for it, which adds no new constraint and
        // therefore cannot introduce wrong-UNSAT.
        let scalar_elem_lits = |t: TermId| -> Option<Vec<i32>> {
            if let Some(bits) = bv_solver.get_term_bits(t) {
                if bits.is_empty() {
                    return None;
                }
                return Some(bits.iter().map(|&b| offset_bit(b)).collect());
            }
            if *self.ctx.terms.sort(t) == Sort::Bool {
                if let Some(&l) = bv_solver.bool_to_var().get(&t) {
                    return Some(vec![offset_bit(l)]);
                }
                if let Some(&v) = tseitin_term_to_var.get(&t) {
                    return Some(vec![v as i32]);
                }
            }
            None
        };

        // Build index: array TermId → vec of selects from that array
        let mut selects_by_array: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        let mut exact_select_index: HashMap<(TermId, TermId), TermId> = HashMap::default();
        let mut normalized_select_index: HashMap<TermId, HashMap<NormalizedBvIndexKey, TermId>> =
            HashMap::default();
        for &(select_term, array, index) in &select_terms {
            selects_by_array
                .entry(array)
                .or_default()
                .push((select_term, index));
            exact_select_index
                .entry((array, index))
                .or_insert(select_term);
            normalized_select_index
                .entry(array)
                .or_default()
                .entry(self.normalize_bv_index_key(index))
                .or_insert(select_term);
        }

        let mut next_var = var_offset + 1;

        // Pre-compute normalized index keys for all select and store indices.
        // This avoids redundant O(depth) normalize_bv_index_key calls in the
        // O(N^2) functional consistency loop and O(S×R) ROW loops.
        let mut norm_key_cache: HashMap<TermId, NormalizedBvIndexKey> = HashMap::default();
        for &(_sel, _arr, idx) in &select_terms {
            norm_key_cache
                .entry(idx)
                .or_insert_with(|| self.normalize_bv_index_key(idx));
        }
        for &(_store, _base, store_idx, _val) in &store_terms {
            norm_key_cache
                .entry(store_idx)
                .or_insert_with(|| self.normalize_bv_index_key(store_idx));
        }

        section_trace!("before-row");
        // ROW1/ROW2: For each select(store(a, i, v), j)
        for &(store_term, base_array, store_idx, store_val) in &store_terms {
            let Some(selects) = selects_by_array.get(&store_term) else {
                continue;
            };

            for &(select_term, sel_idx) in selects {
                // Skip syntactically equal indices (handled by mk_select rewriting)
                if store_idx == sel_idx {
                    continue;
                }

                // Get bit representations for all terms
                let Some(idx_i_bits) = bv_solver.get_term_bits(store_idx) else {
                    continue;
                };
                let Some(idx_j_bits) = bv_solver.get_term_bits(sel_idx) else {
                    continue;
                };
                if idx_i_bits.len() != idx_j_bits.len() || idx_i_bits.is_empty() {
                    continue;
                }

                // Bool elements resolve to a single atom literal (see
                // scalar_elem_lits) — previously this bailed on missing term
                // bits, dropping ROW1+ROW2 for Bool-element arrays entirely.
                let Some(result_lits) = scalar_elem_lits(select_term) else {
                    continue;
                };
                let Some(val_lits) = scalar_elem_lits(store_val) else {
                    continue;
                };
                if result_lits.len() != val_lits.len() {
                    continue;
                }

                // Create diff variables for index bits: diff_k ↔ (i_k ⊕ j_k)
                // Skip bit positions where both are known-equal constants
                // (XOR is trivially 0, contributing nothing to "some_diff").
                let mut diff_vars = Vec::with_capacity(idx_i_bits.len());
                for (&bit_i, &bit_j) in idx_i_bits.iter().zip(idx_j_bits.iter()) {
                    let v_i = bv_solver.bit_constant_value(bit_i);
                    let v_j = bv_solver.bit_constant_value(bit_j);
                    if let (Some(ci), Some(cj)) = (v_i, v_j) {
                        if ci == cj {
                            continue; // Known-equal: XOR is always 0
                        }
                    }

                    let ob_i = offset_bit(bit_i);
                    let ob_j = offset_bit(bit_j);
                    let diff_var = next_var as i32;
                    next_var += 1;
                    diff_vars.push(diff_var);

                    // diff_k ↔ (i_k ⊕ j_k) — 4 XOR clauses
                    result
                        .clauses
                        .push(ay_core::CnfClause::new(vec![-diff_var, ob_i, ob_j]));
                    result
                        .clauses
                        .push(ay_core::CnfClause::new(vec![-diff_var, -ob_i, -ob_j]));
                    result
                        .clauses
                        .push(ay_core::CnfClause::new(vec![-ob_i, ob_j, diff_var]));
                    result
                        .clauses
                        .push(ay_core::CnfClause::new(vec![ob_i, -ob_j, diff_var]));
                }

                // If diff_vars is empty (all bits known-equal), skip this pair
                // — the indices are definitionally equal, handled by mk_select.
                if diff_vars.is_empty() {
                    continue;
                }

                // ROW1: (i == j) → (result == v)
                // Clausal: (some_diff) ∨ (result_k == v_k)
                // = (diff_0 ∨ diff_1 ∨ ... ∨ ¬result_k ∨ v_k)
                //   (diff_0 ∨ diff_1 ∨ ... ∨ result_k ∨ ¬v_k)
                let suffix_start = diff_vars.len();
                let mut clause_buf = Vec::with_capacity(suffix_start + 2);
                clause_buf.extend_from_slice(&diff_vars);
                clause_buf.push(0);
                clause_buf.push(0);

                for (&ob_r, &ob_v) in result_lits.iter().zip(val_lits.iter()) {
                    clause_buf[suffix_start] = -ob_r;
                    clause_buf[suffix_start + 1] = ob_v;
                    result
                        .clauses
                        .push(ay_core::CnfClause::new(clause_buf.clone()));

                    clause_buf[suffix_start] = ob_r;
                    clause_buf[suffix_start + 1] = -ob_v;
                    result
                        .clauses
                        .push(ay_core::CnfClause::new(clause_buf.clone()));
                }

                // ROW2: (i != j) → (result == select(a, j))
                // Only when select(base_array, sel_idx) exists and has bits.
                // Match by normalized BV index (bvadd/bvsub zero folding, concrete
                // zero_extend folding) so semantically equivalent index terms are
                // connected even when not syntactically identical.
                let norm_sel_idx = norm_key_cache
                    .get(&sel_idx)
                    .cloned()
                    .unwrap_or_else(|| self.normalize_bv_index_key(sel_idx));
                let read_term = normalized_select_index
                    .get(&base_array)
                    .and_then(|by_idx| by_idx.get(&norm_sel_idx))
                    .copied();

                if let Some(read_term) = read_term {
                    if let Some(read_lits) = scalar_elem_lits(read_term) {
                        if read_lits.len() == result_lits.len() {
                            // Create eq_idx variable: eq_idx ↔ ¬(diff_0 ∨ ... ∨ diff_n)
                            let eq_idx = next_var as i32;
                            next_var += 1;

                            // eq_idx → ¬diff_k for each k
                            for &diff_var in &diff_vars {
                                result
                                    .clauses
                                    .push(ay_core::CnfClause::new(vec![-eq_idx, -diff_var]));
                            }
                            // (diff_0 ∨ ... ∨ diff_n ∨ eq_idx)
                            let mut eq_def_clause = diff_vars.clone();
                            eq_def_clause.push(eq_idx);
                            result.clauses.push(ay_core::CnfClause::new(eq_def_clause));

                            // ROW2: ¬eq_idx → (result_k == read_k)
                            // = (eq_idx ∨ ¬result_k ∨ read_k) ∧ (eq_idx ∨ result_k ∨ ¬read_k)
                            for (&ob_r, &ob_rd) in result_lits.iter().zip(read_lits.iter()) {
                                result
                                    .clauses
                                    .push(ay_core::CnfClause::new(vec![eq_idx, -ob_r, ob_rd]));
                                result
                                    .clauses
                                    .push(ay_core::CnfClause::new(vec![eq_idx, ob_r, -ob_rd]));
                            }
                        }
                    }
                }
            }
        }

        section_trace!("after-row");
        // Select-over-ITE arrays:
        // select(ite(c, a, b), i) = ite(c, select(a, i), select(b, i)).
        //
        // `expand_select_store` intentionally avoids expanding both branches in
        // large formulas because it can duplicate deep store chains
        // exponentially. Leaving the term opaque is only sound if the bit-level
        // encoding connects it to both guarded branch reads.
        for &(select_term, array, sel_idx) in &select_terms {
            let TermData::Ite(cond, then_array, else_array) = self.ctx.terms.get(array) else {
                continue;
            };
            let Some(&cond_var) = tseitin_term_to_var.get(cond) else {
                continue;
            };

            let Some(&then_read) = exact_select_index.get(&(*then_array, sel_idx)) else {
                continue;
            };
            let Some(&else_read) = exact_select_index.get(&(*else_array, sel_idx)) else {
                continue;
            };

            // Bool elements resolve to a single atom literal (see
            // scalar_elem_lits) — previously this bailed on missing term bits,
            // leaving a Bool select-over-ITE-array disconnected from both
            // guarded branch reads.
            let Some(result_lits) = scalar_elem_lits(select_term) else {
                continue;
            };
            let Some(then_lits) = scalar_elem_lits(then_read) else {
                continue;
            };
            let Some(else_lits) = scalar_elem_lits(else_read) else {
                continue;
            };
            if result_lits.len() != then_lits.len() || result_lits.len() != else_lits.len() {
                continue;
            }

            let cond_lit = cond_var as i32;
            for ((&ob_r, &ob_then), &ob_else) in result_lits
                .iter()
                .zip(then_lits.iter())
                .zip(else_lits.iter())
            {
                // cond -> result == then_read
                result
                    .clauses
                    .push(ay_core::CnfClause::new(vec![-cond_lit, -ob_r, ob_then]));
                result
                    .clauses
                    .push(ay_core::CnfClause::new(vec![-cond_lit, ob_r, -ob_then]));
                // !cond -> result == else_read
                result
                    .clauses
                    .push(ay_core::CnfClause::new(vec![cond_lit, -ob_r, ob_else]));
                result
                    .clauses
                    .push(ay_core::CnfClause::new(vec![cond_lit, ob_r, -ob_else]));
            }
        }

        section_trace!("after-select-over-ite");
        // Packed finite-array lookup bridge:
        //
        // For a packed word such as:
        //   pack = concat(select(a,#b1), select(a,#b0))
        //   got  = extract[W-1:0](bvlshr(pack, zero_extend(i)))
        //
        // add, for each concrete lane k:
        //   i = k -> got = select(a,k)
        //
        // This is a direct bit-level encoding of the packed layout. Existing
        // array FC clauses then connect select(a,i) to the same concrete lane,
        // closing QF_ABV obligations without trusting model reconstruction.
        let mut all_terms = Vec::new();
        let mut all_terms_seen = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_all_terms(assertion, &mut all_terms, &mut all_terms_seen);
        }
        for &term in extra_terms {
            self.collect_all_terms(term, &mut all_terms, &mut all_terms_seen);
        }
        let packed_words = self.build_packed_array_word_map(&all_terms);
        let source_upper_bounds = self.build_nonnegative_upper_bounds();

        let mut packed_bridge_seen: HashSet<(TermId, TermId, TermId)> = HashSet::default();
        let packed_debug = debug_abv_packed_lookup();
        let mut packed_detected = 0usize;
        let mut packed_emitted_clauses = 0usize;
        for &lookup_term in &all_terms {
            let detected = self
                .detect_packed_array_lookup(lookup_term)
                .or_else(|| self.detect_packed_array_shift_lookup(lookup_term));
            let Some((array, index_term, lane_selects)) = detected else {
                continue;
            };
            packed_detected += 1;
            let Some(raw_lookup_bits) = bv_solver.get_term_bits(lookup_term) else {
                if packed_debug {
                    safe_eprintln!("[abv-packed] skip term {:?}: no lookup bits", lookup_term);
                }
                continue;
            };
            let Some(index_bits) = bv_solver.get_term_bits(index_term) else {
                if packed_debug {
                    safe_eprintln!(
                        "[abv-packed] skip term {:?}: no index bits for {:?}",
                        lookup_term,
                        index_term
                    );
                }
                continue;
            };
            if raw_lookup_bits.is_empty() || index_bits.is_empty() {
                continue;
            }

            for (lane, lane_select) in lane_selects.into_iter().enumerate() {
                if !packed_bridge_seen.insert((lookup_term, index_term, lane_select)) {
                    continue;
                }
                let Some(lane_bits) = bv_solver.get_term_bits(lane_select) else {
                    continue;
                };
                if raw_lookup_bits.len() < lane_bits.len() || lane_bits.is_empty() {
                    if packed_debug {
                        safe_eprintln!(
                            "[abv-packed] skip term {:?} lane {:?}: widths lookup={} lane={}",
                            lookup_term,
                            lane_select,
                            raw_lookup_bits.len(),
                            lane_bits.len()
                        );
                    }
                    continue;
                }
                let lookup_bits = &raw_lookup_bits[..lane_bits.len()];

                let mut guard_neg_lits = Vec::with_capacity(index_bits.len());
                let mut lane_possible = true;
                for (bit_pos, &idx_bit) in index_bits.iter().enumerate() {
                    let want_one =
                        bit_pos < usize::BITS as usize && ((lane >> bit_pos) & 1usize) == 1usize;
                    if let Some(actual) = bv_solver.bit_constant_value(idx_bit) {
                        if actual != want_one {
                            lane_possible = false;
                            break;
                        }
                        continue;
                    }

                    let idx_lit = offset_bit(idx_bit);
                    guard_neg_lits.push(if want_one { -idx_lit } else { idx_lit });
                }
                if !lane_possible {
                    continue;
                }

                for (&lookup_bit, &lane_bit) in lookup_bits.iter().zip(lane_bits.iter()) {
                    let ob_lookup = offset_bit(lookup_bit);
                    let ob_lane = offset_bit(lane_bit);

                    let mut clause = guard_neg_lits.clone();
                    clause.push(-ob_lookup);
                    clause.push(ob_lane);
                    result.clauses.push(ay_core::CnfClause::new(clause));
                    packed_emitted_clauses += 1;

                    let mut clause = guard_neg_lits.clone();
                    clause.push(ob_lookup);
                    clause.push(-ob_lane);
                    result.clauses.push(ay_core::CnfClause::new(clause));
                    packed_emitted_clauses += 1;
                }

                let symbolic_select = exact_select_index.get(&(array, index_term)).copied();
                if let Some(symbolic_select) = symbolic_select {
                    if symbolic_select != lane_select {
                        if let Some(symbolic_bits) = bv_solver.get_term_bits(symbolic_select) {
                            if symbolic_bits.len() == lookup_bits.len() {
                                for (&lookup_bit, &symbolic_bit) in
                                    lookup_bits.iter().zip(symbolic_bits.iter())
                                {
                                    let ob_lookup = offset_bit(lookup_bit);
                                    let ob_symbolic = offset_bit(symbolic_bit);

                                    let mut clause = guard_neg_lits.clone();
                                    clause.push(-ob_lookup);
                                    clause.push(ob_symbolic);
                                    result.clauses.push(ay_core::CnfClause::new(clause));
                                    packed_emitted_clauses += 1;

                                    let mut clause = guard_neg_lits.clone();
                                    clause.push(ob_lookup);
                                    clause.push(-ob_symbolic);
                                    result.clauses.push(ay_core::CnfClause::new(clause));
                                    packed_emitted_clauses += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
        if packed_debug {
            safe_eprintln!(
                "[abv-packed] detected={} emitted_clauses={}",
                packed_detected,
                packed_emitted_clauses
            );
        }

        section_trace!("after-packed-lookup");
        // Lowered packed-mux bridge:
        //
        // Some QF_ABV inputs lower:
        //   select(a, ((_ extract n 0) x))
        // into a Boolean ITE tree whose leaves read individual bits from
        // packed constant-index selects. The path bits already imply the
        // concrete lane, so add guarded FC clauses:
        //   path_bits(x == k) -> select(a,k) == select(a, ((_ extract n 0) x))
        //
        // This is a fail-closed array axiom shortcut: it does not assume the
        // mux result is well-formed, only that the low-index path bits imply
        // the same concrete lane used by an existing packed select.
        if !packed_words.is_empty() {
            let mut mux_bridge_candidates = Vec::new();
            for &assertion in &self.ctx.assertions {
                self.collect_mux_packed_leaf_bridge_candidates(
                    assertion,
                    &packed_words,
                    None,
                    true,
                    &mut Vec::new(),
                    &mut Vec::new(),
                    &mut mux_bridge_candidates,
                );
            }
            for &term in extra_terms {
                self.collect_mux_packed_leaf_bridge_candidates(
                    term,
                    &packed_words,
                    None,
                    false,
                    &mut Vec::new(),
                    &mut Vec::new(),
                    &mut mux_bridge_candidates,
                );
            }
            let mut mux_output_bridge_candidates = Vec::new();
            for &assertion in &self.ctx.assertions {
                self.collect_positive_mux_output_bridge_candidates(
                    assertion,
                    &packed_words,
                    None,
                    &mut mux_output_bridge_candidates,
                );
            }

            let mut mux_bridge_seen: HashSet<(TermId, TermId, usize)> = HashSet::default();
            let mut mux_target_bridge_seen: HashSet<(TermId, TermId, usize, Vec<i32>)> =
                HashSet::default();
            let mut mux_target_full_coverage: HashMap<
                (TermId, TermId, TermId, usize),
                MuxTargetCoverage,
            > = HashMap::default();
            let mut mux_emitted_clauses = 0usize;
            let mut mux_clause_limit_hit = false;
            {
                for (bit_guards, eq_guards, target_bit, leaf) in &mux_bridge_candidates {
                    if mux_clause_limit_hit {
                        break;
                    }
                    if leaf.bit_pos >= leaf.elem_width as usize {
                        continue;
                    }
                    if leaf.index_width >= usize::BITS || leaf.lane >= (1usize << leaf.index_width)
                    {
                        continue;
                    }

                    let mut sources = Vec::new();
                    for guard in bit_guards {
                        if guard.bit_pos < leaf.index_width && !sources.contains(&guard.source) {
                            sources.push(guard.source);
                        }
                    }

                    for source in sources {
                        let mut low_guards = vec![None; leaf.index_width as usize];
                        let mut conflicted = false;
                        for guard in bit_guards.iter().filter(|guard| {
                            guard.source == source && guard.bit_pos < leaf.index_width
                        }) {
                            let slot = &mut low_guards[guard.bit_pos as usize];
                            if let Some((_, want_one)) = slot {
                                if *want_one != guard.want_one {
                                    conflicted = true;
                                    break;
                                }
                            } else {
                                *slot = Some((guard.bit_term, guard.want_one));
                            }
                        }
                        if conflicted || low_guards.iter().any(Option::is_none) {
                            continue;
                        }

                        let mut guard_neg_lits = Vec::with_capacity(leaf.index_width as usize);
                        let mut guard_possible = true;
                        for (bit_pos, guard) in low_guards.into_iter().enumerate() {
                            let (bit_term, want_one) = guard.expect("checked complete low guards");
                            let lane_want_one = ((leaf.lane >> bit_pos) & 1usize) == 1usize;
                            if lane_want_one != want_one {
                                guard_possible = false;
                                break;
                            }

                            let Some(bit_bits) = bv_solver.get_term_bits(bit_term) else {
                                guard_possible = false;
                                break;
                            };
                            if bit_bits.len() != 1 {
                                guard_possible = false;
                                break;
                            }
                            if let Some(actual) = bv_solver.bit_constant_value(bit_bits[0]) {
                                if actual != want_one {
                                    guard_possible = false;
                                    break;
                                }
                                continue;
                            }

                            let bit_lit = offset_bit(bit_bits[0]);
                            guard_neg_lits.push(if want_one { -bit_lit } else { bit_lit });
                        }
                        if !guard_possible {
                            continue;
                        }
                        if !self.bit_guards_are_implied_by_lane(
                            bit_guards,
                            source,
                            leaf.index_width,
                            leaf.lane,
                        ) || !self.eq_guards_are_implied_by_lane(
                            eq_guards,
                            source,
                            leaf.index_width,
                            leaf.lane,
                        ) {
                            continue;
                        }

                        let Some(symbolic_select) = self.find_symbolic_select_for_source(
                            &exact_select_index,
                            leaf.array,
                            source,
                            leaf.index_width,
                        ) else {
                            continue;
                        };
                        if leaf.lane_select != symbolic_select
                            && mux_bridge_seen.insert((
                                leaf.lane_select,
                                symbolic_select,
                                leaf.lane,
                            ))
                        {
                            if let (Some(lane_bits), Some(symbolic_bits)) = (
                                bv_solver.get_term_bits(leaf.lane_select),
                                bv_solver.get_term_bits(symbolic_select),
                            ) {
                                if !lane_bits.is_empty() && lane_bits.len() == symbolic_bits.len() {
                                    for (&lane_bit, &symbolic_bit) in
                                        lane_bits.iter().zip(symbolic_bits.iter())
                                    {
                                        if mux_emitted_clauses + 2 > PACKED_MUX_BRIDGE_CLAUSE_LIMIT
                                        {
                                            mux_clause_limit_hit = true;
                                            break;
                                        }
                                        push_guarded_bit_eq(
                                            &mut result,
                                            bv_offset,
                                            &guard_neg_lits,
                                            lane_bit,
                                            symbolic_bit,
                                            &mut mux_emitted_clauses,
                                        );
                                    }
                                }
                            }
                        }
                        if mux_clause_limit_hit {
                            break;
                        }

                        if let Some(target_bit) = target_bit {
                            if mux_target_bridge_seen.insert((
                                *target_bit,
                                symbolic_select,
                                leaf.bit_pos,
                                guard_neg_lits.clone(),
                            )) {
                                let Some(target_bits) = bv_solver.get_term_bits(*target_bit) else {
                                    continue;
                                };
                                let Some(symbolic_bits) = bv_solver.get_term_bits(symbolic_select)
                                else {
                                    continue;
                                };
                                if target_bits.len() != 1 || leaf.bit_pos >= symbolic_bits.len() {
                                    continue;
                                }
                                if mux_emitted_clauses + 2 > PACKED_MUX_BRIDGE_CLAUSE_LIMIT {
                                    mux_clause_limit_hit = true;
                                    break;
                                }
                                push_guarded_bit_eq(
                                    &mut result,
                                    bv_offset,
                                    &guard_neg_lits,
                                    target_bits[0],
                                    symbolic_bits[leaf.bit_pos],
                                    &mut mux_emitted_clauses,
                                );
                                if leaf.index_width < u128::BITS && leaf.lane < u128::BITS as usize
                                {
                                    let entry = mux_target_full_coverage
                                        .entry((*target_bit, symbolic_select, source, leaf.bit_pos))
                                        .or_insert_with(|| MuxTargetCoverage {
                                            source,
                                            target_bit: target_bits[0],
                                            symbolic_bit: symbolic_bits[leaf.bit_pos],
                                            index_width: leaf.index_width,
                                            lanes_mask: 0,
                                        });
                                    if entry.target_bit == target_bits[0]
                                        && entry.symbolic_bit == symbolic_bits[leaf.bit_pos]
                                        && entry.index_width == leaf.index_width
                                    {
                                        entry.lanes_mask |= 1u128 << leaf.lane;
                                    }
                                }
                            }
                        }
                    }
                    if mux_clause_limit_hit {
                        break;
                    }

                    for guard in eq_guards {
                        let lane_value = BigInt::from(leaf.lane);
                        let guard_identifies_lane = guard.width == leaf.index_width
                            && if guard.cond_is_true {
                                guard.value == lane_value
                            } else {
                                leaf.index_width == 1 && guard.value != lane_value
                            };
                        if !guard_identifies_lane
                            || !self.bit_guards_are_implied_by_lane(
                                bit_guards,
                                guard.index,
                                leaf.index_width,
                                leaf.lane,
                            )
                            || !self.eq_guards_identify_lane(
                                eq_guards,
                                guard.index,
                                leaf.index_width,
                                leaf.lane,
                            )
                        {
                            continue;
                        }
                        let Some(&symbolic_select) =
                            exact_select_index.get(&(leaf.array, guard.index))
                        else {
                            continue;
                        };
                        let mut guard_neg_lits = Vec::with_capacity(eq_guards.len());
                        let mut all_eq_guard_lits_available = true;
                        for path_guard in eq_guards {
                            let Some(&cond_var) = tseitin_term_to_var.get(&path_guard.cond) else {
                                all_eq_guard_lits_available = false;
                                break;
                            };
                            let cond_lit = cond_var as i32;
                            guard_neg_lits.push(if path_guard.cond_is_true {
                                -cond_lit
                            } else {
                                cond_lit
                            });
                        }
                        if !all_eq_guard_lits_available {
                            continue;
                        }
                        if leaf.lane_select != symbolic_select
                            && mux_bridge_seen.insert((
                                leaf.lane_select,
                                symbolic_select,
                                leaf.lane,
                            ))
                        {
                            if let (Some(lane_bits), Some(symbolic_bits)) = (
                                bv_solver.get_term_bits(leaf.lane_select),
                                bv_solver.get_term_bits(symbolic_select),
                            ) {
                                if !lane_bits.is_empty() && lane_bits.len() == symbolic_bits.len() {
                                    for (&lane_bit, &symbolic_bit) in
                                        lane_bits.iter().zip(symbolic_bits.iter())
                                    {
                                        if mux_emitted_clauses + 2 > PACKED_MUX_BRIDGE_CLAUSE_LIMIT
                                        {
                                            mux_clause_limit_hit = true;
                                            break;
                                        }
                                        push_guarded_bit_eq(
                                            &mut result,
                                            bv_offset,
                                            &guard_neg_lits,
                                            lane_bit,
                                            symbolic_bit,
                                            &mut mux_emitted_clauses,
                                        );
                                    }
                                }
                            }
                        }
                        if mux_clause_limit_hit {
                            break;
                        }

                        if let Some(target_bit) = target_bit {
                            if mux_target_bridge_seen.insert((
                                *target_bit,
                                symbolic_select,
                                leaf.bit_pos,
                                guard_neg_lits.clone(),
                            )) {
                                let Some(target_bits) = bv_solver.get_term_bits(*target_bit) else {
                                    continue;
                                };
                                let Some(symbolic_bits) = bv_solver.get_term_bits(symbolic_select)
                                else {
                                    continue;
                                };
                                if target_bits.len() != 1 || leaf.bit_pos >= symbolic_bits.len() {
                                    continue;
                                }
                                if mux_emitted_clauses + 2 > PACKED_MUX_BRIDGE_CLAUSE_LIMIT {
                                    mux_clause_limit_hit = true;
                                    break;
                                }
                                push_guarded_bit_eq(
                                    &mut result,
                                    bv_offset,
                                    &guard_neg_lits,
                                    target_bits[0],
                                    symbolic_bits[leaf.bit_pos],
                                    &mut mux_emitted_clauses,
                                );
                                if leaf.index_width < u128::BITS && leaf.lane < u128::BITS as usize
                                {
                                    let entry = mux_target_full_coverage
                                        .entry((
                                            *target_bit,
                                            symbolic_select,
                                            guard.index,
                                            leaf.bit_pos,
                                        ))
                                        .or_insert_with(|| MuxTargetCoverage {
                                            source: guard.index,
                                            target_bit: target_bits[0],
                                            symbolic_bit: symbolic_bits[leaf.bit_pos],
                                            index_width: leaf.index_width,
                                            lanes_mask: 0,
                                        });
                                    if entry.target_bit == target_bits[0]
                                        && entry.symbolic_bit == symbolic_bits[leaf.bit_pos]
                                        && entry.index_width == leaf.index_width
                                    {
                                        entry.lanes_mask |= 1u128 << leaf.lane;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            for candidate in &mux_output_bridge_candidates {
                if mux_clause_limit_hit {
                    break;
                }
                let leaf = &candidate.leaf;
                if leaf.bit_pos >= leaf.elem_width as usize {
                    continue;
                }
                if leaf.index_width >= usize::BITS || leaf.lane >= (1usize << leaf.index_width) {
                    continue;
                }

                let mut sources = Vec::new();
                for guard in &candidate.bit_guards {
                    if guard.bit_pos < leaf.index_width && !sources.contains(&guard.source) {
                        sources.push(guard.source);
                    }
                }

                for source in sources {
                    let mut low_guards = vec![None; leaf.index_width as usize];
                    let mut conflicted = false;
                    for guard in candidate
                        .bit_guards
                        .iter()
                        .filter(|guard| guard.source == source && guard.bit_pos < leaf.index_width)
                    {
                        let slot = &mut low_guards[guard.bit_pos as usize];
                        if let Some((_, want_one)) = slot {
                            if *want_one != guard.want_one {
                                conflicted = true;
                                break;
                            }
                        } else {
                            *slot = Some((guard.bit_term, guard.want_one));
                        }
                    }
                    if conflicted || low_guards.iter().any(Option::is_none) {
                        continue;
                    }

                    let mut guard_neg_lits = Vec::with_capacity(leaf.index_width as usize);
                    let mut guard_possible = true;
                    for (bit_pos, guard) in low_guards.into_iter().enumerate() {
                        let (bit_term, want_one) = guard.expect("checked complete low guards");
                        let lane_want_one = ((leaf.lane >> bit_pos) & 1usize) == 1usize;
                        if lane_want_one != want_one {
                            guard_possible = false;
                            break;
                        }

                        let Some(bit_bits) = bv_solver.get_term_bits(bit_term) else {
                            guard_possible = false;
                            break;
                        };
                        if bit_bits.len() != 1 {
                            guard_possible = false;
                            break;
                        }
                        if let Some(actual) = bv_solver.bit_constant_value(bit_bits[0]) {
                            if actual != want_one {
                                guard_possible = false;
                                break;
                            }
                            continue;
                        }

                        let bit_lit = offset_bit(bit_bits[0]);
                        guard_neg_lits.push(if want_one { -bit_lit } else { bit_lit });
                    }
                    if !guard_possible {
                        continue;
                    }
                    if !self.bit_guards_are_implied_by_lane(
                        &candidate.bit_guards,
                        source,
                        leaf.index_width,
                        leaf.lane,
                    ) || !self.eq_guards_are_implied_by_lane(
                        &candidate.eq_guards,
                        source,
                        leaf.index_width,
                        leaf.lane,
                    ) {
                        continue;
                    }

                    let Some(symbolic_select) = self.find_symbolic_select_for_source(
                        &exact_select_index,
                        leaf.array,
                        source,
                        leaf.index_width,
                    ) else {
                        continue;
                    };
                    if mux_target_bridge_seen.insert((
                        candidate.output,
                        symbolic_select,
                        leaf.bit_pos,
                        guard_neg_lits.clone(),
                    )) {
                        let Some(output_bits) = bv_solver.get_term_bits(candidate.output) else {
                            continue;
                        };
                        let Some(symbolic_bits) = bv_solver.get_term_bits(symbolic_select) else {
                            continue;
                        };
                        if output_bits.len() != symbolic_bits.len()
                            || leaf.bit_pos >= output_bits.len()
                            || leaf.bit_pos >= symbolic_bits.len()
                        {
                            continue;
                        }
                        if mux_emitted_clauses + 2 > PACKED_MUX_BRIDGE_CLAUSE_LIMIT {
                            mux_clause_limit_hit = true;
                            break;
                        }
                        push_guarded_bit_eq(
                            &mut result,
                            bv_offset,
                            &guard_neg_lits,
                            output_bits[leaf.bit_pos],
                            symbolic_bits[leaf.bit_pos],
                            &mut mux_emitted_clauses,
                        );
                        if leaf.index_width < u128::BITS && leaf.lane < u128::BITS as usize {
                            let entry = mux_target_full_coverage
                                .entry((candidate.output, symbolic_select, source, leaf.bit_pos))
                                .or_insert_with(|| MuxTargetCoverage {
                                    source,
                                    target_bit: output_bits[leaf.bit_pos],
                                    symbolic_bit: symbolic_bits[leaf.bit_pos],
                                    index_width: leaf.index_width,
                                    lanes_mask: 0,
                                });
                            if entry.target_bit == output_bits[leaf.bit_pos]
                                && entry.symbolic_bit == symbolic_bits[leaf.bit_pos]
                                && entry.index_width == leaf.index_width
                            {
                                entry.lanes_mask |= 1u128 << leaf.lane;
                            }
                        }
                    }
                }
                if mux_clause_limit_hit {
                    break;
                }

                for guard in &candidate.eq_guards {
                    let lane_value = BigInt::from(leaf.lane);
                    let guard_identifies_lane = guard.width == leaf.index_width
                        && if guard.cond_is_true {
                            guard.value == lane_value
                        } else {
                            leaf.index_width == 1 && guard.value != lane_value
                        };
                    if !guard_identifies_lane
                        || !self.bit_guards_are_implied_by_lane(
                            &candidate.bit_guards,
                            guard.index,
                            leaf.index_width,
                            leaf.lane,
                        )
                        || !self.eq_guards_identify_lane(
                            &candidate.eq_guards,
                            guard.index,
                            leaf.index_width,
                            leaf.lane,
                        )
                    {
                        continue;
                    }
                    let Some(&symbolic_select) = exact_select_index.get(&(leaf.array, guard.index))
                    else {
                        continue;
                    };
                    let mut guard_neg_lits = Vec::with_capacity(candidate.eq_guards.len());
                    let mut all_eq_guard_lits_available = true;
                    for path_guard in &candidate.eq_guards {
                        let Some(&cond_var) = tseitin_term_to_var.get(&path_guard.cond) else {
                            all_eq_guard_lits_available = false;
                            break;
                        };
                        let cond_lit = cond_var as i32;
                        guard_neg_lits.push(if path_guard.cond_is_true {
                            -cond_lit
                        } else {
                            cond_lit
                        });
                    }
                    if !all_eq_guard_lits_available {
                        continue;
                    }
                    if mux_target_bridge_seen.insert((
                        candidate.output,
                        symbolic_select,
                        leaf.bit_pos,
                        guard_neg_lits.clone(),
                    )) {
                        let Some(output_bits) = bv_solver.get_term_bits(candidate.output) else {
                            continue;
                        };
                        let Some(symbolic_bits) = bv_solver.get_term_bits(symbolic_select) else {
                            continue;
                        };
                        if output_bits.len() != symbolic_bits.len()
                            || leaf.bit_pos >= output_bits.len()
                            || leaf.bit_pos >= symbolic_bits.len()
                        {
                            continue;
                        }
                        if mux_emitted_clauses + 2 > PACKED_MUX_BRIDGE_CLAUSE_LIMIT {
                            mux_clause_limit_hit = true;
                            break;
                        }
                        push_guarded_bit_eq(
                            &mut result,
                            bv_offset,
                            &guard_neg_lits,
                            output_bits[leaf.bit_pos],
                            symbolic_bits[leaf.bit_pos],
                            &mut mux_emitted_clauses,
                        );
                        if leaf.index_width < u128::BITS && leaf.lane < u128::BITS as usize {
                            let entry = mux_target_full_coverage
                                .entry((
                                    candidate.output,
                                    symbolic_select,
                                    guard.index,
                                    leaf.bit_pos,
                                ))
                                .or_insert_with(|| MuxTargetCoverage {
                                    source: guard.index,
                                    target_bit: output_bits[leaf.bit_pos],
                                    symbolic_bit: symbolic_bits[leaf.bit_pos],
                                    index_width: leaf.index_width,
                                    lanes_mask: 0,
                                });
                            if entry.target_bit == output_bits[leaf.bit_pos]
                                && entry.symbolic_bit == symbolic_bits[leaf.bit_pos]
                                && entry.index_width == leaf.index_width
                            {
                                entry.lanes_mask |= 1u128 << leaf.lane;
                            }
                        }
                    }
                }
            }
            for coverage in mux_target_full_coverage.values() {
                if mux_clause_limit_hit {
                    break;
                }
                if coverage.index_width > 7 {
                    continue;
                }
                let lane_count = 1u32 << coverage.index_width;
                let full_mask = if lane_count == u128::BITS {
                    u128::MAX
                } else {
                    (1u128 << lane_count) - 1
                };
                let range_mask =
                    source_upper_bounds
                        .get(&coverage.source)
                        .and_then(|&upper_bound| {
                            let lane_count = lane_count as usize;
                            (upper_bound < lane_count).then(|| {
                                if upper_bound + 1 == u128::BITS as usize {
                                    u128::MAX
                                } else {
                                    (1u128 << (upper_bound + 1)) - 1
                                }
                            })
                        });
                let required_mask = range_mask.unwrap_or(full_mask);
                if coverage.lanes_mask & required_mask != required_mask {
                    continue;
                }
                if mux_emitted_clauses + 2 > PACKED_MUX_BRIDGE_CLAUSE_LIMIT {
                    mux_clause_limit_hit = true;
                    break;
                }
                push_guarded_bit_eq(
                    &mut result,
                    bv_offset,
                    &[],
                    coverage.target_bit,
                    coverage.symbolic_bit,
                    &mut mux_emitted_clauses,
                );
            }
            if packed_debug {
                safe_eprintln!(
                    "[abv-packed-mux] candidates={} emitted_clauses={} candidate_limit_hit={} clause_limit_hit={}",
                    mux_bridge_candidates.len(),
                    mux_emitted_clauses,
                    mux_bridge_candidates.len() >= PACKED_MUX_BRIDGE_CANDIDATE_LIMIT,
                    mux_clause_limit_hit
                );
            }
        }

        section_trace!("after-packed-mux");
        // Functional consistency: for selects on the same array with different
        // syntactic indices, add (i == j) → (select(a, i) == select(a, j))
        //
        // Optimization 1 (#8286): base-grouped FC with budget. Group indices by
        // their symbolic base (e.g., all `p0 + c` share base `p0`). Generate FC
        // axioms in two phases:
        // Phase 1: same-base pairs (e.g., p0+1 vs p0+2) — high priority, most
        //   likely to alias. These are the pairs that matter for byte-level memory
        //   access patterns.
        // Phase 2: cross-base pairs (e.g., p0+1 vs p1+2) — lower priority, only
        //   generated up to a per-array budget. On formulas with many symbolic
        //   bases (N pointers × M accesses each), this reduces O((N*M)^2) pairs
        //   to O(N*M^2 + budget) pairs.
        //
        // Optimization 2: skip pairs where both indices are fully-constant and
        // distinct — they can never be equal, so functional consistency is
        // vacuously satisfied. This avoids O(N^2) axiom explosion on benchmarks
        // with many constant-indexed selects (e.g., egt-3092 has 34 selects on
        // one array at mostly-distinct constant addresses).
        //
        // Optimization 3: for non-constant pairs, skip diff variable creation
        // for bit positions where both indices have the same known constant
        // value — those bits can never differ, so the XOR is always false.
        //
        // Per-array FC pair budget for cross-base pairs (#8286). Same-base pairs
        // are high-priority (most likely to alias); cross-base pairs are capped
        // at this budget per array to prevent O(N^2) explosion. Env-tunable
        // (#dt-array-fc-lazy): lowering these sheds the eager FC clause mass to
        // the lazy Phase 10.7 CEGAR loop.
        let fc_cross_base_budget_per_array: usize = fc_budget_env("AY_FC_CROSS_BUDGET", 200);
        // Same-base pairs are ALSO budgeted (previously unlimited). SOUND: FC
        // axioms are entailed by the array theory, so emitting fewer eagerly
        // only over-approximates; the Phase 10.7 CEGAR loop (#8510) lazily adds
        // any FC axiom the model actually violates, and its exhaustion path
        // fail-closes a still-violating model to Unknown, so a wrong SAT cannot
        // escape. Generous enough that typical instances never hit it.
        let fc_same_base_budget_per_array: usize = fc_budget_env("AY_FC_SAME_BUDGET", 10_000);
        // GLOBAL FC pair budget across ALL arrays. Per-array budgets do not
        // protect a BMC-style instance where SSA versioning mints a fresh array
        // TermId per store/merge: the aterm parser-dispatch instance has 1259
        // arrays with >500 candidate pairs each, so 200 cross-base pairs/array
        // still emitted ~250K pairs x ~344 clauses/pair = 86M clauses (43% of a
        // 200M-clause CNF; memout). Pairs beyond this global cap are left to
        // the CEGAR refinement — same soundness argument as the per-array caps.
        // Lower it (`--fc-global-budget 2000`) to make a huge-array instance
        // solve its base CNF first and lazily refine FC on demand.
        let fc_budget_cli = ay_core::misc_cli_flags().fc_global_budget;
        let mut fc_global_pair_budget: usize = fc_budget_cli.unwrap_or(30_000);
        // AUTO-SCALE for the many-array BMC class (#dt-array-fc-autoscale). A BMC
        // instance that mints thousands of SSA array versions generates a
        // candidate FC set whose clause mass drowns the CDCL even at the global
        // cap (the aterm parser instance: ~1259 arrays -> ~10M FC clauses on top
        // of a 20M-clause base -> CDCL never finishes in 5.6h). When there are
        // MANY distinct arrays with reads AND the user did not set the budget
        // explicitly, auto-lower it so the FC mass defers to the lazy Phase 10.7
        // loop (which adds only the pairs a model actually violates). Keyed on
        // ARRAY COUNT, not raw pair count, so a SINGLE big-array case (e.g. a
        // csplit-style array with thousands of constant selects, which needs its
        // eager FC) is NOT affected. Sound: identical lazy-refinement +
        // fail-closed-to-Unknown safety net as any FC truncation.
        if fc_budget_cli.is_none() {
            const FC_AUTOSCALE_ARRAY_THRESHOLD: usize = 500;
            const FC_AUTOSCALE_BUDGET: usize = 2_000;
            let arrays_with_reads = selects_by_array.values().filter(|s| s.len() >= 2).count();
            if arrays_with_reads > FC_AUTOSCALE_ARRAY_THRESHOLD
                && fc_global_pair_budget > FC_AUTOSCALE_BUDGET
            {
                if ay_core::misc_cli_flags().phase_trace {
                    eprintln!(
                        "c phase-trace fc-autoscale arrays={arrays_with_reads} budget {fc_global_pair_budget}->{FC_AUTOSCALE_BUDGET}"
                    );
                }
                fc_global_pair_budget = FC_AUTOSCALE_BUDGET;
            }
        }
        let mut fc_global_pairs_emitted: usize = 0;
        let mut fc_global_pairs_skipped: usize = 0;

        for (&array, selects) in &selects_by_array {
            if selects.len() < 2 {
                continue;
            }

            // Collect FC candidate pairs, separated by priority (#8286).
            // Same-base pairs first (always generated), cross-base second (budgeted).
            let mut finite_domain_pairs: Vec<(usize, usize)> = Vec::new();
            let mut same_base_pairs: Vec<(usize, usize)> = Vec::new();
            let mut cross_base_pairs: Vec<(usize, usize)> = Vec::new();
            let mut finite_pair_seen: HashSet<(usize, usize)> = HashSet::default();

            // Small finite BV-index arrays are common for packed-word memory
            // encodings. Make FC complete between symbolic base-array reads and
            // existing constant-index reads so pairs like
            // select(a, ((_ extract 3 0) i)) vs select(a, #x3) are never lost to
            // the cross-base budget.
            let finite_domain_complete = matches!(self.ctx.terms.get(array), TermData::Var(_, _))
                && matches!(
                    self.ctx.terms.sort(array),
                    Sort::Array(arr_sort)
                        if matches!(&arr_sort.index_sort, Sort::BitVec(idx_bv) if idx_bv.width <= 4)
                );

            if finite_domain_complete {
                for i in 0..selects.len() {
                    for j in (i + 1)..selects.len() {
                        let (_sel1, idx1) = selects[i];
                        let (_sel2, idx2) = selects[j];
                        if idx1 == idx2 {
                            continue;
                        }
                        let idx1_const = matches!(
                            self.ctx.terms.get(idx1),
                            TermData::Const(Constant::BitVec { .. })
                        );
                        let idx2_const = matches!(
                            self.ctx.terms.get(idx2),
                            TermData::Const(Constant::BitVec { .. })
                        );
                        if idx1_const ^ idx2_const {
                            finite_pair_seen.insert((i, j));
                            finite_domain_pairs.push((i, j));
                        }
                    }
                }
            }

            for i in 0..selects.len() {
                for j in (i + 1)..selects.len() {
                    let (_sel1, idx1) = selects[i];
                    let (_sel2, idx2) = selects[j];
                    if idx1 == idx2 {
                        continue;
                    }
                    if finite_pair_seen.contains(&(i, j)) {
                        continue;
                    }

                    // Classify as same-base or cross-base using normalized keys.
                    let shares_base = norm_key_cache
                        .get(&idx1)
                        .zip(norm_key_cache.get(&idx2))
                        .is_some_and(|(nk1, nk2)| nk1.shares_base_with(nk2));

                    if shares_base {
                        same_base_pairs.push((i, j));
                    } else {
                        cross_base_pairs.push((i, j));
                    }
                }
            }

            // Process same-base pairs (up to their budget — high priority),
            // then cross-base pairs (up to their budget). Anything past a
            // budget is left to the Phase 10.7 CEGAR FC refinement.
            let same_base_limit = fc_same_base_budget_per_array.min(same_base_pairs.len());
            let cross_base_limit = fc_cross_base_budget_per_array.min(cross_base_pairs.len());
            if ptrace && same_base_limit < same_base_pairs.len() {
                // No silent caps: make the truncation visible in the trace.
                eprintln!(
                    "c phase-trace array-axioms.fc-same-base-truncated kept={} of {}",
                    same_base_limit,
                    same_base_pairs.len()
                );
            }
            if ptrace && (same_base_pairs.len() + cross_base_pairs.len() > 500) {
                eprintln!(
                    "c phase-trace array-axioms.fc-array selects={} finite={} same_base={} cross_base={} clauses_so_far={}",
                    selects.len(),
                    finite_domain_pairs.len(),
                    same_base_pairs.len(),
                    cross_base_pairs.len(),
                    result.clauses.len()
                );
            }
            let all_pairs = finite_domain_pairs
                .iter()
                .chain(same_base_pairs[..same_base_limit].iter())
                .chain(cross_base_pairs[..cross_base_limit].iter());

            for &(i, j) in all_pairs {
                // Global FC budget (see FC_GLOBAL_PAIR_BUDGET): pairs beyond it
                // are counted (reported below — no silent caps) and left to the
                // CEGAR refinement.
                if fc_global_pairs_emitted >= fc_global_pair_budget {
                    fc_global_pairs_skipped += 1;
                    continue;
                }
                fc_global_pairs_emitted += 1;
                let (sel1, idx1) = selects[i];
                let (sel2, idx2) = selects[j];

                let Some(idx1_bits) = bv_solver.get_term_bits(idx1) else {
                    continue;
                };
                let Some(idx2_bits) = bv_solver.get_term_bits(idx2) else {
                    continue;
                };
                if idx1_bits.len() != idx2_bits.len() || idx1_bits.is_empty() {
                    continue;
                }

                // Skip pairs with provably-distinct indices.
                // Check 1: all bits constant and at least one differs.
                if bv_solver.are_bits_distinct_constants(idx1_bits, idx2_bits) {
                    continue;
                }
                // Check 2: any single bit position known-different makes
                // "some_diff" always true, so functional consistency is
                // vacuously satisfied for partially-constant pairs too.
                let has_known_different_bit =
                    idx1_bits.iter().zip(idx2_bits.iter()).any(|(&b1, &b2)| {
                        matches!(
                            (bv_solver.bit_constant_value(b1), bv_solver.bit_constant_value(b2)),
                            (Some(c1), Some(c2)) if c1 != c2
                        )
                    });
                if has_known_different_bit {
                    continue;
                }
                // Check 3: structural distinctness at the normalized key level
                // (e.g., base+0 vs base+1 in byte-load patterns).
                // Uses pre-computed cache to avoid O(N^2 × depth) overhead.
                if norm_key_cache
                    .get(&idx1)
                    .zip(norm_key_cache.get(&idx2))
                    .is_some_and(|(nk1, nk2)| NormalizedBvIndexKey::are_provably_distinct(nk1, nk2))
                {
                    continue;
                }
                // Note: indices with disjoint symbolic variables CAN still
                // be equal at runtime. FC axioms between such pairs are
                // necessary for soundness (#7974 regression check).

                // NOTE: do not fetch/short-circuit on the select VALUE bits here.
                // ARRAY-VALUED selects (nested arrays, e.g. `[[T;N];M]`) have no
                // value bits, but the functional-consistency axiom still applies
                // and is handled by the array-valued branch below. Bailing here
                // (the historical behaviour) silently dropped nested-array
                // congruence — the root cause of the nested-array incompleteness
                // (the development design notes). `eq_idx` below depends
                // only on the INDEX bits, which exist for both cases.

                // Create diff variables only for bit positions that are NOT
                // known-equal constants. Known-equal bits always have XOR = 0,
                // so their diff variables are trivially false and don't
                // contribute to the "some_diff" disjunction.
                let mut diff_vars = Vec::with_capacity(idx1_bits.len());
                for (&b1, &b2) in idx1_bits.iter().zip(idx2_bits.iter()) {
                    // Skip bit positions where both are the same known constant.
                    let v1 = bv_solver.bit_constant_value(b1);
                    let v2 = bv_solver.bit_constant_value(b2);
                    if let (Some(c1), Some(c2)) = (v1, v2) {
                        if c1 == c2 {
                            continue; // Known-equal: XOR is always 0
                        }
                    }

                    let ob1 = offset_bit(b1);
                    let ob2 = offset_bit(b2);
                    let diff_var = next_var as i32;
                    next_var += 1;
                    diff_vars.push(diff_var);

                    result
                        .clauses
                        .push(ay_core::CnfClause::new(vec![-diff_var, ob1, ob2]));
                    result
                        .clauses
                        .push(ay_core::CnfClause::new(vec![-diff_var, -ob1, -ob2]));
                    result
                        .clauses
                        .push(ay_core::CnfClause::new(vec![-ob1, ob2, diff_var]));
                    result
                        .clauses
                        .push(ay_core::CnfClause::new(vec![ob1, -ob2, diff_var]));
                }

                // If no diff variables were created (all bits known-equal),
                // functional consistency is trivially required. But this case
                // should not happen because idx1 != idx2 syntactically.
                if diff_vars.is_empty() {
                    continue;
                }

                // Use eq_idx summary variable to encode FC compactly.
                // Instead of wide clauses (diff_0 ∨ ... ∨ diff_N ∨ -s1_k ∨ s2_k)
                // with N+2 literals each, we introduce eq_idx such that:
                //   eq_idx ↔ (idx1 == idx2)  i.e.  eq_idx ↔ ¬(diff_0 ∨ ... ∨ diff_N)
                // Then FC becomes: eq_idx → (sel1_k == sel2_k)
                // This produces 2-literal and 3-literal clauses instead of
                // (N+2)-literal clauses, reducing clause count and improving
                // unit propagation in the SAT solver.
                // Same pattern as ROW2 encoding above (lines ~477-505).
                let eq_idx = next_var as i32;
                next_var += 1;

                // eq_idx → ¬diff_k  (2-literal clauses)
                for &diff_var in &diff_vars {
                    result
                        .clauses
                        .push(ay_core::CnfClause::new(vec![-eq_idx, -diff_var]));
                }
                // (diff_0 ∨ ... ∨ diff_N ∨ eq_idx)  (definition clause)
                let mut eq_def_clause = diff_vars.clone();
                eq_def_clause.push(eq_idx);
                result.clauses.push(ay_core::CnfClause::new(eq_def_clause));

                // FC consequent: eq_idx → (select(a, i) == select(a, j)).
                // scalar_elem_lits covers BitVec elements (term bits) AND Bool
                // elements (single atom literal). Previously Bool selects had
                // no term bits and fell into the array-valued arm, whose
                // nested-read propagation emits NOTHING for scalar Bool reads
                // — the FC consequent was silently dropped and the SAT core
                // could assign equal-index selects opposite values (wrong
                // `sat` on UNSAT Bool-element-array instances).
                match (scalar_elem_lits(sel1), scalar_elem_lits(sel2)) {
                    (Some(sel1_lits), Some(sel2_lits)) if sel1_lits.len() == sel2_lits.len() => {
                        // SCALAR element sort: literal-wise equality of values.
                        // = (¬eq_idx ∨ ¬sel1_k ∨ sel2_k) ∧ (¬eq_idx ∨ sel1_k ∨ ¬sel2_k)
                        for (&ob1, &ob2) in sel1_lits.iter().zip(sel2_lits.iter()) {
                            result
                                .clauses
                                .push(ay_core::CnfClause::new(vec![-eq_idx, -ob1, ob2]));
                            result
                                .clauses
                                .push(ay_core::CnfClause::new(vec![-eq_idx, ob1, -ob2]));
                        }
                    }
                    _ => {
                        // ARRAY-VALUED element sort (nested arrays): select(a, i)
                        // and select(a, j) are themselves arrays with no value
                        // bits. `eq_idx ⟹ select(a,i) = select(a,j)` (congruence
                        // on `select(a, ·)`), so propagate that array equality to
                        // their reads: for reads r1 = select(select(a,i), k1) and
                        // r2 = select(select(a,j), k2) with k1 = k2,
                        // `eq_idx ⟹ r1 = r2`. This is the missing nested-array
                        // congruence; sound because it only instantiates the array
                        // congruence axiom (it can add only valid facts).
                        Self::emit_nested_select_congruence_to_reads(
                            sel1,
                            sel2,
                            eq_idx,
                            &selects_by_array,
                            bv_solver,
                            &mut next_var,
                            &mut result,
                            bv_offset,
                        );
                    }
                }
            }
        }

        section_trace!("after-fc");
        if ptrace && fc_global_pairs_skipped > 0 {
            eprintln!(
                "c phase-trace array-axioms.fc-global-truncated emitted={fc_global_pairs_emitted} skipped={fc_global_pairs_skipped}"
            );
        }
        result.num_vars = next_var.saturating_sub(var_offset + 1);
        result
    }

    /// Propagate functional-consistency congruence for ARRAY-VALUED selects
    /// down to their reads (nested-array completeness).
    ///
    /// Given two selects `sel1 = select(a, i)` and `sel2 = select(a, j)` on a
    /// common base array whose RESULT sort is itself an array, and a SAT literal
    /// `eq_idx ↔ (i == j)`, congruence gives `eq_idx ⟹ sel1 = sel2` (equal
    /// arrays). Since `sel1`/`sel2` have no value bits, we express that array
    /// equality through their reads: for every collected read
    /// `r1 = select(sel1, k1)` and `r2 = select(sel2, k2)` whose read indices are
    /// equal (`k1 == k2` syntactically, or via a fresh `eq_k` summary var),
    /// emit `eq_idx ∧ eq_k ⟹ (r1 == r2)`, encoded bitwise on the (scalar) reads.
    ///
    /// Soundness: every clause is an instance of the array congruence axiom
    /// `x = y ⟹ select(x, k) = select(y, k)` conjoined with index equalities the
    /// antecedent literals encode — only valid facts are added, so this can never
    /// cause false-UNSAT. Reads that are themselves array-valued (3+ levels of
    /// nesting) are skipped here; their own FC pairs apply this rule recursively,
    /// and skipping is sound (it only forgoes a valid lemma, never asserts one).
    #[allow(clippy::too_many_arguments)]
    fn emit_nested_select_congruence_to_reads(
        sel1: TermId,
        sel2: TermId,
        eq_idx: i32,
        selects_by_array: &HashMap<TermId, Vec<(TermId, TermId)>>,
        bv_solver: &BvSolver<'_>,
        next_var: &mut u32,
        result: &mut ArrayAxiomResult,
        bv_offset: u32,
    ) {
        let offset_bit = |bit: i32| -> i32 {
            if bit > 0 {
                bit + bv_offset as i32
            } else {
                bit - bv_offset as i32
            }
        };

        let (Some(reads_a), Some(reads_b)) =
            (selects_by_array.get(&sel1), selects_by_array.get(&sel2))
        else {
            return;
        };

        for &(r1, k1) in reads_a {
            // Only scalar reads can be bit-equated here (deeper nesting handled
            // recursively by those reads' own FC pairs).
            let Some(r1_bits) = bv_solver.get_term_bits(r1) else {
                continue;
            };
            if r1_bits.is_empty() {
                continue;
            }
            for &(r2, k2) in reads_b {
                let Some(r2_bits) = bv_solver.get_term_bits(r2) else {
                    continue;
                };
                if r1_bits.len() != r2_bits.len() || r2_bits.is_empty() {
                    continue;
                }

                // Antecedent literals: ¬eq_idx (the array-valued selects are
                // equal) and, when read indices are not syntactically identical,
                // ¬eq_k where eq_k ↔ (k1 == k2).
                let mut antecedent = vec![-eq_idx];
                if k1 != k2 {
                    let (Some(k1_bits), Some(k2_bits)) =
                        (bv_solver.get_term_bits(k1), bv_solver.get_term_bits(k2))
                    else {
                        continue;
                    };
                    if k1_bits.len() != k2_bits.len() || k1_bits.is_empty() {
                        continue;
                    }
                    // Provably-distinct read indices ⟹ congruence says nothing.
                    if bv_solver.are_bits_distinct_constants(k1_bits, k2_bits) {
                        continue;
                    }
                    let mut diff_vars = Vec::with_capacity(k1_bits.len());
                    for (&b1, &b2) in k1_bits.iter().zip(k2_bits.iter()) {
                        if let (Some(c1), Some(c2)) = (
                            bv_solver.bit_constant_value(b1),
                            bv_solver.bit_constant_value(b2),
                        ) {
                            if c1 == c2 {
                                continue; // known-equal bit: XOR always 0
                            }
                        }
                        let ob1 = offset_bit(b1);
                        let ob2 = offset_bit(b2);
                        let diff_var = *next_var as i32;
                        *next_var += 1;
                        diff_vars.push(diff_var);
                        result
                            .clauses
                            .push(ay_core::CnfClause::new(vec![-diff_var, ob1, ob2]));
                        result
                            .clauses
                            .push(ay_core::CnfClause::new(vec![-diff_var, -ob1, -ob2]));
                        result
                            .clauses
                            .push(ay_core::CnfClause::new(vec![-ob1, ob2, diff_var]));
                        result
                            .clauses
                            .push(ay_core::CnfClause::new(vec![ob1, -ob2, diff_var]));
                    }
                    // If all bits are known-equal (diff_vars empty), k1 == k2 in
                    // every model, so the condition is just eq_idx. Otherwise add
                    // eq_k ↔ ¬(diff_0 ∨ … ∨ diff_N) and require it.
                    if !diff_vars.is_empty() {
                        let eq_k = *next_var as i32;
                        *next_var += 1;
                        for &dv in &diff_vars {
                            result
                                .clauses
                                .push(ay_core::CnfClause::new(vec![-eq_k, -dv]));
                        }
                        let mut eq_def = diff_vars;
                        eq_def.push(eq_k);
                        result.clauses.push(ay_core::CnfClause::new(eq_def));
                        antecedent.push(-eq_k);
                    }
                }

                // antecedent ⟹ (r1 == r2), bitwise.
                for (&a_bit, &b_bit) in r1_bits.iter().zip(r2_bits.iter()) {
                    let oa = offset_bit(a_bit);
                    let ob = offset_bit(b_bit);
                    let mut c1 = antecedent.clone();
                    c1.push(-oa);
                    c1.push(ob);
                    result.clauses.push(ay_core::CnfClause::new(c1));
                    let mut c2 = antecedent.clone();
                    c2.push(oa);
                    c2.push(-ob);
                    result.clauses.push(ay_core::CnfClause::new(c2));
                }
            }
        }
    }

    /// Flatten BV1 bvand assertions: `(= #b1 (bvand t1 t2))` becomes
    /// separate assertions `(= #b1 t1)` and `(= #b1 t2)`.
    ///
    /// The try3/try5 QF_ABV benchmarks encode their entire formula as a single
    /// assertion: `(= (_ bv1 1) (bvand (bvand ...) ...))`.
    /// Flattening the bvand tree exposes individual ITE-wrapped constraints
    /// as separate assertions, enabling store-flat substitution and better
    /// SAT solver propagation.
    pub(in crate::executor) fn flatten_bv1_bvand_assertions(&mut self) {
        let mut source_sets = vec![Vec::new(); self.ctx.assertions.len()];
        self.flatten_bv1_bvand_assertions_with_sources(&mut source_sets);
    }

    pub(in crate::executor) fn flatten_bv1_bvand_assertions_with_sources(
        &mut self,
        source_sets: &mut Vec<Vec<TermId>>,
    ) {
        debug_assert_eq!(self.ctx.assertions.len(), source_sets.len());
        let mut new_assertions = Vec::new();
        let mut new_source_sets = Vec::new();
        let mut modified = false;

        for (&assertion, source_set) in self.ctx.assertions.iter().zip(source_sets.iter()) {
            // Match: (= #b1 (bvand ...)) at BV1 width
            if let TermData::App(ref sym, ref args) = self.ctx.terms.get(assertion).clone() {
                if sym.name() == "=" && args.len() == 2 {
                    let (lhs, rhs) = (args[0], args[1]);
                    // Check if one side is #b1 and the other is bvand at BV1
                    let bvand_term = if Self::is_bv1_one_const(&self.ctx.terms, lhs) {
                        Some(rhs)
                    } else if Self::is_bv1_one_const(&self.ctx.terms, rhs) {
                        Some(lhs)
                    } else {
                        None
                    };

                    if let Some(bvand) = bvand_term {
                        let mut leaves = Vec::new();
                        Self::collect_bv1_bvand_leaves_static(&self.ctx.terms, bvand, &mut leaves);
                        if leaves.len() > 1 {
                            modified = true;
                            let bv1_one = self.ctx.terms.mk_bitvec(BigInt::from(1u8), 1);
                            for leaf in leaves {
                                let eq = self.ctx.terms.mk_eq(bv1_one, leaf);
                                new_assertions.push(eq);
                                new_source_sets.push(source_set.clone());
                            }
                            continue;
                        }
                    }
                }
            }
            new_assertions.push(assertion);
            new_source_sets.push(source_set.clone());
        }

        if modified {
            self.ctx.assertions = new_assertions;
            *source_sets = new_source_sets;
        }
        debug_assert_eq!(self.ctx.assertions.len(), source_sets.len());
    }

    /// Check if a term is the BV1 constant #b1 (value 1, width 1).
    fn is_bv1_one_const(terms: &ay_core::TermStore, term: TermId) -> bool {
        matches!(
            terms.get(term),
            TermData::Const(Constant::BitVec { value, width })
                if *width == 1 && *value == BigInt::from(1u8)
        )
    }

    /// Recursively collect leaves of a BV1 bvand tree.
    fn collect_bv1_bvand_leaves_static(
        terms: &ay_core::TermStore,
        term: TermId,
        leaves: &mut Vec<TermId>,
    ) {
        if let TermData::App(ref sym, ref args) = terms.get(term) {
            if sym.name() == "bvand" && args.len() == 2 {
                if let Sort::BitVec(bv) = terms.sort(term) {
                    if bv.width == 1 {
                        let a = args[0];
                        let b = args[1];
                        Self::collect_bv1_bvand_leaves_static(terms, a, leaves);
                        Self::collect_bv1_bvand_leaves_static(terms, b, leaves);
                        return;
                    }
                }
            }
        }
        leaves.push(term);
    }

    /// Count the total number of select terms reachable from assertions.
    /// Used by the adaptive fixpoint gate to skip expensive axiom fixpoints
    /// on formulas with many array selects.
    #[allow(dead_code)]
    pub(in crate::executor) fn count_array_selects_in_assertions(&self) -> usize {
        let mut selects = Vec::new();
        let mut stores = Vec::new();
        let mut visited = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_array_terms(assertion, &mut selects, &mut stores, &mut visited);
        }
        selects.len()
    }

    /// Count the total number of store terms reachable from assertions.
    /// Used by the adaptive ITE budget gate in expand_select_store (#8140):
    /// formulas with moderate store counts (< 500) use a higher symbolic ITE
    /// budget to resolve more store chains at the term level, reducing the
    /// clause count sent to the SAT solver.
    pub(in crate::executor) fn count_array_stores_in_assertions(&self) -> usize {
        let mut selects = Vec::new();
        let mut stores = Vec::new();
        let mut visited = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_array_terms(assertion, &mut selects, &mut stores, &mut visited);
        }
        stores.len()
    }

    /// Count the number of "complex" array selects in assertions (#8510).
    ///
    /// A select is complex if its array operand involves a store chain
    /// (directly or transitively) or if it reads from an array that also
    /// has stores. Selects with concrete indices on plain declared array
    /// variables (no stores) are trivial and don't need the fixpoint.
    ///
    /// This is used by the fixpoint gate to avoid skipping the fixpoint
    /// on benchmarks with many trivial constant-indexed selects (e.g.,
    /// csplit-query QF_ABV benchmarks have 2000+ trivial selects from
    /// constant arrays but only ~10 complex ones involving store chains).
    pub(in crate::executor) fn count_complex_array_selects_in_assertions(&self) -> usize {
        let mut selects = Vec::new();
        let mut stores = Vec::new();
        let mut visited = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_array_terms(assertion, &mut selects, &mut stores, &mut visited);
        }

        // Build set of array TermIds that have stores on them (the base array
        // of any store, or the store term itself since select(store(...), i)
        // has the store as its array operand).
        let mut store_arrays: HashSet<TermId> = HashSet::default();
        for &(store_term, base_array, _, _) in &stores {
            store_arrays.insert(store_term);
            store_arrays.insert(base_array);
            // Walk up the store chain to mark all intermediate arrays
            let mut current = base_array;
            loop {
                match self.ctx.terms.get(current) {
                    TermData::App(Symbol::Named(name), args)
                        if name.as_str() == "store" && args.len() == 3 =>
                    {
                        store_arrays.insert(args[0]);
                        current = args[0];
                    }
                    _ => break,
                }
            }
        }

        // A select is complex if its array operand is a store or reads from
        // an array that has stores.
        selects
            .iter()
            .filter(|&&(_sel, array, _idx)| store_arrays.contains(&array))
            .count()
    }

    /// Recursively collect select and store terms from an expression
    pub(in crate::executor) fn collect_array_terms(
        &self,
        term: TermId,
        selects: &mut Vec<(TermId, TermId, TermId)>,
        stores: &mut Vec<(TermId, TermId, TermId, TermId)>,
        visited: &mut HashSet<TermId>,
    ) {
        if visited.contains(&term) {
            return;
        }
        visited.insert(term);

        match self.ctx.terms.get(term) {
            TermData::App(sym, args) => {
                match sym.name() {
                    "select" if args.len() == 2 => {
                        selects.push((term, args[0], args[1]));
                        // Recurse into array and index
                        self.collect_array_terms(args[0], selects, stores, visited);
                        self.collect_array_terms(args[1], selects, stores, visited);
                    }
                    "store" if args.len() == 3 => {
                        stores.push((term, args[0], args[1], args[2]));
                        // Recurse into array, index, and value
                        self.collect_array_terms(args[0], selects, stores, visited);
                        self.collect_array_terms(args[1], selects, stores, visited);
                        self.collect_array_terms(args[2], selects, stores, visited);
                    }
                    _ => {
                        // Recurse into other function applications, including
                        // indexed BV operators such as extract/zero_extend.
                        for &arg in args {
                            self.collect_array_terms(arg, selects, stores, visited);
                        }
                    }
                }
            }
            TermData::Not(inner) => {
                self.collect_array_terms(*inner, selects, stores, visited);
            }
            TermData::Ite(c, t, e) => {
                self.collect_array_terms(*c, selects, stores, visited);
                self.collect_array_terms(*t, selects, stores, visited);
                self.collect_array_terms(*e, selects, stores, visited);
            }
            _ => {}
        }
    }
}
