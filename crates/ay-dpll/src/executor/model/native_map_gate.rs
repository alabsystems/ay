// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native finite-map fail-closed SAT gate (#map-value-semantics).
//!
//! A `(Map K V)` is a pair: a value array `Array(K -> V)` — the map term
//! itself, since the frontend erases the sort — and a domain `Array(K ->
//! Bool)`. `map.insert` stores into both, `map.remove` into the domain only,
//! `map.get` reads the values, `map.contains_key` the domain, the empty map is
//! the sort's one unconstrained value array with the all-false domain, and two
//! maps are equal when both parts are (`ay-frontend`, `elaborate/app/map.rs`,
//! "Semantics"). The frontend derives a domain structurally through the empty
//! map and the constructors, and for any other map term mints a domain
//! carrier; carriers are chained so that maps with equal value arrays share
//! one. Map-sorted `=` compares the value arrays; the chain supplies the rest.
//!
//! A model of that encoding is a model of the source — pair each map's value
//! array with its domain — while all of these hold:
//!
//! - the empty map, `map.insert` and `map.remove` appear only under readers
//!   (a `select` of the empty map is a `map.get`). As a value (in `=`, an
//!   `ite` branch, a function argument, ...) only the value array is tied and
//!   the domain they carry is lost.
//! - every carried domain belongs to a declared map constant. The carrier of a
//!   bound variable, an `ite`, a `select` or a function result is one free
//!   array, not a function of the map it stands for.
//! - no quantifier over a map-holding sort compares maps (`=`, `distinct`).
//!   The encoding has one map per value array, so a universal claim such as
//!   "maps with equal values are equal" holds there and fails for the pairs.
//!   No measured `sat` comes from this; it is defence in depth.
//! - `map.subset` compares a map with itself. Anything else is decided only
//!   over keys both operands read, and the independent model gate adopts its
//!   value unchecked.
//! - no constant array is written at a map sort (`((as const (Map K V)) v)`):
//!   it is not the empty map, and nothing gives it a domain.
//!
//! Outside that fragment this gate withholds `sat`: degrade-only (`Sat ->
//! Unknown`, never an UNSAT flip), and a problem that elaborated no native map
//! operator, builtin or user-declared (`Context::uses_map`), is never walked.
//! The authored assertions are walked as well as the live stack and the
//! assumptions, so a preprocessing rewrite cannot hide a shape. Measured on
//! `7b6e639c98`, each of these is `unsat` and answered `sat`:
//!
//! ```text
//! (= n (as map.empty (Map Int Int))) (map.contains_key n 3)       empty map as a value
//! (= (map.insert m 1 5) (as map.empty (Map Int Int)))             constructor as a value
//! (= m n) (not (map.subset m n))                                  subset beyond reflexivity
//! (forall ((x (Map Int Int))) (map.contains_key x 1))             carrier of a bound map
//! (= i j) (map.contains_key (select (store A i (as map.empty ..)) j) 1)
//! ```
//!
//! The encoding is also STRONGER than the semantics in one place, which no
//! `sat` gate can repair: the chain gives maps with equal value arrays one
//! domain, so over a finite key sort, where two maps' values can agree at
//! every key, maps that differ only in their domains cannot exist, and a
//! problem that needs them answers `unsat` (`LIMITATIONS.md`).

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{TermData, TermId};

use crate::executor::Executor;
use crate::executor_types::SolveResult;

/// Why a native-map `sat` cannot be published.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum NativeMapGap {
    /// A domain carrier was minted for a map term other than a declared
    /// constant (bound variable, `ite`, `select`, UF result, ...).
    UnfaithfulDomainCarrier,
    /// An empty map used as a value rather than read.
    EmptyMapAsValue,
    /// A `map.insert` / `map.remove` application used as a value.
    ConstructorAsValue,
    /// A `map.subset` atom over two different operands.
    SubsetBeyondReflexivity,
    /// A map comparison under a quantifier that binds a map-holding sort.
    QuantifiedMapComparison,
    /// A constant array, `((as const (Map K V)) v)`, at a map sort.
    ConstantArrayMap,
}

impl NativeMapGap {
    fn label(self) -> &'static str {
        match self {
            Self::UnfaithfulDomainCarrier => "unfaithful-domain-carrier",
            Self::EmptyMapAsValue => "empty-map-as-value",
            Self::ConstructorAsValue => "constructor-as-value",
            Self::SubsetBeyondReflexivity => "subset-beyond-reflexivity",
            Self::QuantifiedMapComparison => "quantified-map-comparison",
            Self::ConstantArrayMap => "constant-array-map",
        }
    }

    fn detail(self) -> &'static str {
        match self {
            Self::UnfaithfulDomainCarrier => {
                "a map domain was carried for a map term that is not a declared map constant; \
                 that carrier need not match the map's real domain, so this `sat` may ignore it"
            }
            Self::EmptyMapAsValue => {
                "the empty map is used as a value; AY ties only its value array there, so this \
                 `sat` may ignore the map's domain"
            }
            Self::ConstructorAsValue => {
                "a map built by map.insert/map.remove is used as a value; AY ties only its value \
                 array there, so this `sat` may ignore the map's domain"
            }
            Self::SubsetBeyondReflexivity => {
                "map.subset is decided only by reflexivity and over keys both operands already \
                 read, and the independent model gate does not interpret it"
            }
            Self::QuantifiedMapComparison => {
                "a quantifier over maps compares maps; AY quantifies over value arrays only, \
                 which are fewer than the maps, so this `sat` may not hold for every map"
            }
            Self::ConstantArrayMap => {
                "a constant array is used at a map sort; AY gives it no domain of its own, so \
                 this `sat` may ignore the map's domain"
            }
        }
    }
}

impl Executor {
    /// Why this problem's native-map `sat` is unpublishable, or `None` — always
    /// `None` for a problem that elaborated no native map operator.
    pub(in crate::executor) fn native_map_gap(&self) -> Option<NativeMapGap> {
        if !self.ctx.uses_map() {
            return None;
        }
        if self.ctx.map_domain_unfaithful() {
            return Some(NativeMapGap::UnfaithfulDomainCarrier);
        }
        if self.ctx.map_constant_array() {
            return Some(NativeMapGap::ConstantArrayMap);
        }
        let mut roots = self.ctx.concrete_authored_assertion_terms();
        roots.extend(self.ctx.assertions.iter().copied());
        if let Some(assumptions) = &self.last_assumptions {
            roots.extend(assumptions.iter().copied());
        }
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots;
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if self.ctx.is_native_empty_map(term) {
                return Some(NativeMapGap::EmptyMapAsValue);
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => match (sym.name(), args.as_slice()) {
                    ("map.insert", [_, _, _]) | ("map.remove", [_, _]) => {
                        return Some(NativeMapGap::ConstructorAsValue);
                    }
                    // `(map.subset t t)` holds whatever `t` is, and the native
                    // solver decides exactly that.
                    ("map.subset", [sub, sup]) if sub != sup => {
                        return Some(NativeMapGap::SubsetBeyondReflexivity);
                    }
                    // `map.get` of the empty map: a read, not a use as a value.
                    ("select", [array, index]) if self.ctx.is_native_empty_map(*array) => {
                        stack.push(*index);
                        continue;
                    }
                    _ => {}
                },
                TermData::Forall(bound, body, _) | TermData::Exists(bound, body, _)
                    if bound
                        .iter()
                        .any(|(_, sort)| self.ctx.sort_may_hold_map(sort))
                        && self.compares_maps(*body) =>
                {
                    return Some(NativeMapGap::QuantifiedMapComparison);
                }
                _ => {}
            }
            stack.extend(self.ctx.terms.children(term));
        }
        None
    }

    /// Whether `root` contains an `=` or `distinct` over a map-holding sort.
    fn compares_maps(&self, root: TermId) -> bool {
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(term) {
                if matches!(sym.name(), "=" | "distinct")
                    && args
                        .first()
                        .is_some_and(|arg| self.ctx.sort_may_hold_map(self.ctx.terms.sort(*arg)))
                {
                    return true;
                }
            }
            stack.extend(self.ctx.terms.children(term));
        }
        false
    }

    /// Downgrade a `Sat` to `Unknown` when the problem uses a native map outside
    /// the faithfully encoded fragment (see the module docs). Every other
    /// result, and every problem without a native map operator, passes through
    /// untouched.
    pub(in crate::executor) fn apply_native_map_failclosed_gate(
        &mut self,
        result: SolveResult,
    ) -> SolveResult {
        if result != SolveResult::Sat {
            return result;
        }
        let Some(gap) = self.native_map_gap() else {
            return result;
        };
        tracing::warn!(
            gap = gap.label(),
            "native-map fail-closed gate: the problem uses a native map outside the faithfully \
             encoded fragment; downgrading SAT to Unknown"
        );
        self.last_statistics
            .set_string("model_check_gate.native_map_failclosed", gap.label());
        self.downgrade_sat_after_gate(gap.detail());
        SolveResult::Unknown
    }
}
