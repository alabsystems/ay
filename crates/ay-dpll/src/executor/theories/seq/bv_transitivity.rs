// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! BV comparison transitivity axiom injection for `Seq<BitVec>` formulas (#7587, #7579).
//!
//! When the Seq solver path handles formulas containing BV comparisons
//! (e.g., `bvsle`, `bvule`), the EUF+Seq theory combination treats these
//! predicates as uninterpreted. This loses ordering semantics, specifically
//! transitivity: `bvsle(a,b) /\ bvsle(b,c) => bvsle(a,c)`.
//!
//! This module scans for BV comparison atoms and injects explicit transitivity
//! axioms in clausal form: `(or (not (bvsle a b)) (not (bvsle b c)) (bvsle a c))`.
//!
//! Note: `bvsge(a,b)` and `bvsgt(a,b)` are normalized to `bvsle(b,a)` and
//! `bvslt(b,a)` at term construction time (see `comparison.rs`), so the scanner
//! only needs to handle the four canonical forms: bvsle, bvule, bvslt, bvult.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData, TermId};
use ay_core::Sort;

use super::super::super::Executor;

/// A BV comparison atom: `(op lhs rhs)` where op is a BV comparison.
#[derive(Debug, Clone)]
struct BvCompAtom {
    /// The full predicate term (e.g., the TermId for `bvsle(a, b)`)
    predicate: TermId,
    /// Left operand
    lhs: TermId,
    /// Right operand
    rhs: TermId,
    /// Comparison kind
    kind: BvCompKind,
}

/// BV comparison operators (canonical forms only -- GE/GT normalized at construction).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum BvCompKind {
    /// `bvsle` (signed <=) -- reflexive, transitive
    Bvsle,
    /// `bvule` (unsigned <=) -- reflexive, transitive
    Bvule,
    /// `bvslt` (signed <) -- irreflexive, transitive
    Bvslt,
    /// `bvult` (unsigned <) -- irreflexive, transitive
    Bvult,
}

impl BvCompKind {
    fn from_name(name: &str) -> Option<Self> {
        match name {
            "bvsle" => Some(Self::Bvsle),
            "bvule" => Some(Self::Bvule),
            "bvslt" => Some(Self::Bvslt),
            "bvult" => Some(Self::Bvult),
            _ => None,
        }
    }

    /// The transitivity family: LE and LT within the same signedness form
    /// transitivity chains.
    fn family(self) -> TransitivityFamily {
        match self {
            Self::Bvsle | Self::Bvslt => TransitivityFamily::Signed,
            Self::Bvule | Self::Bvult => TransitivityFamily::Unsigned,
        }
    }

    fn is_strict(self) -> bool {
        matches!(self, Self::Bvslt | Self::Bvult)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TransitivityFamily {
    Signed,
    Unsigned,
}

impl Executor {
    /// Collect BV comparison transitivity axioms from assertions (#7587).
    ///
    /// Scans for BV comparison predicates (bvsle, bvule, bvslt, bvult) and
    /// injects transitivity lemmas in clausal form:
    ///   `(or (not P_ab) (not P_bc) C_ac)`
    /// where `P_ab = op(a,b)`, `P_bc = op(b,c)`, `C_ac = op(a,c)`.
    ///
    /// When `C_ac` simplifies to `false` (e.g., `bvslt(a,a)`), the clause
    /// becomes `(or (not P_ab) (not P_bc))`, directly deriving contradiction
    /// from the anti-symmetry of `<`.
    ///
    /// Also handles alias resolution: when `a = seq.nth(s, i)` and
    /// `bvsle(a, b)` appear, the comparison is resolved through the alias (#7579).
    pub(super) fn collect_bv_transitivity_axioms(&mut self) -> Vec<TermId> {
        let mut comps = self.scan_bv_comparisons();
        if comps.is_empty() {
            return Vec::new();
        }

        // Build connected alias classes from BV equality assertions so matching
        // works through arbitrary equality chains (#7579).
        let alias_classes = self.build_bv_alias_classes();

        let mut axioms = Vec::new();
        let mut seen_atoms = HashSet::default();
        let mut seen_axioms = HashSet::default();

        for comp in &comps {
            seen_atoms.insert(self.canonical_comp_key(
                comp.kind,
                comp.lhs,
                comp.rhs,
                &alias_classes,
            ));
        }

        // Close the comparison set under transitivity. Derived conclusions are
        // fed back into the worklist so longer chains also propagate.
        //
        // #8637: Cap iterations at 10,000 and check interrupt flag to prevent
        // unbounded looping on formulas with many BV comparison chains.
        let should_stop = self.make_should_stop();
        let mut transit_iters: usize = 0;
        let mut i = 0;
        while i < comps.len() {
            transit_iters += 1;
            if transit_iters > 10_000 || should_stop() {
                break;
            }
            let ab = comps[i].clone();
            let current_len = comps.len();
            for j in 0..current_len {
                if i == j {
                    continue;
                }
                let bc = comps[j].clone();

                // Must be in the same transitivity family (signed/unsigned).
                if ab.kind.family() != bc.kind.family() {
                    continue;
                }

                // Check if ab.rhs matches bc.lhs (direct or via alias).
                if !self.bv_terms_match(ab.rhs, bc.lhs, &alias_classes) {
                    continue;
                }

                // Determine result kind: if either is strict (<), result is strict.
                let result_kind = if ab.kind.is_strict() || bc.kind.is_strict() {
                    match ab.kind.family() {
                        TransitivityFamily::Signed => BvCompKind::Bvslt,
                        TransitivityFamily::Unsigned => BvCompKind::Bvult,
                    }
                } else {
                    ab.kind // Both are LE, result is LE
                };

                // Skip if conclusion is trivially true (reflexive LE)
                if ab.lhs == bc.rhs && !result_kind.is_strict() {
                    continue;
                }

                let conclusion = self.mk_bv_comp(result_kind, ab.lhs, bc.rhs);

                // Skip tautologies like `p /\ q => p`.
                if conclusion == ab.predicate || conclusion == bc.predicate {
                    continue;
                }

                let premise_key = if ab.predicate <= bc.predicate {
                    (ab.predicate, bc.predicate, conclusion)
                } else {
                    (bc.predicate, ab.predicate, conclusion)
                };
                if !seen_axioms.insert(premise_key) {
                    continue;
                }

                // Build clausal transitivity axiom:
                //   (or (not P_ab) (not P_bc) C_ac)
                // This is the clause form of P_ab /\ P_bc => C_ac.
                //
                // When C_ac = false (e.g., bvslt(x,x) is irreflexive), we get
                //   (or (not P_ab) (not P_bc))
                // which directly derives contradiction from anti-symmetry.
                let not_ab = self.ctx.terms.mk_not(ab.predicate);
                let not_bc = self.ctx.terms.mk_not(bc.predicate);
                let axiom = self.ctx.terms.mk_or(vec![not_ab, not_bc, conclusion]);
                axioms.push(axiom);

                let key = self.canonical_comp_key(result_kind, ab.lhs, bc.rhs, &alias_classes);
                if seen_atoms.insert(key) {
                    comps.push(BvCompAtom {
                        predicate: conclusion,
                        lhs: ab.lhs,
                        rhs: bc.rhs,
                        kind: result_kind,
                    });
                }
            }
            i += 1;
        }

        axioms
    }

    /// Scan assertions for BV comparison atoms (bvsle, bvule, bvslt, bvult).
    ///
    /// GE/GT forms are already normalized to LE/LT at term construction time.
    fn scan_bv_comparisons(&self) -> Vec<BvCompAtom> {
        let mut comps = Vec::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if let Some(kind) = BvCompKind::from_name(name) {
                        if args.len() == 2 {
                            comps.push(BvCompAtom {
                                predicate: term,
                                lhs: args[0],
                                rhs: args[1],
                                kind,
                            });
                        }
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        comps
    }

    /// Build connected alias classes for BV-sorted terms (#7579).
    ///
    /// Scans equality assertions for patterns like `(= a (seq.nth s i))` or
    /// `(= a b)` where operands are BV-sorted. Uses union-find to group all
    /// terms in the same equality chain under a single representative.
    fn build_bv_alias_classes(&self) -> HashMap<TermId, TermId> {
        let mut adjacency: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for &assertion in &self.ctx.assertions {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) {
                if name == "=" && args.len() == 2 {
                    let (a, b) = (args[0], args[1]);
                    if matches!(self.ctx.terms.sort(a), Sort::BitVec(_)) {
                        adjacency.entry(a).or_default().push(b);
                        adjacency.entry(b).or_default().push(a);
                    }
                }
            }
        }

        let mut alias_classes = HashMap::default();
        let mut visited = HashSet::default();
        let mut nodes: Vec<_> = adjacency.keys().copied().collect();
        nodes.sort_unstable();

        for start in nodes {
            if !visited.insert(start) {
                continue;
            }
            let mut component = vec![start];
            let mut stack = vec![start];
            while let Some(term) = stack.pop() {
                if let Some(neighbors) = adjacency.get(&term) {
                    for &neighbor in neighbors {
                        if visited.insert(neighbor) {
                            component.push(neighbor);
                            stack.push(neighbor);
                        }
                    }
                }
            }

            let representative = *component.iter().min().expect("component is non-empty");
            for term in component {
                alias_classes.insert(term, representative);
            }
        }

        alias_classes
    }

    /// Check if two BV terms match directly or through alias chains.
    fn bv_terms_match(
        &self,
        a: TermId,
        b: TermId,
        alias_classes: &HashMap<TermId, TermId>,
    ) -> bool {
        self.canonical_bv_term(a, alias_classes) == self.canonical_bv_term(b, alias_classes)
    }

    /// Create a BV comparison term using the canonical construction methods.
    fn mk_bv_comp(&mut self, kind: BvCompKind, lhs: TermId, rhs: TermId) -> TermId {
        match kind {
            BvCompKind::Bvsle => self.ctx.terms.mk_bvsle(lhs, rhs),
            BvCompKind::Bvule => self.ctx.terms.mk_bvule(lhs, rhs),
            BvCompKind::Bvslt => self.ctx.terms.mk_bvslt(lhs, rhs),
            BvCompKind::Bvult => self.ctx.terms.mk_bvult(lhs, rhs),
        }
    }

    fn canonical_comp_key(
        &self,
        kind: BvCompKind,
        lhs: TermId,
        rhs: TermId,
        alias_classes: &HashMap<TermId, TermId>,
    ) -> (TermId, TermId, BvCompKind) {
        (
            self.canonical_bv_term(lhs, alias_classes),
            self.canonical_bv_term(rhs, alias_classes),
            kind,
        )
    }

    fn canonical_bv_term(&self, term: TermId, alias_classes: &HashMap<TermId, TermId>) -> TermId {
        alias_classes.get(&term).copied().unwrap_or(term)
    }
}
