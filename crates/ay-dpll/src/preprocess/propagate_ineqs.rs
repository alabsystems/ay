// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PropagateIneqs goal pass (z3's `propagate-ineqs` tactic).
//!
//! A bound-subsumption pass over the goal's top-level formulas — deliberately
//! NOT value propagation (z3's `propagate-ineqs` does not substitute values;
//! aliasing it to `PropagateValues` was factually wrong and was split out):
//!
//! - An inequality atom `(op x c)` / `(op c x)` for `op ∈ {<, <=}` with `x` a
//!   declared variable and `c` an Int/Real constant is a *bound* on `x`
//!   (AY's constructors already normalize `>`/`>=` into `<`/`<=` with the
//!   sides swapped, so these two shapes are exhaustive).
//! - A bound is DROPPED iff it is implied by a retained entry on the same
//!   variable and direction that is (a) a bound of the SAME strictness with an
//!   equal-or-stronger constant (ties keep the earliest — exact duplicates
//!   dedup), or (b) a value equality `(= x v)` whose `v` satisfies it —
//!   NON-STRICT bounds only: the equality is absorbed as the non-strict bound
//!   pair `x >= v ∧ x <= v`, and strict/non-strict never subsume each other
//!   (measured against z3 4.15.4, which keeps `(> x 3)` alongside `(= x 5)`
//!   and keeps both `(< x 5)` and `(<= x 5)`).
//! - Value equalities `(= x c)` are retained and re-emitted at the END of the
//!   goal (matching z3's output order); exact duplicates dedup to the earliest
//!   copy (measured z3 behavior).
//! - Everything else (var–var equalities, monomials like `(<= (* 2 x) 10)`,
//!   Bool formulas) is retained VERBATIM in place — fail-conservative.
//! - Contradictory bounds are both kept — no `false` collapse (matching z3).
//!
//! # Soundness
//!
//! EQUIVALENCE-PRESERVING (stronger than equisatisfiable): the pass only DROPS
//! a conjunct that is logically implied by a retained conjunct, and only
//! REORDERS the rest — both preserve the conjunction's model set exactly.
//!
//! # Scope
//!
//! Apply-surface only: this pass is registered for the tactic path and is
//! deliberately NOT part of the solve preprocessing pipeline (it does not
//! implement [`super::PreprocessingPass`], so it cannot auto-enroll), keeping
//! plain `check-sat` behavior byte-for-byte unchanged.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, TermData};
use ay_core::{TermId, TermStore};
use num_rational::BigRational;

/// How a goal formula participates in bound subsumption.
enum Classified {
    /// `(op x c)` / `(op c x)` for `op ∈ {<, <=}`: a bound on `var`.
    /// `upper` is true for `x < c` / `x <= c`, false for `c < x` / `c <= x`.
    Bound {
        var: TermId,
        upper: bool,
        strict: bool,
        value: BigRational,
    },
    /// `(= x c)` / `(= c x)` with `x` a variable and `c` an Int/Real constant.
    ValueEq { var: TermId, value: BigRational },
    /// Anything else — retained verbatim, in place.
    Passthrough,
}

/// The numeric value of an Int/Real constant term (compared via rationals so
/// Int and Real bounds on the same variable are commensurable — a variable's
/// sort is fixed, so cross-sort comparison never actually arises).
fn numeric_const(terms: &TermStore, t: TermId) -> Option<BigRational> {
    match terms.get(t) {
        TermData::Const(Constant::Int(i)) => Some(BigRational::from_integer(i.clone())),
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        _ => None,
    }
}

/// Whether `t` is a declared variable (`TermData::Var`).
fn is_var(terms: &TermStore, t: TermId) -> bool {
    matches!(terms.get(t), TermData::Var(_, _))
}

/// Classify one goal formula. Unrecognized shapes are `Passthrough` —
/// fail-conservative, never rewritten or dropped.
fn classify(terms: &TermStore, f: TermId) -> Classified {
    if let TermData::App(sym, args) = terms.get(f) {
        if args.len() == 2 {
            let (a, b) = (args[0], args[1]);
            match sym.name() {
                op @ ("<" | "<=") => {
                    let strict = op == "<";
                    if is_var(terms, a) {
                        if let Some(value) = numeric_const(terms, b) {
                            // (op x c): upper bound on x.
                            return Classified::Bound {
                                var: a,
                                upper: true,
                                strict,
                                value,
                            };
                        }
                    }
                    if is_var(terms, b) {
                        if let Some(value) = numeric_const(terms, a) {
                            // (op c x): lower bound on x.
                            return Classified::Bound {
                                var: b,
                                upper: false,
                                strict,
                                value,
                            };
                        }
                    }
                }
                "=" => {
                    if is_var(terms, a) {
                        if let Some(value) = numeric_const(terms, b) {
                            return Classified::ValueEq { var: a, value };
                        }
                    }
                    if is_var(terms, b) {
                        if let Some(value) = numeric_const(terms, a) {
                            return Classified::ValueEq { var: b, value };
                        }
                    }
                }
                _ => {}
            }
        }
    }
    Classified::Passthrough
}

/// Bound subsumption over the goal's top-level inequalities (see module docs).
pub(crate) struct PropagateIneqs;

impl PropagateIneqs {
    pub(crate) fn new() -> Self {
        PropagateIneqs
    }

    /// Apply the pass to the goal formulas; returns whether the goal changed.
    ///
    /// GROUP-WISE, not a sequential retained-so-far filter: the strongest
    /// bound per `(var, direction, strictness)` is computed over the WHOLE
    /// goal first, so `(<= x 10)` followed by `(<= x 5)` keeps the later,
    /// stronger `(<= x 5)` (a sequential filter would wrongly keep the weaker
    /// earlier bound).
    pub(crate) fn apply_goal(&mut self, terms: &mut TermStore, fs: &mut Vec<TermId>) -> bool {
        // Phase 1: classify every formula.
        let classified: Vec<Classified> = fs.iter().map(|&f| classify(terms, f)).collect();

        // Phase 2: strongest bound per (var, upper?, strict?) — upper bounds
        // want the MINIMUM constant, lower bounds the MAXIMUM; ties keep the
        // EARLIEST index (so exact duplicates dedup to the first copy) — plus
        // every value equality per var (all value equalities are retained).
        let mut best: HashMap<(TermId, bool, bool), (usize, BigRational)> = HashMap::default();
        let mut value_eqs: HashMap<TermId, Vec<BigRational>> = HashMap::default();
        for (i, c) in classified.iter().enumerate() {
            match c {
                Classified::Bound {
                    var,
                    upper,
                    strict,
                    value,
                } => {
                    let key = (*var, *upper, *strict);
                    let stronger = match best.get(&key) {
                        None => true,
                        Some((_, cur)) => {
                            if *upper {
                                value < cur
                            } else {
                                value > cur
                            }
                        }
                    };
                    if stronger {
                        best.insert(key, (i, value.clone()));
                    }
                }
                Classified::ValueEq { var, value } => {
                    value_eqs.entry(*var).or_default().push(value.clone());
                }
                Classified::Passthrough => {}
            }
        }

        // Phase 3: emit. Retained non-ValueEq formulas keep input order (a
        // passthrough keeps its slot); retained ValueEqs (the ORIGINAL
        // TermIds, never rewritten) are appended at the end in input order.
        let mut out: Vec<TermId> = Vec::with_capacity(fs.len());
        let mut eq_tail: Vec<TermId> = Vec::new();
        for (i, c) in classified.iter().enumerate() {
            match c {
                Classified::Passthrough => out.push(fs[i]),
                // Exact-duplicate value equalities dedup to the earliest copy
                // (hash-consing makes duplicates TermId-equal; measured z3
                // prints `(= x 5)(= x 5)` as one `(= x 5)`). Dropping an exact
                // duplicate conjunct is trivially equivalence-preserving.
                Classified::ValueEq { .. } => {
                    if !eq_tail.contains(&fs[i]) {
                        eq_tail.push(fs[i]);
                    }
                }
                Classified::Bound {
                    var,
                    upper,
                    strict,
                    value,
                } => {
                    // Dropped unless it IS the retained strongest bound of its
                    // group (equal-or-stronger same-strictness subsumption;
                    // the earliest strongest copy is the retained one).
                    let key = (*var, *upper, *strict);
                    let is_best = matches!(best.get(&key), Some((bi, _)) if *bi == i);
                    if !is_best {
                        continue;
                    }
                    // Dropped if implied by a retained value equality on the
                    // same var. NON-STRICT bounds only: `(= x v)` is absorbed
                    // as the non-strict pair `x >= v ∧ x <= v`, and strict and
                    // non-strict never subsume each other (measured z3
                    // behavior: `(> x 3)` is KEPT alongside `(= x 5)`). A
                    // contradictory value equality never subsumes — the bound
                    // is kept; no `false` collapse, matching z3.
                    if !*strict {
                        if let Some(vals) = value_eqs.get(var) {
                            let implied = vals.iter().any(|v| {
                                if *upper {
                                    v <= value // (<= x c): v <= c
                                } else {
                                    v >= value // (<= c x): v >= c
                                }
                            });
                            if implied {
                                continue;
                            }
                        }
                    }
                    out.push(fs[i]);
                }
            }
        }
        out.extend(eq_tail);

        let changed = out != *fs;
        *fs = out;
        changed
    }
}

impl Default for PropagateIneqs {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests;
