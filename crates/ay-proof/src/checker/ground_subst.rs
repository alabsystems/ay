// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equals-for-equals substitution under asserted ground equalities
//! ([`ay_core::TheoryLemmaKind::GroundEqualitySubstitution`]).
//!
//! Clause shape (positional, producer-fixed):
//!
//! ```text
//! (cl (not (= e_1 v_1)) .. (not (= e_k v_k)) (not P) Q)      k >= 1
//! ```
//!
//! Valid iff every `v_i` is a literal constant, `P` is quantifier-free, every
//! `e_i` occurs in `P`, and `Q` is EXACTLY `P` with all occurrences of each
//! `e_i` simultaneously replaced by `v_i`. Soundness is substitution of
//! equals: under the hypotheses `e_i = v_i`, every occurrence rewrite is an
//! equivalence, and capture is impossible because `P` carries no binders and
//! each `v_i` is a closed literal.
//!
//! The recognizer IS the validator: it re-walks `P` and `Q` in parallel
//! against the substitution map and fails closed on any node pair the map
//! does not explain — a node equal on both sides must contain NO mapped key
//! (all occurrences must have been replaced), a mapped key on the left must
//! face exactly its value on the right, and any other divergence must
//! decompose structurally. No term is interned; the walk is budgeted.
//!
//! Introduced for the checked-SAT refutation's ground-encoding bridge (the
//! deductive-checks letleak shape): a solver lane substitutes an entailed constant
//! (`len -> 1`) into a recorded quantifier instance below every provenance
//! seam, and this lemma re-derives the substituted clause from the exact
//! recorded instance plus the authored defining equalities.
//!
//! SECOND ACCEPTANCE LEG — substitution composed with CHECKED GROUND
//! NORMALIZATION. The ground encoder does not stop at substitution: it also
//! folds what the substitution made foldable (`(= 1 1)` -> true,
//! `(not true)` -> false, dropped `or`/`and` identity elements) and
//! canonicalizes INTEGER comparisons (`(< x 1)` -> `(<= x 0)`). When the
//! exact parallel walk refuses, the validator re-derives both sides through
//! an INDEPENDENT normalizer — substitution applied during the walk, every
//! fold equivalence-preserving over the Int order, comparisons gated on
//! Int-sorted arguments (a Real-sorted `<` is NOT `<=`-shiftable and stays
//! structural) — and accepts only when the two normal forms are identical.
//! Soundness: `Q` then differs from `subst(P)` by equivalences alone, so
//! the clause implication holds by substitution of equals.

use ay_core::kani_compat::DetHashMap;
use ay_core::{ProofId, TermData, TermId, TermStore};

use super::ProofCheckError;

mod normalize;
mod structural;

use normalize::normalize_with_substitution;
use structural::{is_literal_constant, key_occurs_or_binder, substituted_exactly};

/// Node budget for the combined occurs/parallel walks of one validation.
const GROUND_SUBST_WALK_BUDGET: usize = 200_000;

fn invalid(step: ProofId, reason: impl Into<String>) -> ProofCheckError {
    ProofCheckError::InvalidTheoryLemma {
        step,
        reason: reason.into(),
    }
}

/// Strict validation of one `GroundEqualitySubstitution` clause; see the
/// module docs for the shape and the soundness argument.
pub(crate) fn validate_ground_equality_substitution(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() < 3 {
        return Err(invalid(
            step_id,
            "ground-equality substitution needs at least (not eq), (not P), Q",
        ));
    }
    let q = clause[clause.len() - 1];
    let TermData::Not(p) = terms.get(clause[clause.len() - 2]) else {
        return Err(invalid(
            step_id,
            "second-to-last literal must be the negated source term (not P)",
        ));
    };
    let p = *p;
    let mut map: DetHashMap<TermId, TermId> = DetHashMap::default();
    for &literal in &clause[..clause.len() - 2] {
        let TermData::Not(equality) = terms.get(literal) else {
            return Err(invalid(
                step_id,
                "leading literals must be negated equalities",
            ));
        };
        let TermData::App(symbol, args) = terms.get(*equality) else {
            return Err(invalid(step_id, "leading literal is not an equality"));
        };
        if symbol.name() != "=" || args.len() != 2 {
            return Err(invalid(step_id, "leading literal is not a binary equality"));
        }
        let (key, value) = (args[0], args[1]);
        if !is_literal_constant(terms, value) {
            return Err(invalid(
                step_id,
                "equality right-hand side must be a literal constant",
            ));
        }
        if key == value || is_literal_constant(terms, key) {
            return Err(invalid(
                step_id,
                "equality left-hand side must be a non-constant key",
            ));
        }
        if let Some(existing) = map.insert(key, value) {
            if existing != value {
                return Err(invalid(step_id, "conflicting values for one key"));
            }
        }
    }
    if map.is_empty() {
        return Err(invalid(step_id, "no substitution equalities"));
    }
    let mut budget = GROUND_SUBST_WALK_BUDGET;
    // Sharpness: every key must actually occur in P (an unused hypothesis is
    // producer sloppiness the strict lane refuses), and P must genuinely move.
    for &key in map.keys() {
        let mut single: DetHashMap<TermId, TermId> = DetHashMap::default();
        single.insert(key, key);
        match key_occurs_or_binder(terms, p, &single, &mut budget) {
            Ok(true) => {}
            Ok(false) => return Err(invalid(step_id, "a substitution key does not occur in P")),
            Err(()) => return Err(invalid(step_id, "substitution walk budget exhausted")),
        }
    }
    if p == q {
        return Err(invalid(
            step_id,
            "P and Q are identical — nothing substituted",
        ));
    }
    match substituted_exactly(terms, p, q, &map, &mut budget) {
        Ok(true) => Ok(()),
        Ok(false) => {
            // Second leg: substitution composed with checked ground
            // normalization (see the module docs for the soundness argument).
            let empty: DetHashMap<TermId, TermId> = DetHashMap::default();
            let lhs = normalize_with_substitution(terms, p, &map, &mut budget);
            let rhs = normalize_with_substitution(terms, q, &empty, &mut budget);
            match (lhs, rhs) {
                (Ok(lhs), Ok(rhs)) if lhs == rhs => Ok(()),
                (Ok(_), Ok(_)) => Err(invalid(
                    step_id,
                    "Q is neither the exact substitution image of P nor its checked ground normal form",
                )),
                _ => Err(invalid(step_id, "substitution walk budget exhausted")),
            }
        }
        Err(()) => Err(invalid(step_id, "substitution walk budget exhausted")),
    }
}

/// Producer-side recognizer — the same computation as the validator.
pub fn recognize_ground_equality_substitution(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_ground_equality_substitution(terms, ProofId(0), clause).is_ok()
}

/// Producer-side pre-check with NO term interning: would the clause
/// `[(not (= k_i v_i)).., (not p), q]` built from `pairs` validate? Runs the
/// same key/value shape checks, sharpness (every key occurs in `p`), and
/// parallel substitution walk as the validator, so a `true` here guarantees
/// the assembled clause passes `validate_ground_equality_substitution`.
/// Lets an emitter decide BEFORE minting the negation literals, keeping the
/// exact-fragment term-store metering exact.
pub fn ground_substitution_image_matches(
    terms: &TermStore,
    p: TermId,
    q: TermId,
    pairs: &[(TermId, TermId)],
) -> bool {
    if pairs.is_empty() || p == q {
        return false;
    }
    let mut map: DetHashMap<TermId, TermId> = DetHashMap::default();
    for &(key, value) in pairs {
        if !is_literal_constant(terms, value) || key == value || is_literal_constant(terms, key) {
            return false;
        }
        if let Some(existing) = map.insert(key, value) {
            if existing != value {
                return false;
            }
        }
    }
    let mut budget = GROUND_SUBST_WALK_BUDGET;
    for &key in map.keys() {
        let mut single: DetHashMap<TermId, TermId> = DetHashMap::default();
        single.insert(key, key);
        match key_occurs_or_binder(terms, p, &single, &mut budget) {
            Ok(true) => {}
            _ => return false,
        }
    }
    match substituted_exactly(terms, p, q, &map, &mut budget) {
        Ok(true) => true,
        Ok(false) => {
            let empty: DetHashMap<TermId, TermId> = DetHashMap::default();
            let lhs = normalize_with_substitution(terms, p, &map, &mut budget);
            let rhs = normalize_with_substitution(terms, q, &empty, &mut budget);
            matches!((&lhs, &rhs), (Ok(l), Ok(r)) if l == r)
        }
        Err(()) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Sort, Symbol};
    use num_bigint::BigInt;

    fn store() -> TermStore {
        TermStore::new()
    }

    fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
        terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
    }

    #[test]
    fn letleak_dn17_shape_normalizes() {
        let mut terms = store();
        let len = terms.mk_var("gl_len", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let w = terms.mk_var("gl_w", Sort::Int);
        let x = terms.mk_var("gl_x", Sort::Int);
        let y = terms.mk_var("gl_y", Sort::Int);
        let n = terms.mk_app(Symbol::named("bv2nat_stub"), [w], Sort::Int);
        let lt_len = terms.mk_app(Symbol::named("<"), [n, len], Sort::Bool);
        let lt_one = terms.mk_app(Symbol::named("<"), [n, one], Sort::Bool);
        let xy = eq(&mut terms, x, y);
        let not_xy = terms.mk_not_raw(xy);
        let len_eq = eq(&mut terms, len, one);
        let not_len_eq = terms.mk_not_raw(len_eq);
        let and_p = terms.mk_app(Symbol::named("and"), [lt_len, not_xy], Sort::Bool);
        let p = terms.mk_app(Symbol::named("or"), [not_len_eq, and_p], Sort::Bool);
        let fls = terms.mk_bool(false);
        let and_q = terms.mk_app(Symbol::named("and"), [lt_one, not_xy], Sort::Bool);
        let q = terms.mk_app(Symbol::named("or"), [fls, and_q], Sort::Bool);
        let clause = vec![terms.mk_not_raw(len_eq), terms.mk_not_raw(p), q];
        assert!(
            recognize_ground_equality_substitution(&terms, &clause),
            "dn17-shape substitution+normalization must validate"
        );
    }

    #[test]
    fn exact_substitution_validates() {
        let mut terms = store();
        let len = terms.mk_var("gs_len", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let x = terms.mk_var("gs_x", Sort::Int);
        let p = terms.mk_app(Symbol::named("<"), [x, len], Sort::Bool);
        let q = terms.mk_app(Symbol::named("<"), [x, one], Sort::Bool);
        let hyp = eq(&mut terms, len, one);
        let clause = vec![terms.mk_not_raw(hyp), terms.mk_not_raw(p), q];
        assert!(recognize_ground_equality_substitution(&terms, &clause));
    }

    #[test]
    fn unreplaced_occurrence_rejects() {
        let mut terms = store();
        let len = terms.mk_var("gs2_len", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        // P = (+ len len), Q = (+ 1 len): only one occurrence replaced.
        let p = terms.mk_app(Symbol::named("+"), [len, len], Sort::Int);
        let q = terms.mk_app(Symbol::named("+"), [one, len], Sort::Int);
        let p_atom = eq(&mut terms, p, one);
        let q_atom = eq(&mut terms, q, one);
        let hyp = eq(&mut terms, len, one);
        let clause = vec![terms.mk_not_raw(hyp), terms.mk_not_raw(p_atom), q_atom];
        assert!(!recognize_ground_equality_substitution(&terms, &clause));
    }

    #[test]
    fn wrong_value_rejects() {
        let mut terms = store();
        let len = terms.mk_var("gs3_len", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let two = terms.mk_int(BigInt::from(2));
        let x = terms.mk_var("gs3_x", Sort::Int);
        let p = terms.mk_app(Symbol::named("<"), [x, len], Sort::Bool);
        let q = terms.mk_app(Symbol::named("<"), [x, two], Sort::Bool);
        let hyp = eq(&mut terms, len, one);
        let clause = vec![terms.mk_not_raw(hyp), terms.mk_not_raw(p), q];
        assert!(!recognize_ground_equality_substitution(&terms, &clause));
    }

    #[test]
    fn quantified_source_rejects() {
        let mut terms = store();
        let len = terms.mk_var("gs4_len", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let x = terms.mk_var("gs4_x", Sort::Int);
        let body = terms.mk_app(Symbol::named("<"), [x, len], Sort::Bool);
        let body_sub = terms.mk_app(Symbol::named("<"), [x, one], Sort::Bool);
        let p = terms.mk_forall(vec![("gs4_x".to_string(), Sort::Int)], body);
        let q = terms.mk_forall(vec![("gs4_x".to_string(), Sort::Int)], body_sub);
        let hyp = eq(&mut terms, len, one);
        let clause = vec![terms.mk_not_raw(hyp), terms.mk_not_raw(p), q];
        assert!(!recognize_ground_equality_substitution(&terms, &clause));
    }

    #[test]
    fn unused_hypothesis_rejects() {
        let mut terms = store();
        let len = terms.mk_var("gs5_len", Sort::Int);
        let other = terms.mk_var("gs5_other", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let x = terms.mk_var("gs5_x", Sort::Int);
        let p = terms.mk_app(Symbol::named("<"), [x, len], Sort::Bool);
        let q = terms.mk_app(Symbol::named("<"), [x, one], Sort::Bool);
        let hyp_len = eq(&mut terms, len, one);
        let hyp_other = eq(&mut terms, other, one);
        let clause = vec![
            terms.mk_not_raw(hyp_len),
            terms.mk_not_raw(hyp_other),
            terms.mk_not_raw(p),
            q,
        ];
        assert!(!recognize_ground_equality_substitution(&terms, &clause));
    }
}
