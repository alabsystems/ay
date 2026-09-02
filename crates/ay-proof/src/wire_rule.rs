// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complete-step selection of externally meaningful theory-lemma rules.

use ay_core::kani_compat::DetHashMap;
use ay_core::{
    Constant, FarkasAnnotation, LiaAnnotation, Proof, ProofId, ProofStep, Symbol, TermData, TermId,
    TermStore, TheoryLemmaKind, TheoryLit, UNPROVED_STEP_RULE,
};
use num_traits::Zero;

use crate::alethe_printer::ClauseSurfaceAgreement;

/// Whether the exact clause authenticated against AY's term DAG is also the
/// exact clause the Alethe printer will expose to an external checker.
///
/// Certificate producers use this before attaching numeric evidence whose
/// operand orientation is significant.  An override that changes even one
/// reachable subterm must be bridged before that evidence can be published;
/// silently repairing coefficients against opaque source text would make the
/// text, rather than the authenticated term DAG, the proof authority.
#[must_use]
pub fn exact_clause_surface_preserved(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> bool {
    crate::alethe_printer::clause_surface_agreement(terms, clause, term_overrides)
        == ClauseSurfaceAgreement::Identical
}

/// Largest number of native arithmetic lemmas one proof may probe for the
/// expensive `poly_simp` wire lowering.
///
/// The lowering is a completeness-only presentation repair. A proof above
/// this cap keeps honest `hole` spellings instead of multiplying the two
/// recognizers' large local work envelopes by its step count.
pub const MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF: usize = 16;

/// Proof-wide admission and attempt budget for `poly_simp` wire promotion.
///
/// [`Self::for_proof`] is an allocation-free borrowed preflight. If the proof
/// has more candidate steps than the cap, every attempt is disabled before the
/// first recognizer runs. The remaining counter is still checked at each call,
/// so direct step-formatting users that bypass proof preparation cannot exceed
/// the same envelope.
pub struct ArithPolySimpPromotionBudget {
    remaining: usize,
    proof_admitted: bool,
}

impl ArithPolySimpPromotionBudget {
    /// Preflight one complete proof without cloning steps or clauses.
    #[must_use]
    pub fn for_proof(proof: &Proof) -> Self {
        let candidate_count = proof
            .steps
            .iter()
            .filter(|step| {
                matches!(
                    step,
                    ProofStep::TheoryLemma {
                        kind: TheoryLemmaKind::ArithClauseTautology,
                        ..
                    }
                ) || matches!(
                    step,
                    ProofStep::TheoryLemma {
                        kind: TheoryLemmaKind::LiaGeneric,
                        lia: Some(LiaAnnotation::LinearIdentity),
                        ..
                    }
                )
            })
            .take(MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF + 1)
            .count();
        let proof_admitted = candidate_count <= MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF;
        Self {
            remaining: if proof_admitted {
                MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF
            } else {
                0
            },
            proof_admitted,
        }
    }

    /// Budget for isolated formatting helpers that have no complete proof to
    /// preflight. The per-attempt counter remains authoritative.
    pub(crate) const fn standalone() -> Self {
        Self {
            remaining: MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF,
            proof_admitted: true,
        }
    }

    /// Whether the whole-proof preflight admitted any promotion attempts.
    #[must_use]
    pub const fn proof_admitted(&self) -> bool {
        self.proof_admitted
    }

    fn spend_attempt(&mut self) -> bool {
        let Some(remaining) = self.remaining.checked_sub(1) else {
            return false;
        };
        self.remaining = remaining;
        true
    }
}

/// Whether one native arithmetic tautology has the exact checked
/// premise-free `poly_simp` lowering emitted by the Alethe printer.
///
/// Both the printer and the publication wire-gap screen consume this
/// predicate. The arithmetic recognizers reason about the internal term DAG,
/// so a source-syntax override may authorize the lowering only when it leaves
/// the rendered clause byte-for-byte identical.
#[must_use]
pub fn arith_poly_simp_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&DetHashMap<TermId, String>>,
    budget: &mut ArithPolySimpPromotionBudget,
) -> bool {
    budget.spend_attempt()
        && crate::alethe_printer::clause_surface_agreement(terms, clause, term_overrides)
            == ClauseSurfaceAgreement::Identical
        && crate::recognize_arith_poly_simp(terms, clause)
        && crate::recognize_arith_clause_tautology(terms, clause)
}

/// Whether this exact theory-lemma classification may use the shared checked
/// `poly_simp` lowering.
///
/// `LiaGeneric` linear identities are unit positive equalities. They cannot be
/// sent through `la_generic`: negating the clause produces a disequality,
/// which Carcara's `la_generic` rule rejects. The independent polynomial and
/// arithmetic-tautology recognizers can instead re-derive the same clause as a
/// premise-free `poly_simp` theorem. Both native kinds share the same surface
/// and proof-wide attempt budget.
#[must_use]
pub fn theory_lemma_poly_simp_lowering_supported(
    terms: &TermStore,
    kind: &TheoryLemmaKind,
    lia: Option<&LiaAnnotation>,
    clause: &[TermId],
    term_overrides: Option<&DetHashMap<TermId, String>>,
    budget: &mut ArithPolySimpPromotionBudget,
) -> bool {
    let lia_linear_identity = matches!(kind, TheoryLemmaKind::LiaGeneric)
        && matches!(lia, Some(LiaAnnotation::LinearIdentity));
    (matches!(kind, TheoryLemmaKind::ArithClauseTautology) || lia_linear_identity)
        // Preserve the established smaller ground `evaluate` lowering. This
        // check is shared by the terminal screen and printer, before either
        // spends a poly_simp attempt, so their rule precedence cannot drift.
        && !(lia_linear_identity && lia_ground_evaluate_is_supported(terms, clause))
        && arith_poly_simp_lowering_supported(terms, clause, term_overrides, budget)
}

/// Whether an exact integer bounds tautology has the checked `la_generic`
/// lowering emitted by the Alethe printer.
#[must_use]
pub fn int_bounds_tautology_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> bool {
    crate::alethe_printer::clause_surface_agreement(terms, clause, term_overrides)
        == ClauseSurfaceAgreement::Identical
        && carcara_la_generic_clause_supported(terms, clause)
        && ay_core::proof_validation::recognize_int_bounds_tautology(terms, clause)
}

const MAX_CARCARA_LINEAR_WIRE_NODES: usize = 100_000;
const MAX_CARCARA_LINEAR_WIRE_DEPTH: usize = 256;
const MAX_REORIENTED_FARKAS_RENDER_WORK: u64 = 1_048_576;
const MAX_REORIENTED_FARKAS_SIGN_CHECKS: usize = 65_536;
const MAX_REORIENTED_FARKAS_PARSE_BYTES: usize = 1_048_576;
const MAX_DIVERGENT_PRINTED_FARKAS_ROWS: usize = 8;

#[derive(Clone, Copy)]
enum FarkasSurfacePolicy {
    /// Accept identity and exact same-atom order/equality reorientation only.
    SameAtomOnly,
    /// An explicit `LraFarkas` row may instead prove the exact effective
    /// printed clause independently, within the narrow row/work bounds below.
    ReplayExactPrintedClause,
}

/// Whether Carcara's `negate_disequality` accepts every clause literal and its
/// `LinearComb::from_term` shares AY's syntactic interpretation of every
/// arithmetic operand.
///
/// In particular, Carcara flattens multiplication only when it is binary and
/// one direct operand is a wire numeral/fraction. Otherwise it retains the
/// whole product as an opaque atom. AY also folds n-ary numeric products and
/// computed constants such as `(+ 1 1)` in coefficient position, but retains
/// a product as that same opaque atom after seeing two nonconstant factors.
/// Printing a product outside those shared cases under `la_generic` can make
/// the two checkers build different linear rows. At the literal boundary
/// Carcara accepts either polarity of an order comparison, and a NEGATED
/// equality (whose negation is an equality row), but not a positive equality
/// or SMT-LIB `distinct`.
///
/// This deliberately conservative shared grammar retains direct binary
/// numeral products and the complete equality/order relation surface while
/// rejecting every known parser-mismatch class.
fn carcara_la_generic_clause_supported(terms: &TermStore, clause: &[TermId]) -> bool {
    let mut nodes_left = MAX_CARCARA_LINEAR_WIRE_NODES;
    if !clause.iter().all(|&literal| {
        let Some(remaining) = nodes_left.checked_sub(1) else {
            return false;
        };
        nodes_left = remaining;
        let (relation, outer_negated) = match terms.get(literal) {
            TermData::Not(inner) => (*inner, true),
            _ => (literal, false),
        };
        let TermData::App(Symbol::Named(operator), operands) = terms.get(relation) else {
            return false;
        };
        let [left, right] = operands.as_slice() else {
            return false;
        };
        (matches!(operator.as_str(), "<" | "<=" | ">" | ">=") || (outer_negated && operator == "="))
            && carcara_linear_term_supported(terms, *left, 0, &mut nodes_left)
            && carcara_linear_term_supported(terms, *right, 0, &mut nodes_left)
    }) {
        return false;
    }
    // The internal grammar alone cannot see lexical failures introduced by
    // rendering (notably AY/Z3 `\|` escapes, which pinned Carcara rejects).
    // Render the exact canonical literals under the same bounded work envelope
    // used by divergent-surface replay and re-run the printed grammar.
    let no_overrides = DetHashMap::default();
    let Ok(rendered) = crate::format_terms_alethe_with_overrides_bounded(
        terms,
        clause,
        &no_overrides,
        MAX_REORIENTED_FARKAS_RENDER_WORK,
    ) else {
        return false;
    };
    clause.iter().all(|literal| {
        rendered
            .get(literal)
            .is_some_and(|printed| crate::carcara_printed_la_generic_literal_supported(printed))
    })
}

/// Whether this exact Farkas theory lemma can be published through the pinned
/// checker's `la_generic` rule.
///
/// This is the single fail-closed authority shared by Farkas producers, the
/// terminal wire-gap screen, and the Alethe printer. It requires the same
/// clause surface the external checker will read, Carcara's exact accepted
/// literal relation shape and conservative shared linear-term grammar, and an
/// actual AY-validated linear Farkas contradiction. Surface order reversal is
/// retained because the classifier has already proved it is the same atom
/// expressed with the converse comparison operator.
#[must_use]
pub fn la_generic_farkas_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    farkas: &FarkasAnnotation,
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> bool {
    la_generic_farkas_lowering_supported_with_policy(
        terms,
        clause,
        farkas,
        term_overrides,
        FarkasSurfacePolicy::SameAtomOnly,
    )
}

fn la_generic_farkas_lowering_supported_with_policy(
    terms: &TermStore,
    clause: &[TermId],
    farkas: &FarkasAnnotation,
    term_overrides: Option<&DetHashMap<TermId, String>>,
    surface_policy: FarkasSurfacePolicy,
) -> bool {
    let agreement = crate::alethe_printer::clause_surface_agreement(terms, clause, term_overrides);
    let conflict: Vec<TheoryLit> = clause
        .iter()
        .map(|&literal| match terms.get(literal) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(literal, false),
        })
        .collect();
    if !carcara_la_generic_clause_supported(terms, clause)
        || ay_core::proof_validation::verify_farkas_conflict_lits_linear(terms, &conflict, farkas)
            .is_err()
    {
        return false;
    }
    match agreement {
        ClauseSurfaceAgreement::Identical | ClauseSurfaceAgreement::OrderReversed => true,
        ClauseSurfaceAgreement::EqualityReversed => {
            effective_printed_farkas_is_valid(terms, clause, farkas, term_overrides)
        }
        ClauseSurfaceAgreement::Divergent => {
            matches!(
                surface_policy,
                FarkasSurfacePolicy::ReplayExactPrintedClause
            ) && clause.len() <= MAX_DIVERGENT_PRINTED_FARKAS_ROWS
                && effective_printed_farkas_is_valid(terms, clause, farkas, term_overrides)
        }
    }
}

fn effective_printed_farkas_is_valid(
    terms: &TermStore,
    clause: &[TermId],
    farkas: &FarkasAnnotation,
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> bool {
    let Some(term_overrides) = term_overrides else {
        return false;
    };
    let Ok(rendered) = crate::format_terms_alethe_with_overrides_bounded(
        terms,
        clause,
        term_overrides,
        MAX_REORIENTED_FARKAS_RENDER_WORK,
    ) else {
        return false;
    };
    let mut remaining_checks = MAX_REORIENTED_FARKAS_SIGN_CHECKS;
    let mut remaining_parse_bytes = MAX_REORIENTED_FARKAS_PARSE_BYTES;
    crate::printed_la_generic_certificate_is_valid_bounded(
        terms,
        clause,
        farkas,
        &rendered,
        &mut remaining_checks,
        &mut remaining_parse_bytes,
    )
}

fn carcara_linear_term_supported(
    terms: &TermStore,
    term: TermId,
    depth: usize,
    nodes_left: &mut usize,
) -> bool {
    if depth > MAX_CARCARA_LINEAR_WIRE_DEPTH {
        return false;
    }
    let Some(remaining) = nodes_left.checked_sub(1) else {
        return false;
    };
    *nodes_left = remaining;
    let recurse = |child, nodes_left: &mut usize| {
        carcara_linear_term_supported(terms, child, depth + 1, nodes_left)
    };
    match terms.get(term) {
        TermData::App(Symbol::Named(operator), operands) if operator == "+" => {
            operands.len() >= 2
                && operands
                    .iter()
                    .copied()
                    .all(|operand| recurse(operand, nodes_left))
        }
        TermData::App(Symbol::Named(operator), operands) if operator == "-" => {
            !operands.is_empty()
                && operands
                    .iter()
                    .copied()
                    .all(|operand| recurse(operand, nodes_left))
        }
        TermData::App(Symbol::Named(operator), operands) if operator == "*" => {
            if let [left, right] = operands.as_slice() {
                if (carcara_wire_fraction(terms, *left) && recurse(*right, nodes_left))
                    || (carcara_wire_fraction(terms, *right) && recurse(*left, nodes_left))
                {
                    return true;
                }
            }

            // With no direct binary coefficient Carcara makes the complete
            // product one opaque atom. AY does exactly the same after its
            // linearizer encounters a second nonconstant factor. Admit only
            // factors whose nonconstancy is structurally certain, so a
            // computed constant such as `(+ 1 1)` can never be mistaken for
            // the first of those factors.
            at_least_two_definitely_nonconstant(terms, operands, depth + 1, nodes_left)
        }
        // AY and Carcara both understand a direct rational fraction. Every
        // computed numerator/denominator, and integer `div`, remains outside
        // this exact shared grammar.
        TermData::App(Symbol::Named(operator), _) if operator == "/" => {
            carcara_wire_fraction(terms, term)
        }
        TermData::App(Symbol::Named(operator), _) if operator == "div" => false,
        _ => true,
    }
}

/// A fail-closed witness that AY's linear parser cannot reduce `term` to a
/// constant. This is intentionally narrower than AY's full parser: it exists
/// only to prove when a multiplication reaches AY's "second nonconstant
/// factor" branch and becomes the complete product's opaque atom.
fn ay_linear_term_definitely_nonconstant(
    terms: &TermStore,
    term: TermId,
    depth: usize,
    nodes_left: &mut usize,
) -> bool {
    if depth > MAX_CARCARA_LINEAR_WIRE_DEPTH {
        return false;
    }
    let Some(remaining) = nodes_left.checked_sub(1) else {
        return false;
    };
    *nodes_left = remaining;

    match terms.get(term) {
        TermData::Var(_, _) => true,
        TermData::Const(Constant::Int(_) | Constant::Rational(_)) => false,
        TermData::App(Symbol::Named(operator), _) if operator == "+" => false,
        TermData::App(Symbol::Named(operator), operands) if operator == "-" => {
            matches!(operands.as_slice(), [inner]
            if ay_linear_term_definitely_nonconstant(
                terms,
                *inner,
                depth + 1,
                nodes_left,
            ))
        }
        TermData::App(Symbol::Named(operator), operands) if operator == "*" => {
            at_least_two_definitely_nonconstant(terms, operands, depth + 1, nodes_left)
        }
        // A well-shaped quotient may become constant after AY recursively
        // evaluates its operands. Conservatively decline it here. Every
        // differently shaped named arithmetic form falls through to AY's
        // opaque-variable branch and is necessarily nonconstant.
        TermData::App(Symbol::Named(operator), operands)
            if operator == "/" && operands.len() == 2 =>
        {
            false
        }
        _ => true,
    }
}

fn at_least_two_definitely_nonconstant(
    terms: &TermStore,
    operands: &[TermId],
    depth: usize,
    nodes_left: &mut usize,
) -> bool {
    let mut found = 0_u8;
    for &operand in operands {
        // Stop traversing a wide node as soon as the shared work allowance is
        // exhausted. Continuing to scan siblings after every recursive probe
        // fails would make the nominal node cap ineffective.
        if *nodes_left == 0 {
            return false;
        }
        if ay_linear_term_definitely_nonconstant(terms, operand, depth, nodes_left) {
            found += 1;
            if found == 2 {
                return true;
            }
        }
    }
    false
}

fn carcara_wire_fraction(terms: &TermStore, term: TermId) -> bool {
    if carcara_wire_signed_number(terms, term) {
        return true;
    }
    match terms.get(term) {
        TermData::App(Symbol::Named(operator), operands) if operator == "-" => {
            let [inner] = operands.as_slice() else {
                return false;
            };
            carcara_wire_unsigned_fraction(terms, *inner)
        }
        _ => carcara_wire_unsigned_fraction(terms, term),
    }
}

fn carcara_wire_unsigned_fraction(terms: &TermStore, term: TermId) -> bool {
    if matches!(
        terms.get(term),
        TermData::Const(Constant::Int(_) | Constant::Rational(_))
    ) {
        return true;
    }
    let TermData::App(Symbol::Named(operator), operands) = terms.get(term) else {
        return false;
    };
    let [numerator, denominator] = operands.as_slice() else {
        return false;
    };
    operator == "/"
        && carcara_wire_signed_number(terms, *numerator)
        && carcara_wire_signed_number(terms, *denominator)
        && carcara_wire_signed_number_is_nonzero(terms, *denominator)
}

fn carcara_wire_signed_number(terms: &TermStore, term: TermId) -> bool {
    if matches!(
        terms.get(term),
        TermData::Const(Constant::Int(_) | Constant::Rational(_))
    ) {
        return true;
    }
    matches!(
        terms.get(term),
        TermData::App(Symbol::Named(operator), operands)
            if operator == "-"
                && matches!(operands.as_slice(), [inner]
                    if matches!(terms.get(*inner),
                        TermData::Const(Constant::Int(_) | Constant::Rational(_))))
    )
}

fn carcara_wire_signed_number_is_nonzero(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) => !value.is_zero(),
        TermData::Const(Constant::Rational(value)) => !value.0.is_zero(),
        TermData::App(Symbol::Named(operator), operands) if operator == "-" => {
            matches!(operands.as_slice(), [inner]
                if carcara_wire_signed_number_is_nonzero(terms, *inner))
        }
        _ => false,
    }
}

/// Whether one native arithmetic equality triangle has the exact checked
/// multi-step lowering emitted by the Alethe printer.
///
/// The internal recognizer authenticates the positional `L <= R`, `R <= L`,
/// and `L = R` relationship. The external derivation is assembled from their
/// rendered text, so every reachable surface override must leave that text
/// byte-for-byte identical to the authenticated internal clause.
#[must_use]
pub fn arith_eq_triangle_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> bool {
    crate::alethe_printer::clause_surface_agreement(terms, clause, term_overrides)
        == ClauseSurfaceAgreement::Identical
        && crate::recognize_arith_eq_triangle(terms, clause)
}

/// Whether the equality-to-bound adapter has the exact checked `la_generic`
/// lowering emitted by the Alethe printer.
///
/// Both native structure and effective text are load-bearing: the fixed
/// coefficients `(-1 1)` are valid only for the strict checker's positional
/// `not (= a b), (<= a b|b a)` shape, and no surface rewrite may change those
/// rows before Carcara consumes them.
#[must_use]
pub fn arith_eq_implies_bound_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> bool {
    let farkas = FarkasAnnotation::from_ints(&[-1, 1]);
    exact_clause_surface_preserved(terms, clause, term_overrides)
        && crate::recognize_arith_eq_implies_bound(terms, clause)
        && la_generic_farkas_lowering_supported(terms, clause, &farkas, term_overrides)
}

/// Whether a strictly checked `evaluate` step retains the exact clause text
/// whose ground semantics the internal validator authenticated.
///
/// `evaluate` is directional and recursively interprets its left-hand term.
/// A surface override on the equality or any reachable subterm can therefore
/// change the external proposition without changing the internal DAG. Both
/// the printer and publication gate use this conservative identity test.
#[must_use]
pub fn evaluate_step_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> bool {
    crate::alethe_printer::clause_surface_agreement(terms, clause, term_overrides)
        == ClauseSurfaceAgreement::Identical
}

/// Whether one native `Divisibility` lemma has the exact checked external
/// lowering implemented by the Alethe printer.
///
/// This is consumed by both the printer and the publication wire-gap screen.
/// Requiring an identity surface is deliberate: the lattice witness was
/// derived from the internal term DAG, so a spelling channel that changes the
/// clause must be bridged or purged before this certificate can publish.
#[must_use]
pub fn lia_divisibility_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    lia: Option<&LiaAnnotation>,
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> bool {
    matches!(lia, Some(LiaAnnotation::Divisibility))
        && crate::alethe_printer::clause_surface_agreement(terms, clause, term_overrides)
            == ClauseSurfaceAgreement::Identical
        && ay_core::proof_validation::lia_divisibility_equality_witness(terms, clause).is_some()
}

/// Select the externally meaningful wire rule for one complete theory lemma.
///
/// The pinned Alethe checker recognizes `lia_generic` but treats it as an
/// unchecked placeholder. A [`TheoryLemmaKind::LiaGeneric`] step therefore
/// stays an honest [`UNPROVED_STEP_RULE`] unless either its clause is accepted
/// by the independent ground `evaluate` validator, or its actual Farkas
/// annotation proves the clause in the checker's linear fragment and can be
/// promoted to checked `la_generic`.
///
/// Surface overrides are a hard barrier for both promotions whenever they
/// CHANGE WHAT THIS CLAUSE SAYS. The validators reason about the internal term
/// DAG, while an override changes the text the external checker reads; a
/// promotion is honest exactly when those two agree, which
/// [`crate::alethe_printer::clause_surface_agreement`] decides by re-rendering
/// the clause without the channel.
///
/// One deliberately narrower exception applies to an explicit
/// [`TheoryLemmaKind::LraFarkas`] certificate with at most eight rows: the
/// shared gate may re-render and independently replay the exact printed
/// clause through the Carcara-faithful linear parser. This does not infer that
/// a divergent spelling denotes the internal term; it proves the emitted
/// clause as a fresh arithmetic theorem. A spelling that makes the printed
/// hypotheses satisfiable is rejected. Generic LIA promotion and producer
/// admission keep the same-atom-only policy.
///
/// Screening the whole document instead — refusing whenever the channel is
/// installed at all — threw away checkable evidence for every clause the
/// overrides never touched, which is how a composed authored root degraded an
/// independently checked ground `evaluate` step to `hole`.
///
/// [`ClauseSurfaceAgreement::OrderReversed`] is the residual case that byte
/// comparison over-refused. `TermStore::mk_gt`/`mk_ge` canonicalize an
/// authored `(> t u)` into `(< u t)`, and the surface channel then re-spells
/// that atom back to the problem's own `(> t u)` — the SAME atom, printed
/// converse-first. There is nothing to reconcile semantically, so the Farkas
/// promotion stands; the `evaluate` lowering is nevertheless withheld, because
/// `format_lia_ground_evaluate` self-guards on byte-identical clause text and
/// would silently fall back to a `hole` the gate had already granted. Keeping
/// that arm on `Identical` is what keeps the two consumers exact.
///
/// Both the Alethe printer and the publication wire-gap gate consume THIS
/// function with the same override state, so the narrowed test cannot drift
/// between them; neither may reconstruct the decision from
/// [`TheoryLemmaKind::alethe_wire_rule`] alone.
#[must_use]
pub fn promoted_wire_rule<'a>(
    terms: &TermStore,
    kind: &'a TheoryLemmaKind,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> &'a str {
    if matches!(kind, TheoryLemmaKind::LraFarkas) {
        return farkas
            .filter(|farkas| {
                la_generic_farkas_lowering_supported_with_policy(
                    terms,
                    clause,
                    farkas,
                    term_overrides,
                    FarkasSurfacePolicy::ReplayExactPrintedClause,
                )
            })
            .map_or(UNPROVED_STEP_RULE, |_| "la_generic");
    }
    if !matches!(kind, TheoryLemmaKind::LiaGeneric) {
        return kind.alethe_wire_rule();
    }
    let agreement = crate::alethe_printer::clause_surface_agreement(terms, clause, term_overrides);
    if agreement == ClauseSurfaceAgreement::Divergent {
        return UNPROVED_STEP_RULE;
    }
    if agreement == ClauseSurfaceAgreement::Identical
        && lia_ground_evaluate_is_supported(terms, clause)
    {
        return "evaluate";
    }
    let Some(farkas) = farkas else {
        return UNPROVED_STEP_RULE;
    };
    if la_generic_farkas_lowering_supported(terms, clause, farkas, term_overrides) {
        "la_generic"
    } else {
        UNPROVED_STEP_RULE
    }
}

fn lia_ground_evaluate_is_supported(terms: &TermStore, clause: &[TermId]) -> bool {
    if crate::checker::validate_ground_evaluate_for_printer(terms, ProofId(0), clause, 0, &[])
        .is_ok()
    {
        return true;
    }
    let [literal] = clause else {
        return false;
    };
    let TermData::Not(equality) = terms.get(*literal) else {
        return false;
    };
    matches!(
        terms.get(*equality),
        TermData::App(Symbol::Named(operator), operands)
            if operator == "=" && operands.len() == 2
    ) && crate::checker::recognize_ground_evaluate(terms, *literal)
}

#[cfg(test)]
mod tests {
    use ay_core::{FarkasAnnotation, Sort, Symbol};
    use num_bigint::BigInt;

    use super::*;

    fn comparison(terms: &mut TermStore, left: i64, right: i64) -> TermId {
        let left = terms.mk_int(BigInt::from(left));
        let right = terms.mk_int(BigInt::from(right));
        terms.mk_app(Symbol::named("<"), [left, right], Sort::Bool)
    }

    fn integer_gap_clause(
        terms: &mut TermStore,
        upper_form: TermId,
        lower_form: TermId,
    ) -> [TermId; 2] {
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let upper = terms.mk_app(Symbol::named("<="), [upper_form, zero], Sort::Bool);
        let lower = terms.mk_app(Symbol::named("<="), [one, lower_form], Sort::Bool);
        [terms.mk_not_raw(upper), terms.mk_not_raw(lower)]
    }

    #[test]
    fn symbolic_lia_identities_share_the_poly_simp_proof_budget() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("poly_simp_budget_x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let sum = terms.mk_app(Symbol::named("+"), [x, zero], Sort::Int);
        let identity = terms.mk_app(Symbol::named("="), [sum, x], Sort::Bool);
        let mut proof = Proof::new();
        for _ in 0..=MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF {
            proof.add_theory_lemma_with_lia(
                "LIA",
                vec![identity],
                Some(FarkasAnnotation::from_ints(&[1])),
                TheoryLemmaKind::LiaGeneric,
                LiaAnnotation::LinearIdentity,
            );
        }

        assert!(!ArithPolySimpPromotionBudget::for_proof(&proof).proof_admitted());
    }

    #[test]
    fn int_bounds_wire_grammar_matches_carcara_binary_coefficients_only() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("int_bounds_grammar_x", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let two = terms.mk_int(BigInt::from(2));
        let three = terms.mk_int(BigInt::from(3));
        let six = terms.mk_int(BigInt::from(6));

        let two_x = terms.mk_app(Symbol::named("*"), [two, x], Sort::Int);
        let literal_first = integer_gap_clause(&mut terms, two_x, two_x);
        assert!(ay_core::proof_validation::recognize_int_bounds_tautology(
            &terms,
            &literal_first
        ));
        assert!(int_bounds_tautology_lowering_supported(
            &terms,
            &literal_first,
            None
        ));

        let x_two = terms.mk_app(Symbol::named("*"), [x, two], Sort::Int);
        let literal_second = integer_gap_clause(&mut terms, x_two, x_two);
        assert!(ay_core::proof_validation::recognize_int_bounds_tautology(
            &terms,
            &literal_second
        ));
        assert!(int_bounds_tautology_lowering_supported(
            &terms,
            &literal_second,
            None
        ));

        let nary = terms.mk_app(Symbol::named("*"), [two, three, x], Sort::Int);
        let six_x = terms.mk_app(Symbol::named("*"), [six, x], Sort::Int);
        let nary_clause = integer_gap_clause(&mut terms, nary, six_x);
        assert!(
            ay_core::proof_validation::recognize_int_bounds_tautology(&terms, &nary_clause),
            "AY's internal normalization deliberately remains broader"
        );
        assert!(!int_bounds_tautology_lowering_supported(
            &terms,
            &nary_clause,
            None
        ));

        let computed_two = terms.mk_app(Symbol::named("+"), [one, one], Sort::Int);
        let computed_product = terms.mk_app(Symbol::named("*"), [computed_two, x], Sort::Int);
        let computed_clause = integer_gap_clause(&mut terms, computed_product, two_x);
        assert!(
            ay_core::proof_validation::recognize_int_bounds_tautology(&terms, &computed_clause),
            "AY may fold a computed coefficient internally"
        );
        assert!(!int_bounds_tautology_lowering_supported(
            &terms,
            &computed_clause,
            None
        ));

        let unary_plus = terms.mk_app(Symbol::named("+"), [x], Sort::Int);
        let unary_plus_clause = integer_gap_clause(&mut terms, unary_plus, unary_plus);
        assert!(ay_core::proof_validation::recognize_int_bounds_tautology(
            &terms,
            &unary_plus_clause
        ));
        assert!(
            !int_bounds_tautology_lowering_supported(&terms, &unary_plus_clause, None),
            "pinned Carcara rejects unary plus before checking the rule"
        );
    }

    #[test]
    fn lra_farkas_rejects_computed_coefficient_that_carcara_keeps_opaque() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("wire_computed_coefficient_x", Sort::Int);
        let y = terms.mk_var("wire_computed_coefficient_y", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let two = terms.mk_int(BigInt::from(2));
        let fact = terms.mk_app(Symbol::named("<="), [x, zero], Sort::Bool);
        let not_fact = terms.mk_not_raw(fact);
        let computed_two = terms.mk_app(Symbol::named("+"), [one, one], Sort::Int);
        let computed_product = terms.mk_app(Symbol::named("*"), [computed_two, x], Sort::Int);
        let computed_target =
            terms.mk_app(Symbol::named("<="), [computed_product, zero], Sort::Bool);
        let computed_clause = [not_fact, computed_target];
        let coefficients = FarkasAnnotation::from_ints(&[2, 1]);
        let computed_conflict = [
            TheoryLit::new(fact, true),
            TheoryLit::new(computed_target, false),
        ];

        assert!(
            ay_core::proof_validation::verify_farkas_conflict_lits_linear(
                &terms,
                &computed_conflict,
                &coefficients,
            )
            .is_ok(),
            "AY deliberately folds the computed coefficient internally"
        );
        assert!(!la_generic_farkas_lowering_supported(
            &terms,
            &computed_clause,
            &coefficients,
            None,
        ));
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LraFarkas,
                &computed_clause,
                Some(&coefficients),
                None,
            ),
            UNPROVED_STEP_RULE,
            "Carcara treats `(* (+ 1 1) x)` as one opaque atom"
        );

        let direct_product = terms.mk_app(Symbol::named("*"), [two, x], Sort::Int);
        let direct_target = terms.mk_app(Symbol::named("<="), [direct_product, zero], Sort::Bool);
        let direct_clause = [not_fact, direct_target];
        assert!(la_generic_farkas_lowering_supported(
            &terms,
            &direct_clause,
            &coefficients,
            None,
        ));
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LraFarkas,
                &direct_clause,
                Some(&coefficients),
                None,
            ),
            "la_generic",
            "a direct binary numeral coefficient is in the shared grammar"
        );

        let canceled_factor = terms.mk_app(Symbol::named("-"), [x, x], Sort::Int);
        let canceled_product = terms.mk_app(Symbol::named("*"), [canceled_factor, y], Sort::Int);
        let canceled_target =
            terms.mk_app(Symbol::named("<="), [canceled_product, zero], Sort::Bool);
        let canceled_clause = [canceled_target];
        let unit_coefficient = FarkasAnnotation::from_ints(&[1]);
        let canceled_conflict = [TheoryLit::new(canceled_target, false)];
        assert!(
            ay_core::proof_validation::verify_farkas_conflict_lits_linear(
                &terms,
                &canceled_conflict,
                &unit_coefficient,
            )
            .is_ok(),
            "AY reduces `(* (- x x) y)` to zero internally"
        );
        assert!(!la_generic_farkas_lowering_supported(
            &terms,
            &canceled_clause,
            &unit_coefficient,
            None,
        ));
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LraFarkas,
                &canceled_clause,
                Some(&unit_coefficient),
                None,
            ),
            UNPROVED_STEP_RULE,
            "Carcara keeps the whole canceled-factor product opaque"
        );
    }

    #[test]
    fn la_generic_equality_row_polarity_matches_carcara() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("wire_equality_row_x", Sort::Real);
        let zero = terms.mk_rational(BigInt::from(0).into());
        let equality = terms.mk_app(Symbol::named("="), [x, zero], Sort::Bool);
        let not_equality = terms.mk_not_raw(equality);
        let upper = terms.mk_app(Symbol::named("<="), [x, zero], Sort::Bool);
        let valid_clause = [not_equality, upper];
        let coefficients = FarkasAnnotation::from_ints(&[1, 1]);

        assert!(carcara_la_generic_clause_supported(&terms, &valid_clause));
        assert!(la_generic_farkas_lowering_supported(
            &terms,
            &valid_clause,
            &coefficients,
            None,
        ));
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LraFarkas,
                &valid_clause,
                Some(&coefficients),
                None,
            ),
            "la_generic",
            "`(not (= x 0))` negates to the equality row Carcara accepts"
        );

        let mut symmetric_surface = DetHashMap::default();
        symmetric_surface.insert(equality, "(= 0.0 wire_equality_row_x)".to_string());
        assert!(la_generic_farkas_lowering_supported(
            &terms,
            &valid_clause,
            &coefficients,
            Some(&symmetric_surface),
        ));
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LraFarkas,
                &valid_clause,
                Some(&coefficients),
                Some(&symmetric_surface),
            ),
            "la_generic",
            "an exact equality symmetry is replayed against the printed row"
        );

        assert!(!carcara_la_generic_clause_supported(
            &terms,
            &[equality, upper],
        ));

        let distinct = terms.mk_app(Symbol::named("distinct"), [x, zero], Sort::Bool);
        let distinct_clause = [distinct, upper];
        let distinct_conflict = [
            TheoryLit::new(distinct, false),
            TheoryLit::new(upper, false),
        ];
        assert!(
            ay_core::proof_validation::verify_farkas_conflict_lits_linear(
                &terms,
                &distinct_conflict,
                &coefficients,
            )
            .is_ok(),
            "AY treats a false `distinct` conflict literal as an equality row"
        );
        assert!(!la_generic_farkas_lowering_supported(
            &terms,
            &distinct_clause,
            &coefficients,
            None,
        ));
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LraFarkas,
                &distinct_clause,
                Some(&coefficients),
                None,
            ),
            UNPROVED_STEP_RULE,
            "Carcara's `negate_disequality` does not accept `distinct`"
        );
    }

    #[test]
    fn lia_wire_promotes_only_real_checked_evidence() {
        let mut terms = TermStore::new();
        let two = terms.mk_int(BigInt::from(2));
        let three = terms.mk_int(BigInt::from(3));
        let five = terms.mk_int(BigInt::from(5));
        let sum = terms.mk_app(Symbol::named("+"), [two, three], Sort::Int);
        let tautology = terms.mk_app(Symbol::named("="), [sum, five], Sort::Bool);
        let falsehood = comparison(&mut terms, 1, 0);
        let one = FarkasAnnotation::from_ints(&[1]);

        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &[tautology],
                Some(&one),
                None,
            ),
            "evaluate",
            "a ground truth uses the independently checked evaluate lowering"
        );
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &[falsehood],
                Some(&one),
                None,
            ),
            UNPROVED_STEP_RULE,
            "a certificate for a satisfiable conflict proves nothing"
        );
    }

    #[test]
    fn symbolic_farkas_promotion_and_override_barrier_are_atomic() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("wire_x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let lower = terms.mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
        let upper = terms.mk_app(Symbol::named("<"), [x, zero], Sort::Bool);
        let clause = [terms.mk_not_raw(lower), terms.mk_not_raw(upper)];
        let coefficients = FarkasAnnotation::from_ints(&[1, 1]);

        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                None,
            ),
            "la_generic"
        );

        let mut overrides = DetHashMap::default();
        overrides.insert(x, "(+ wire_x 1)".to_string());
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                Some(&overrides),
            ),
            UNPROVED_STEP_RULE,
            "a surface channel blocks the term-only promotion"
        );
    }

    #[test]
    fn explicit_lra_farkas_replays_a_bounded_divergent_printed_clause() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("wire_surface_replay_x", Sort::Real);
        let zero = terms.mk_rational(BigInt::from(0).into());
        let one = terms.mk_rational(BigInt::from(1).into());
        let equals_zero = terms.mk_app(Symbol::named("="), [x, zero], Sort::Bool);
        let equals_one = terms.mk_app(Symbol::named("="), [one, x], Sort::Bool);
        let clause = [terms.mk_not_raw(equals_zero), terms.mk_not_raw(equals_one)];
        let coefficients = FarkasAnnotation::from_ints(&[1, 1]);

        let mut consistently_respelled = DetHashMap::default();
        consistently_respelled.insert(x, "(+ wire_surface_replay_x 10.0)".to_string());
        assert!(!la_generic_farkas_lowering_supported(
            &terms,
            &clause,
            &coefficients,
            Some(&consistently_respelled),
        ));
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                Some(&consistently_respelled),
            ),
            UNPROVED_STEP_RULE,
            "the generic producer API retains its same-atom-only surface policy"
        );
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LraFarkas,
                &clause,
                Some(&coefficients),
                Some(&consistently_respelled),
            ),
            "la_generic",
            "an explicit LRA certificate may prove the exact printed clause anew"
        );

        let mut made_satisfiable = DetHashMap::default();
        made_satisfiable.insert(equals_zero, "(= wire_surface_replay_x 1.0)".to_string());
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LraFarkas,
                &clause,
                Some(&coefficients),
                Some(&made_satisfiable),
            ),
            UNPROVED_STEP_RULE,
            "a divergent spelling that destroys the contradiction must fail closed"
        );

        let not_equals_zero = clause[0];
        let mut outer_literal_override = DetHashMap::default();
        outer_literal_override.insert(
            not_equals_zero,
            "(not (= wire_surface_replay_x 1.0))".to_string(),
        );
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LraFarkas,
                &clause,
                Some(&coefficients),
                Some(&outer_literal_override),
            ),
            UNPROVED_STEP_RULE,
            "exact replay must render an override on the complete negated literal"
        );
    }

    #[test]
    fn divergent_lra_replay_rejects_products_carcara_keeps_opaque() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("wire_surface_product_x", Sort::Real);
        let zero = terms.mk_rational(BigInt::from(0).into());
        let one = terms.mk_rational(BigInt::from(1).into());
        let two = terms.mk_rational(BigInt::from(2).into());
        let twice_x = terms.mk_app(Symbol::named("*"), [two, x], Sort::Real);
        let equals_zero = terms.mk_app(Symbol::named("="), [twice_x, zero], Sort::Bool);
        let equals_one = terms.mk_app(Symbol::named("="), [one, twice_x], Sort::Bool);
        let clause = [terms.mk_not_raw(equals_zero), terms.mk_not_raw(equals_one)];
        let coefficients = FarkasAnnotation::from_ints(&[1, 1]);

        let mut computed_coefficient = DetHashMap::default();
        computed_coefficient.insert(
            equals_zero,
            "(= (* (+ 1.0 1.0) wire_surface_product_x) 0.0)".to_string(),
        );
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LraFarkas,
                &clause,
                Some(&coefficients),
                Some(&computed_coefficient),
            ),
            UNPROVED_STEP_RULE,
            "Carcara does not flatten a computed multiplication coefficient"
        );

        let mut nary_product = DetHashMap::default();
        nary_product.insert(
            equals_zero,
            "(= (* 2.0 1.0 wire_surface_product_x) 0.0)".to_string(),
        );
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LraFarkas,
                &clause,
                Some(&coefficients),
                Some(&nary_product),
            ),
            UNPROVED_STEP_RULE,
            "Carcara does not flatten an n-ary multiplication"
        );

        let mut unary_plus = DetHashMap::default();
        unary_plus.insert(
            equals_zero,
            "(= (+ wire_surface_product_x) 0.0)".to_string(),
        );
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LraFarkas,
                &clause,
                Some(&coefficients),
                Some(&unary_plus),
            ),
            UNPROVED_STEP_RULE,
            "pinned Carcara rejects unary plus in a divergent override"
        );
    }

    /// The AUTHORED spelling of a canonicalized order atom is the same atom.
    ///
    /// `mk_gt` interns `(> t u)` as `(< u t)`, and the surface channel then
    /// re-spells that exact atom back to the problem's own `(> t u)`. Byte
    /// comparison called that a changed clause and withheld a certificate AY
    /// had already checked; same-atom comparison does not. Every NEAR miss
    /// below still withholds it.
    #[test]
    fn authored_order_reversal_is_the_same_atom_and_keeps_the_certificate() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("wire_rev_x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let lower = terms.mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
        let upper = terms.mk_app(Symbol::named("<"), [x, zero], Sort::Bool);
        let clause = [terms.mk_not_raw(lower), terms.mk_not_raw(upper)];
        let coefficients = FarkasAnnotation::from_ints(&[1, 1]);

        // `(<= 0 wire_rev_x)` is exactly how `(>= wire_rev_x 0)` is interned.
        let mut reversed = DetHashMap::default();
        reversed.insert(lower, "(>= wire_rev_x 0)".to_string());
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                Some(&reversed),
            ),
            "la_generic",
            "the authored converse spelling denotes the validated atom"
        );

        // Same operator, swapped arguments: a DIFFERENT atom.
        let mut swapped = DetHashMap::default();
        swapped.insert(lower, "(<= wire_rev_x 0)".to_string());
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                Some(&swapped),
            ),
            UNPROVED_STEP_RULE,
            "an argument swap without the converse operator is another atom"
        );

        // Converse operator but the wrong STRICTNESS: `(<= 0 x)` reverses to
        // `(>= x 0)`, never to `(> x 0)`.
        let mut strictened = DetHashMap::default();
        strictened.insert(lower, "(> wire_rev_x 0)".to_string());
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                Some(&strictened),
            ),
            UNPROVED_STEP_RULE,
            "the converse spelling may not change strictness"
        );

        // Converse operator, converse order, but a RE-SPELLED operand.
        let mut respelled = DetHashMap::default();
        respelled.insert(lower, "(>= (+ wire_rev_x 1) 0)".to_string());
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                Some(&respelled),
            ),
            UNPROVED_STEP_RULE,
            "argument reversal may not smuggle a re-spelled operand"
        );
    }

    /// The classifier both consumers share, pinned outcome by outcome.
    ///
    /// `promoted_wire_rule` reads three distinct answers off this one call —
    /// `Divergent` withholds everything, `Identical` additionally unlocks the
    /// ground `evaluate` lowering (whose printer self-guards on byte-identical
    /// clause text), and the two reorientation variants unlock only the
    /// certificate arm — so the classifier is pinned directly rather than
    /// inferred from a wire name.
    #[test]
    fn clause_surface_agreement_separates_identity_reversal_and_divergence() {
        use crate::alethe_printer::{clause_surface_agreement, ClauseSurfaceAgreement};

        let mut terms = TermStore::new();
        let x = terms.mk_var("wire_agree_x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let lower = terms.mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
        let clause = [terms.mk_not_raw(lower)];

        assert_eq!(
            clause_surface_agreement(&terms, &clause, None),
            ClauseSurfaceAgreement::Identical,
            "no channel is no change"
        );

        let mut identity = DetHashMap::default();
        identity.insert(lower, "(<= 0 wire_agree_x)".to_string());
        assert_eq!(
            clause_surface_agreement(&terms, &clause, Some(&identity)),
            ClauseSurfaceAgreement::Identical,
            "an identity spelling is no change"
        );

        let mut reversed = DetHashMap::default();
        reversed.insert(lower, "(>= wire_agree_x 0)".to_string());
        assert_eq!(
            clause_surface_agreement(&terms, &clause, Some(&reversed)),
            ClauseSurfaceAgreement::OrderReversed,
            "the authored converse spelling is the same atom"
        );

        let equality = terms.mk_app(Symbol::named("="), [x, zero], Sort::Bool);
        let equality_clause = [terms.mk_not_raw(equality)];
        let mut symmetric = DetHashMap::default();
        symmetric.insert(equality, "(= 0 wire_agree_x)".to_string());
        assert_eq!(
            clause_surface_agreement(&terms, &equality_clause, Some(&symmetric)),
            ClauseSurfaceAgreement::EqualityReversed,
            "exact equality symmetry is distinguished for signed-row replay"
        );

        let mut divergent = DetHashMap::default();
        divergent.insert(lower, "(>= wire_agree_x 1)".to_string());
        assert_eq!(
            clause_surface_agreement(&terms, &clause, Some(&divergent)),
            ClauseSurfaceAgreement::Divergent,
            "a changed operand is a changed clause"
        );
    }
}
