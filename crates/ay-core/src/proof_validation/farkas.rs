// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic validation for arithmetic Farkas certificates.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::{One, Signed, Zero};
use thiserror::Error;

use crate::{Constant, FarkasAnnotation, Symbol, TermData, TermId, TermStore, TheoryLit};

/// Conflict-length bound for Farkas scratch vectors. Conflicts and their
/// annotations are producer-controlled, so capacity hints sized by them are
/// clamped to this (growth past the hint is normal); the one exact-length
/// allocation (`resolve_equality_coefficient_signs`'s choice vector) fails
/// closed at it instead.
const MAX_FARKAS_CONFLICT_LITERALS: usize = 1 << 16;
mod recovery;
pub use recovery::recover_single_equality_farkas;
#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[non_exhaustive]
/// Errors returned when a Farkas certificate fails structural or semantic validation.
pub enum FarkasValidationError {
    /// A caller-owned validation work, scratch-space, or cancellation envelope refused progress.
    #[error("Farkas validation resource envelope exhausted")]
    ResourceLimit,
    /// One or more coefficients were negative, violating the Farkas precondition λ >= 0.
    #[error("Farkas coefficients must be non-negative, but found: {negative:?}")]
    NegativeCoefficients {
        /// `(index, coefficient)` pairs for every negative entry.
        negative: Vec<(usize, Rational64)>,
    },

    /// The number of coefficients does not match the number of conflict literals.
    #[error("Farkas has {coefficients} coefficients but conflict has {literals} literals")]
    CoefficientCountMismatch {
        /// Number of coefficients stored in the certificate.
        coefficients: usize,
        /// Number of theory literals in the conflict being certified.
        literals: usize,
    },

    /// A conflict literal was not an arithmetic atom after stripping `not`.
    #[error("Farkas literal {term:?} is not a binary arithmetic atom")]
    NonArithmeticLiteral {
        /// Term that failed arithmetic-atom decoding.
        term: TermId,
    },

    /// The arithmetic atom used a predicate the verifier does not support.
    #[error("Farkas literal {term:?} has unsupported predicate {predicate}")]
    UnsupportedPredicate {
        /// Term that carried the unsupported predicate.
        term: TermId,
        /// Predicate name found on the arithmetic atom.
        predicate: String,
    },

    /// A disequality-style literal cannot be justified by a Farkas certificate.
    #[error(
        "Farkas certificate references disequality literal {term:?} ({predicate} asserted {value})"
    )]
    DisequalityLiteral {
        /// Term whose predicate is incompatible with Farkas validation.
        term: TermId,
        /// Predicate name found on the arithmetic atom.
        predicate: String,
        /// Boolean value asserted for the predicate.
        value: bool,
    },

    /// The weighted sum left at least one variable coefficient non-zero.
    #[error("Farkas combination does not eliminate variables: coeff({term:?}) = {coefficient}")]
    VariablesNotEliminated {
        /// One surviving variable in the weighted combination.
        term: TermId,
        /// The surviving coefficient for `term`.
        coefficient: BigRational,
    },

    /// The weighted sum reduced to a constant but did not produce contradiction.
    #[error(
        "Farkas combination does not yield contradiction: combined constant = {constant} (needs {expected})"
    )]
    NoContradiction {
        /// Combined constant after eliminating variables.
        constant: BigRational,
        /// Comparison threshold required for contradiction (`> 0` or `>= 0`).
        expected: &'static str,
    },
}

include!("farkas/linear_expr.rs");

#[derive(Debug, Clone)]
struct NormalizedConstraint {
    /// Normalized as `expr <= 0` if `strict == false`, or `expr < 0` if `strict == true`.
    expr: LinearExpr,
    strict: bool,
}

/// Verify only the structural shape of a Farkas annotation.
///
/// Checks non-negativity of all coefficients and ensures the annotation length
/// matches the number of conflict literals.
///
/// This is the LITERAL-BLIND gate: it cannot tell an inequality row (where
/// `λ >= 0` is a genuine precondition of Farkas' lemma) from an equality row
/// (where the multiplier is sign-free). Callers that hold the conflict literals
/// should use [`verify_farkas_signed_shape`] instead, which exempts equality
/// rows; this function stays strict for callers that have only the annotation.
pub fn verify_farkas_annotation_shape(
    farkas: &FarkasAnnotation,
    num_literals: usize,
) -> Result<(), FarkasValidationError> {
    if !farkas.is_valid() {
        let negative: Vec<_> = farkas
            .coefficients
            .iter()
            .enumerate()
            .filter(|(_, c)| **c < Rational64::from(0))
            .map(|(idx, coeff)| (idx, *coeff))
            .collect();
        return Err(FarkasValidationError::NegativeCoefficients { negative });
    }

    if farkas.coefficients.len() != num_literals {
        return Err(FarkasValidationError::CoefficientCountMismatch {
            coefficients: farkas.coefficients.len(),
            literals: num_literals,
        });
    }

    Ok(())
}

/// Literal-aware replacement for [`verify_farkas_annotation_shape`]'s
/// non-negativity gate.
///
/// Farkas' lemma requires `λ >= 0` **only for inequality rows**: a negative
/// multiplier there silently flips the constraint's direction, so it must stay
/// rejected. An asserted EQUALITY `e = 0` contributes `μ·e` for an arbitrary
/// real `μ`, so its multiplier is sign-free — a fact this module already relies
/// on in `equality_elimination_contradicts`, and which the orientation search
/// makes concrete: an equality literal yields the two alternatives `e` and `-e`,
/// so `{λ·e, λ·(-e)}` is the same set for `λ` and `-λ`. Rejecting a negative
/// equality coefficient therefore refuses certificates the semantic check would
/// accept, buying no soundness.
///
/// That mismatch was live: the QF_UFLRA congruence conflict
/// `x = y ∧ f(x) > 0 ∧ f(y) < 0` is refuted with a SIGNED multiplier on the
/// equality row, and the strict UNSAT funnel rejected it with
/// "Farkas coefficients must be non-negative, but found: [(2, -1)]", degrading a
/// correct refutation to `unknown`.
///
/// DISEQUALITY rows (`=` asserted false / `distinct` asserted true) stay strict.
/// They are discharged by a two-branch case split whose branches must agree on
/// coefficient magnitude, not by a signed multiplier.
///
/// # Errors
///
/// Returns [`FarkasValidationError::NegativeCoefficients`] listing every
/// negative coefficient that sits on a non-equality row.
pub fn verify_farkas_signed_shape(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> Result<(), FarkasValidationError> {
    if farkas.coefficients.len() != conflict.len() {
        // Length disagreement: defer to the literal-blind gate so a malformed
        // annotation reports exactly what it always did.
        return verify_farkas_annotation_shape(farkas, conflict.len());
    }

    let negative: Vec<_> = farkas
        .coefficients
        .iter()
        .zip(conflict.iter())
        .enumerate()
        .filter(|(_, (c, lit))| {
            **c < Rational64::from(0) && conflict_positive_equality(terms, lit).is_none()
        })
        .map(|(idx, (coeff, _))| (idx, *coeff))
        .collect();
    if !negative.is_empty() {
        return Err(FarkasValidationError::NegativeCoefficients { negative });
    }

    Ok(())
}

/// Verify that a Farkas certificate semantically proves an arithmetic conflict.
///
/// The `conflict` slice contains the signed theory literals that are jointly
/// inconsistent. The certificate is valid only if the weighted linear
/// combination eliminates all variables and yields an impossible constant
/// inequality.
///
/// Disequality literals (an `=` asserted false, or `distinct` asserted true)
/// are supported when AT MOST ONE carries a nonzero coefficient (#rank-4
/// increment 2: equality-implication certificates from the LIA affine path).
/// A conflict `E1 .. En, lhs != rhs` is refuted by case split: BOTH branches
/// `E ∧ (lhs - rhs < 0)` and `E ∧ (rhs - lhs < 0)` must admit a Farkas
/// contradiction with the same coefficient magnitudes. Requiring both
/// branches keeps the check sound: the disequality is a disjunction, so a
/// single-branch contradiction proves nothing about the conjunction.
pub fn verify_farkas_conflict_lits_full(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> Result<(), FarkasValidationError> {
    verify_farkas_conflict_lits_impl(terms, conflict, farkas, true)
}

/// Like [`verify_farkas_conflict_lits_full`], but WITHOUT the #4666
/// congruence-closure merge of opaque terms: the combination must eliminate
/// all variables purely linearly, treating every non-linearizable subterm as
/// its own opaque variable.
///
/// This is exactly the strength of the Alethe `la_generic` rule as external
/// checkers (Carcara) implement it — they perform no congruence reasoning
/// inside `la_generic`. A certificate that only contradicts modulo congruence
/// (e.g. `x = y ∧ f(x) < f(y)` with unit coefficients) is a valid THEORY
/// conflict but NOT a valid `la_generic` step; classification passes that
/// decide whether a lemma may EXPORT as `la_generic` must use this variant.
pub fn verify_farkas_conflict_lits_linear(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> Result<(), FarkasValidationError> {
    verify_farkas_conflict_lits_impl(terms, conflict, farkas, false)
}

/// [`verify_farkas_conflict_lits_full`] for callers that discard the error.
///
/// Same ACCEPT/REJECT decision, byte for byte: the only thing dropped is the
/// construction of the rejection's diagnostic payload. That payload is not
/// free — `farkas_diagnostics` re-sums the whole combination with exact
/// `BigRational` arithmetic purely to name a surviving variable or a
/// non-contradictory constant — and the producers that drive the repeated
/// subset searches (`derive_numeric_negation`'s bounded support enumeration,
/// `classifiable_core_decomposition`'s bounded core search) throw it away
/// immediately with `.is_ok()`.
pub fn verify_farkas_conflict_lits_full_holds(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> bool {
    verify_farkas_conflict_lits_holds_impl(terms, conflict, farkas, true)
}

/// [`verify_farkas_conflict_lits_linear`] for callers that discard the error.
///
/// See [`verify_farkas_conflict_lits_full_holds`] for why this exists.
pub fn verify_farkas_conflict_lits_linear_holds(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> bool {
    verify_farkas_conflict_lits_holds_impl(terms, conflict, farkas, false)
}

/// What one row of a conflict demands of an assignment.
enum RowDemand {
    /// `expr <= 0`.
    NonStrict,
    /// `expr < 0`.
    Strict,
    /// `expr = 0` — an equality literal's two non-strict orientations.
    Zero,
    /// `expr != 0` — a disequality literal, whose two strict branches are a
    /// disjunction and so hold exactly when the difference is nonzero.
    Nonzero,
}

/// The row `conflict` literal `lit` contributes, and what it demands.
///
/// Exactly the rows [`prepare_farkas_combination`] builds, so the two cannot
/// disagree about what a literal means: an equality's two orientations collapse
/// to `= 0`, a disequality's two strict branches collapse to `!= 0`, and a
/// strict integer row carries the same `+1` strengthening.
fn conflict_row_demand(terms: &TermStore, lit: &TheoryLit) -> Option<(LinearExpr, RowDemand)> {
    match normalized_constraint_alternatives(terms, lit.term, lit.value) {
        Ok(alternatives) => match alternatives.as_slice() {
            [row] => Some((
                row.expr.clone(),
                if row.strict {
                    RowDemand::Strict
                } else {
                    RowDemand::NonStrict
                },
            )),
            [row, _] => Some((row.expr.clone(), RowDemand::Zero)),
            _ => None,
        },
        Err(FarkasValidationError::DisequalityLiteral { term, .. }) => {
            disequality_difference(terms, term)
                .ok()
                .map(|expr| (expr, RowDemand::Nonzero))
        }
        Err(_) => None,
    }
}

/// `expr` evaluated at `value_of`, or `None` when any atom is unvalued.
///
/// A numeral can appear as a coefficient KEY: the congruence closure merges the
/// two sides of an asserted `(= x 0)` and may elect the numeral as the class
/// representative. Its value is itself, and no external assignment can supply
/// it.
fn evaluate_linear_expr(
    terms: &TermStore,
    expr: &LinearExpr,
    value_of: &dyn Fn(TermId) -> Option<BigRational>,
) -> Option<BigRational> {
    let mut value = expr.constant.clone();
    for (term, coefficient) in &expr.coeffs {
        let assigned = match terms.get(*term) {
            TermData::Const(Constant::Int(n)) => BigRational::from(n.clone()),
            TermData::Const(Constant::Rational(r)) => r.0.clone(),
            _ => value_of(*term)?,
        };
        value += coefficient * assigned;
    }
    Some(value)
}

/// Whether `value_of` satisfies EVERY row this verifier derives from
/// `conflict` — i.e. whether it is a MODEL of the conflict, in the verifier's
/// own abstraction.
///
/// This is the dual of [`verify_farkas_conflict_lits_full`], and it refutes an
/// entire SEARCH rather than one certificate. Every accept path there ends at
/// `is_contradiction`: the weighted sum must eliminate every variable and
/// leave a positive constant (non-negative when a strict row participates),
/// with non-negative multipliers on inequality rows and sign-free multipliers
/// on equality rows (`equality_elimination_contradicts`), and a disequality
/// literal must contradict on BOTH of its strict branches. A model satisfies
/// every such weighted sum, so none of them can be contradictory, and it
/// satisfies one branch of every disequality. Therefore a model of a literal
/// pool refutes every certificate over that pool — AND over every SUB-MULTISET
/// of it, since dropping a literal only drops a term from the combination.
/// That is what lets a producer decide a bounded-subset search in one step
/// instead of enumerating it.
///
/// The rows are the verifier's own (`conflict_row_demand`), including the
/// integer strengthening of strict rows — which is why a merely rational model
/// of the SOURCE literals is not enough and must not be substituted — and they
/// are canonicalized by the same congruence closure
/// (`build_congruence_closure`) the `full` variant merges with. That closure
/// only grows as literals are added, so a model of the merged pool rows induces
/// one for every subset's coarser rows: evaluating a subset row's atom at its
/// pool representative's value gives the same number.
///
/// Fails CLOSED: a literal the verifier cannot normalize, an unsupported
/// predicate, or an atom `value_of` cannot value all return `false`. A `false`
/// return means "no model was established", never "no model exists".
#[must_use]
pub fn conflict_lits_satisfied_by(
    terms: &TermStore,
    conflict: &[TheoryLit],
    value_of: &dyn Fn(TermId) -> Option<BigRational>,
) -> bool {
    let congruence = build_congruence_closure(terms, conflict);
    let merged = congruence.has_merges();
    for lit in conflict {
        let Some((mut expr, demand)) = conflict_row_demand(terms, lit) else {
            return false;
        };
        if merged {
            canonicalize_linear_expr(&mut expr, &congruence);
        }
        let Some(value) = evaluate_linear_expr(terms, &expr, value_of) else {
            return false;
        };
        let holds = match demand {
            RowDemand::NonStrict => value <= BigRational::zero(),
            RowDemand::Strict => value < BigRational::zero(),
            RowDemand::Zero => value.is_zero(),
            RowDemand::Nonzero => !value.is_zero(),
        };
        if !holds {
            return false;
        }
    }
    true
}

fn verify_farkas_conflict_lits_impl(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
    use_congruence: bool,
) -> Result<(), FarkasValidationError> {
    let prepared = prepare_farkas_combination(terms, conflict, farkas, use_congruence)?;
    if farkas_combination_holds(&prepared, use_congruence) {
        return Ok(());
    }
    prepared.diagnose(use_congruence)
}

/// [`verify_farkas_conflict_lits_impl`] without the rejection diagnostics.
///
/// Structurally identical: it runs the SAME `prepare` and the SAME decision,
/// so it accepts exactly the same `(conflict, certificate)` pairs. A shape
/// error and a failed combination both simply become `false`.
fn verify_farkas_conflict_lits_holds_impl(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
    use_congruence: bool,
) -> bool {
    match prepare_farkas_combination(terms, conflict, farkas, use_congruence) {
        Ok(prepared) => farkas_combination_holds(&prepared, use_congruence),
        Err(_) => false,
    }
}

/// The normalized rows of one `(conflict, certificate)` pair, ready to decide.
struct PreparedFarkas {
    alternatives: Vec<Vec<NormalizedConstraint>>,
    lambdas: Vec<BigRational>,
    disequality_index: Option<usize>,
}

impl PreparedFarkas {
    /// The rejection path: rebuild the failing combination's diagnostics.
    ///
    /// Always `Err`; the callers that only need the verdict skip it.
    fn diagnose(&self, use_congruence: bool) -> Result<(), FarkasValidationError> {
        match self.disequality_index {
            Some(diseq_idx) => {
                for branch in 0..2 {
                    let branch_alternatives = self.branch_alternatives(diseq_idx, branch);
                    if !farkas_combination_contradicts(
                        &branch_alternatives,
                        &self.lambdas,
                        use_congruence,
                    ) {
                        return farkas_diagnostics(&branch_alternatives, &self.lambdas);
                    }
                }
                // Unreachable while `diagnose` is only called after
                // `farkas_combination_holds` returned false, but stay
                // fail-closed rather than reporting success from the error arm.
                farkas_diagnostics(&self.alternatives, &self.lambdas)
            }
            None => farkas_diagnostics(&self.alternatives, &self.lambdas),
        }
    }

    fn branch_alternatives(
        &self,
        diseq_idx: usize,
        branch: usize,
    ) -> Vec<Vec<NormalizedConstraint>> {
        // The disequality row carries exactly its two strict branches by
        // construction (`prepare_farkas_combination`); destructuring keeps
        // that bound local instead of indexing on it.
        self.alternatives
            .iter()
            .enumerate()
            .map(|(idx, alts)| match alts.as_slice() {
                [first, second] if idx == diseq_idx => {
                    vec![if branch == 0 {
                        first.clone()
                    } else {
                        second.clone()
                    }]
                }
                _ => alts.clone(),
            })
            .collect()
    }
}

/// The ACCEPT decision, shared by the `Result` and the `bool` entry points.
fn farkas_combination_holds(prepared: &PreparedFarkas, use_congruence: bool) -> bool {
    match prepared.disequality_index {
        Some(diseq_idx) => {
            // Case split: each branch fixes the disequality to one strict
            // alternative; both must yield a contradiction.
            (0..2).all(|branch| {
                farkas_combination_contradicts(
                    &prepared.branch_alternatives(diseq_idx, branch),
                    &prepared.lambdas,
                    use_congruence,
                )
            })
        }
        None => farkas_combination_contradicts(
            &prepared.alternatives,
            &prepared.lambdas,
            use_congruence,
        ),
    }
}

fn prepare_farkas_combination(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
    use_congruence: bool,
) -> Result<PreparedFarkas, FarkasValidationError> {
    verify_farkas_signed_shape(terms, conflict, farkas)?;

    let lambdas: Vec<BigRational> = farkas
        .coefficients
        .iter()
        .map(rational64_to_bigrational)
        .collect();

    let mut alternatives: Vec<Vec<NormalizedConstraint>> =
        Vec::with_capacity(conflict.len().min(MAX_FARKAS_CONFLICT_LITERALS));
    let mut disequality_indices: Vec<usize> = Vec::new();
    for (idx, (lit, lambda)) in conflict.iter().zip(lambdas.iter()).enumerate() {
        if lambda.is_zero() {
            // Zero-weight literal: contributes nothing to the combination,
            // so its shape (incl. non-arithmetic context literals appended
            // by shared-reason augmentation) must not fail validation.
            alternatives.push(vec![NormalizedConstraint {
                expr: LinearExpr::zero(),
                strict: false,
            }]);
            continue;
        }
        match normalized_constraint_alternatives(terms, lit.term, lit.value) {
            Ok(alts) => alternatives.push(alts),
            Err(FarkasValidationError::DisequalityLiteral {
                term,
                predicate,
                value,
            }) => {
                if !disequality_indices.is_empty() {
                    // More than one weighted disequality: not supported.
                    return Err(FarkasValidationError::DisequalityLiteral {
                        term,
                        predicate,
                        value,
                    });
                }
                disequality_indices.push(idx);
                // `lhs - rhs != 0`: the two strict case-split branches
                // [lhs - rhs < 0, rhs - lhs < 0].
                let expr = disequality_difference(terms, term)?;
                let mut neg = expr.clone();
                neg.negate();
                alternatives.push(vec![
                    NormalizedConstraint { expr, strict: true },
                    NormalizedConstraint {
                        expr: neg,
                        strict: true,
                    },
                ]);
            }
            Err(other) => return Err(other),
        }
    }

    // #4666 manifestation B (EUF-congruence-over-nonlinear). Merge opaque terms
    // that are equal in the congruence closure of the conflict's OWN positive
    // equality literals, so congruent UF applications (e.g. the two
    // `__verification_consumer_nonlinear_mul` apps in `mul(a',b') - mul(a,b)` with `a'=a`,
    // `b'=b`) collapse to one variable and cancel under the linear combination.
    // No certificate-format change: the executor's existing coefficients are
    // reused; the verifier itself derives and CONFIRMS the congruence (it never
    // trusts an asserted UF-app equality — it requires pairwise argument
    // equality drawn from the conflict's equality literals), so it remains the
    // independent soundness gate. Substituting equal terms is model-preserving,
    // so this can only certify conflicts that are genuinely UNSAT.
    let congruence = if use_congruence {
        build_congruence_closure(terms, conflict)
    } else {
        TermUnionFind::new()
    };
    if congruence.has_merges() {
        for alts in alternatives.iter_mut() {
            for nc in alts.iter_mut() {
                canonicalize_linear_expr(&mut nc.expr, &congruence);
            }
        }
    }

    Ok(PreparedFarkas {
        alternatives,
        lambdas,
        disequality_index: disequality_indices.first().copied(),
    })
}

/// Union-find over `TermId`s used to canonicalize a Farkas conflict's linear
/// forms by the congruence closure of its equality literals (#4666 manifestation
/// B: EUF-congruence-over-nonlinear).
///
/// The linear Farkas verifier treats every non-linearizable application (e.g. a
/// `__verification_consumer_nonlinear_mul(a, b)` UF app) as an opaque variable. A conflict
/// such as `{ d <= -1, mul(a',b') - mul(a,b) <= d, a' = a, b' = b }` is UNSAT
/// only via congruence (`a'=a ∧ b'=b ⟹ mul(a',b')=mul(a,b)`), which the
/// purely-linear combination cannot derive: the two `mul` apps are distinct
/// opaque variables that never cancel. This structure rebuilds the congruence
/// closure from the conflict's OWN positive equality literals and uses it to
/// merge congruent opaque terms into one canonical representative before the
/// linear combination runs, so the two `mul` apps become one variable and
/// cancel.
struct TermUnionFind {
    parent: BTreeMap<TermId, TermId>,
}

impl TermUnionFind {
    fn new() -> Self {
        Self {
            parent: BTreeMap::new(),
        }
    }

    fn ensure(&mut self, t: TermId) {
        self.parent.entry(t).or_insert(t);
    }

    /// Non-compressing find (read-only): walks parent pointers to the root.
    fn find(&self, mut t: TermId) -> TermId {
        while let Some(&p) = self.parent.get(&t) {
            if p == t {
                break;
            }
            t = p;
        }
        t
    }

    fn union(&mut self, a: TermId, b: TermId) {
        self.ensure(a);
        self.ensure(b);
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return;
        }
        // Deterministic representative: the lower `TermId` index.
        let (keep, drop) = if ra.index() <= rb.index() {
            (ra, rb)
        } else {
            (rb, ra)
        };
        self.parent.insert(drop, keep);
    }

    /// True when at least one term was merged into a different representative.
    fn has_merges(&self) -> bool {
        self.parent.iter().any(|(k, v)| k != v)
    }
}

/// The positive equality `(a, b)` asserted by a conflict literal, if any.
///
/// Returns `Some((a, b))` only when the literal asserts `a = b` as a fact:
/// `(= a b)` held true, or `(distinct a b)` held false (both binary). Negated
/// forms are unwrapped while tracking the effective Boolean value, so e.g.
/// `(not (distinct a b))` asserted true also yields `Some((a, b))`. Disequality
/// literals (`a ≠ b`) return `None` — they must never feed congruence.
fn conflict_positive_equality(terms: &TermStore, lit: &TheoryLit) -> Option<(TermId, TermId)> {
    let mut term = lit.term;
    let mut value = lit.value;
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
        value = !value;
    }
    if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
        if let &[a, b] = args.as_slice() {
            let asserts_equality = (name == "=" && value) || (name == "distinct" && !value);
            if asserts_equality {
                return Some((a, b));
            }
        }
    }
    None
}

/// Collect every sub-term `TermId` reachable from `term` into `out`. Bounded by
/// the conflict DAG size (conflicts are small); used to find the application
/// terms that participate in congruence closure.
fn collect_subterms(terms: &TermStore, term: TermId, out: &mut BTreeSet<TermId>) {
    if !out.insert(term) {
        return;
    }
    match terms.get(term) {
        TermData::App(_, args) => {
            for &a in args {
                collect_subterms(terms, a, out);
            }
        }
        TermData::Not(inner) => collect_subterms(terms, *inner, out),
        TermData::Ite(c, t, e) => {
            collect_subterms(terms, *c, out);
            collect_subterms(terms, *t, out);
            collect_subterms(terms, *e, out);
        }
        _ => {}
    }
}

/// Whether two application terms are congruent under the current union-find:
/// identical function symbol, equal arity, and arguments pairwise equal in the
/// closure. This is the ONLY way a new equality between opaque terms is derived,
/// and it is sound precisely because each argument equality it relies on was
/// itself established from the conflict's own equality literals (never assumed).
fn terms_congruent(terms: &TermStore, a: TermId, b: TermId, uf: &TermUnionFind) -> bool {
    match (terms.get(a), terms.get(b)) {
        (TermData::App(sa, aargs), TermData::App(sb, bargs)) => {
            sa == sb
                && aargs.len() == bargs.len()
                && aargs
                    .iter()
                    .zip(bargs.iter())
                    .all(|(&x, &y)| uf.find(x) == uf.find(y))
        }
        _ => false,
    }
}

/// Build the congruence closure of a conflict's positive equality literals.
///
/// Returns a union-find that merges (a) the two sides of every asserted positive
/// equality literal, and (b) any two application terms whose arguments are
/// pairwise equal under that relation (congruence). Returns an empty (no-merge)
/// union-find when the conflict has no positive equality — without an argument
/// equality no two distinct applications can become congruent, so the closure is
/// trivial and the linear path runs exactly as before.
fn build_congruence_closure(terms: &TermStore, conflict: &[TheoryLit]) -> TermUnionFind {
    let mut uf = TermUnionFind::new();
    let mut had_equality = false;
    for lit in conflict {
        if let Some((a, b)) = conflict_positive_equality(terms, lit) {
            uf.union(a, b);
            had_equality = true;
        }
    }
    if !had_equality {
        return uf;
    }

    let mut all: BTreeSet<TermId> = BTreeSet::new();
    for lit in conflict {
        collect_subterms(terms, lit.term, &mut all);
    }
    let apps: Vec<TermId> = all
        .iter()
        .copied()
        .filter(|&t| matches!(terms.get(t), TermData::App(_, _)))
        .collect();
    // Guard against pathological blowup of the O(n^2) pairwise scan: bail to the
    // linear path on very large conflicts. Sound — bailing only makes the
    // verifier reject more (never accept more).
    if apps.len() > 4096 {
        return TermUnionFind::new();
    }
    // Fixpoint: re-scan until no further congruence merges occur (handles chains
    // like `f(g(a)) ≡ f(g(b))` once `g(a) ≡ g(b)` is established).
    loop {
        let mut changed = false;
        let mut tail = apps.as_slice();
        while let &[a, ref rest @ ..] = tail {
            for &b in rest {
                if uf.find(a) == uf.find(b) {
                    continue;
                }
                if terms_congruent(terms, a, b, &uf) {
                    uf.union(a, b);
                    changed = true;
                }
            }
            tail = rest;
        }
        if !changed {
            break;
        }
    }
    uf
}

/// Rewrite a linear form's variable keys to their congruence representatives,
/// merging coefficients of now-identical variables. Substituting equal terms is
/// model-preserving under any model of the conflict's conjunction, so it can only
/// ADD cancellation (toward `0` coefficients) and never alters a constant — hence
/// it cannot turn a satisfiable literal set into a spurious contradiction.
fn canonicalize_linear_expr(expr: &mut LinearExpr, uf: &TermUnionFind) {
    if expr.coeffs.is_empty() {
        return;
    }
    let old = std::mem::take(&mut expr.coeffs);
    for (t, c) in old {
        let rep = uf.find(t);
        let is_zero = {
            let entry = expr.coeffs.entry(rep).or_insert_with(BigRational::zero);
            *entry += c;
            entry.is_zero()
        };
        if is_zero {
            expr.coeffs.remove(&rep);
        }
    }
}

/// The linear difference `lhs - rhs` of a (possibly negated) binary `=` or
/// `distinct` atom.
fn disequality_difference(
    terms: &TermStore,
    mut term: TermId,
) -> Result<LinearExpr, FarkasValidationError> {
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
    }
    let (lhs, rhs) = match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" || name == "distinct" => {
            match args.as_slice() {
                &[lhs, rhs] => (lhs, rhs),
                _ => return Err(FarkasValidationError::NonArithmeticLiteral { term }),
            }
        }
        _ => return Err(FarkasValidationError::NonArithmeticLiteral { term }),
    };
    let mut expr = parse_linear_expr(terms, lhs);
    let rhs_expr = parse_linear_expr(terms, rhs);
    expr.add_scaled(&rhs_expr, &BigRational::from(BigInt::from(-1)));
    Ok(expr)
}

/// Search strategy shared by the plain and case-split validation paths:
/// full search for small alternative spaces, first-alternative plus
/// single-flip fast paths beyond the cap (#W16-5).
fn farkas_combination_contradicts(
    alternatives: &[Vec<NormalizedConstraint>],
    lambdas: &[BigRational],
    sign_free_equalities: bool,
) -> bool {
    // Compute total search space: product of alternative counts per literal.
    // Equality literals produce 2 alternatives each; the search function
    // explores all combinations, giving O(2^n) for n equalities.  Cap the
    // search to avoid exponential blowup in conflicts with many equalities
    // (#W16-5: was the dominant cost — 42% of solver time on QF_LRA benchmarks).
    let search_space: u64 = alternatives
        .iter()
        .map(|a| a.len() as u64)
        .try_fold(1u64, u64::checked_mul)
        .unwrap_or(u64::MAX);

    // Both paths below consume the SAME plan: every `λ·e` product is computed
    // once here rather than once per combination, and the single-orientation
    // literals are summed once into `plan.base` (#8404 perf — see `ScaledPlan`).
    //
    // The subtree-prune bounds (`ScaledPlan::remaining`) are read ONLY by the
    // exhaustive `search_plan` walk; the capped fast path below never consults
    // them, so build them only when the walk that reads them will run (see
    // `build_scaled_plan`). Verdict-neutral in both directions.
    let exhaustive = search_space <= 1024;
    let plan = build_scaled_plan(alternatives, lambdas, exhaustive);

    if exhaustive {
        let mut acc = plan.base.clone();
        if search_plan(&plan, 0, &mut acc, plan.base_strict, &mut None) {
            return true;
        }
    } else {
        // Too many combinations — try only the first alternative for each
        // literal (fast path).  If that succeeds, accept the certificate.
        // Every branch carries one scaled row and strict flag per candidate,
        // at least two of each by construction (`build_scaled_plan` folds
        // single-candidate positions into `base`); destructuring keeps that
        // bound local instead of indexing on it.
        let mut sum = plan.base.clone();
        let mut strict = plan.base_strict;
        for branch in &plan.branches {
            if let ([first, ..], [first_strict, ..]) =
                (branch.scaled.as_slice(), branch.strict.as_slice())
            {
                sum.add_expr(first);
                strict = strict || *first_strict;
            }
        }
        if is_contradiction(&sum, strict) {
            return true;
        }
        // Try the second alternative for each equality literal one at a time.
        // `sum` already holds the all-first combination, so each variant is one
        // row swapped out and one swapped in — not a rebuild from scratch.
        for (flipped, branch) in plan.branches.iter().enumerate() {
            let [first, second, ..] = branch.scaled.as_slice() else {
                continue;
            };
            sum.sub_expr(first);
            sum.add_expr(second);
            let strict2 = plan.base_strict
                || plan
                    .branches
                    .iter()
                    .enumerate()
                    .any(|(i, b)| match b.strict.as_slice() {
                        [s0, s1, ..] => {
                            if i == flipped {
                                *s1
                            } else {
                                *s0
                            }
                        }
                        [s0] => *s0,
                        [] => false,
                    });
            let hit = is_contradiction(&sum, strict2);
            sum.sub_expr(second);
            sum.add_expr(first);
            if hit {
                return true;
            }
        }
    }
    // #4666 manifestation C (long equality chains): the orientation search
    // above is capped/incomplete, so a valid certificate whose contradicting
    // combination needs many equality sign flips (e.g. a 12-literal telescoping
    // equality chain on QF_ALIA pointer benchmarks — 2^12 orientations) is
    // missed. Equality multipliers in Farkas' lemma are sign-free, so no
    // enumeration is needed at all: Gaussian-eliminate the fixed-λ inequality
    // combination against the linear span of the equality expressions. This is
    // strictly a COMPLETENESS fix — every accepted combination is still a
    // genuine Farkas contradiction (non-negative multipliers on inequalities,
    // arbitrary real multipliers on equalities), so the gate stays sound. It
    // applies ONLY to the runtime `full` variant: the strict `linear` variant
    // classifies Alethe `la_generic` exportability, where the printed
    // coefficient magnitudes are load-bearing (Carcara forms the exact
    // combination), so hint-magnitude-insensitive acceptance is wrong there.
    sign_free_equalities && equality_elimination_contradicts(alternatives, lambdas)
}

/// Complete check for conflicts mixing inequalities with equality literals.
///
/// Builds `base = Σ λᵢ·eᵢ` over the single-orientation (inequality) literals
/// only, then reduces `base` modulo the row space of the equality expressions
/// (Gauss–Jordan, exact rationals). Any linear combination `base + Σ μⱼ·qⱼ`
/// with arbitrary real `μⱼ` is a valid Farkas combination because each `qⱼ`
/// comes from an asserted equality `qⱼ = 0`. Returns `true` when either
/// (a) some combination of the equalities alone reduces to `0 = c` with
/// `c ≠ 0`, or (b) the fully reduced `base` is a contradictory constant
/// (`> 0`, or `>= 0` when a strict inequality participates).
fn equality_elimination_contradicts(
    alternatives: &[Vec<NormalizedConstraint>],
    lambdas: &[BigRational],
) -> bool {
    let mut base = LinearExpr::zero();
    let mut strict = false;
    let mut equalities: Vec<LinearExpr> = Vec::new();
    for (alts, lambda) in alternatives.iter().zip(lambdas.iter()) {
        if lambda.is_zero() {
            continue;
        }
        // `split_first` instead of slice patterns: the arity discrimination
        // stays total without the index projections whose bounds the L0
        // prover loses.
        match alts.split_first() {
            Some((first, rest)) if !rest.is_empty() => {
                // Equality literal (two non-strict orientations): sign-free
                // multiplier, so only the expression's span matters.
                equalities.push(first.expr.clone());
            }
            Some((only, _)) => {
                base.add_scaled(&only.expr, lambda);
                strict = strict || only.strict;
            }
            None => {}
        }
    }

    // Gauss–Jordan over the equality rows. Invariant: every pivot row is fully
    // reduced against every other pivot (contains no other pivot's variable).
    let mut pivots: Vec<(TermId, LinearExpr)> = Vec::new();
    for mut row in equalities {
        for (v, p) in &pivots {
            if let (Some(c), Some(pivot_coeff)) = (row.coeffs.get(v).cloned(), p.coeffs.get(v)) {
                let factor = -c / pivot_coeff;
                row.add_scaled(p, &factor);
            }
        }
        if let Some((&v, head_coeff)) = row.coeffs.iter().next() {
            let head_coeff = head_coeff.clone();
            for (_, p) in pivots.iter_mut() {
                if let Some(c) = p.coeffs.get(&v).cloned() {
                    let factor = -c / &head_coeff;
                    p.add_scaled(&row, &factor);
                }
            }
            pivots.push((v, row));
        } else if !row.constant.is_zero() {
            // The equalities alone combine to `0 = c` with `c != 0`.
            return true;
        }
    }

    for (v, p) in &pivots {
        if let (Some(c), Some(pivot_coeff)) = (base.coeffs.get(v).cloned(), p.coeffs.get(v)) {
            let factor = -c / pivot_coeff;
            base.add_scaled(p, &factor);
        }
    }
    is_contradiction(&base, strict)
}

/// Error diagnostics for a failed combination, using the first alternative
/// of every literal.
fn farkas_diagnostics(
    alternatives: &[Vec<NormalizedConstraint>],
    lambdas: &[BigRational],
) -> Result<(), FarkasValidationError> {
    let mut sum = LinearExpr::zero();
    let mut strict = false;
    for (alts, lambda) in alternatives.iter().zip(lambdas.iter()) {
        let Some(alt) = alts.first() else {
            continue;
        };
        sum.add_scaled(&alt.expr, lambda);
        strict = strict || (!lambda.is_zero() && alt.strict);
    }

    if let Some((term, coefficient)) = sum.coeffs.iter().find(|(_, coeff)| !coeff.is_zero()) {
        return Err(FarkasValidationError::VariablesNotEliminated {
            term: *term,
            coefficient: coefficient.clone(),
        });
    }

    Err(FarkasValidationError::NoContradiction {
        constant: sum.constant,
        expected: if strict { ">= 0" } else { "> 0" },
    })
}

fn rational64_to_bigrational(r: &Rational64) -> BigRational {
    BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom()))
}

pub(crate) fn parse_linear_expr(terms: &TermStore, term: TermId) -> LinearExpr {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => LinearExpr::constant(BigRational::from(n.clone())),
        TermData::Const(Constant::Rational(r)) => LinearExpr::constant(r.0.clone()),
        TermData::Var(_, _) => LinearExpr::var(term),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                let mut result = LinearExpr::zero();
                for &arg in args {
                    let sub = parse_linear_expr(terms, arg);
                    result.add_scaled(&sub, &BigRational::one());
                }
                result
            }
            "-" => match args.as_slice() {
                &[only] => {
                    let mut result = parse_linear_expr(terms, only);
                    result.negate();
                    result
                }
                [first, rest @ ..] => {
                    let mut result = parse_linear_expr(terms, *first);
                    for &arg in rest {
                        let mut sub = parse_linear_expr(terms, arg);
                        sub.negate();
                        result.add_scaled(&sub, &BigRational::one());
                    }
                    result
                }
                [] => LinearExpr::var(term),
            },
            "*" => {
                let mut const_part = BigRational::one();
                let mut non_const: Option<LinearExpr> = None;

                for &arg in args {
                    let sub = parse_linear_expr(terms, arg);
                    if sub.is_constant() {
                        const_part *= sub.constant;
                    } else if non_const.is_none() {
                        non_const = Some(sub);
                    } else {
                        return LinearExpr::var(term);
                    }
                }

                match non_const {
                    Some(mut expr) => {
                        expr.scale(&const_part);
                        expr
                    }
                    None => LinearExpr::constant(const_part),
                }
            }
            "/" => match args.as_slice() {
                &[num, den] => {
                    let mut numerator = parse_linear_expr(terms, num);
                    let denominator = parse_linear_expr(terms, den);
                    if denominator.is_constant() && !denominator.constant.is_zero() {
                        let inv = BigRational::one() / denominator.constant;
                        numerator.scale(&inv);
                        numerator
                    } else {
                        LinearExpr::var(term)
                    }
                }
                _ => LinearExpr::var(term),
            },
            _ => LinearExpr::var(term),
        },
        TermData::App(_, _) => LinearExpr::var(term),
        _ => LinearExpr::var(term),
    }
}

fn normalized_constraint_alternatives(
    terms: &TermStore,
    mut term: TermId,
    mut value: bool,
) -> Result<Vec<NormalizedConstraint>, FarkasValidationError> {
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
        value = !value;
    }

    let (pred, lhs, rhs) = match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => match args.as_slice() {
            &[lhs, rhs] => (name.as_str(), lhs, rhs),
            _ => return Err(FarkasValidationError::NonArithmeticLiteral { term }),
        },
        _ => return Err(FarkasValidationError::NonArithmeticLiteral { term }),
    };

    let (mut base_expr, base_strict, is_equality_like) = match pred {
        "<" => {
            let mut expr = parse_linear_expr(terms, lhs);
            let rhs_expr = parse_linear_expr(terms, rhs);
            expr.add_scaled(&rhs_expr, &BigRational::from(BigInt::from(-1)));
            (expr, true, false)
        }
        "<=" => {
            let mut expr = parse_linear_expr(terms, lhs);
            let rhs_expr = parse_linear_expr(terms, rhs);
            expr.add_scaled(&rhs_expr, &BigRational::from(BigInt::from(-1)));
            (expr, false, false)
        }
        ">" => {
            let mut expr = parse_linear_expr(terms, rhs);
            let lhs_expr = parse_linear_expr(terms, lhs);
            expr.add_scaled(&lhs_expr, &BigRational::from(BigInt::from(-1)));
            (expr, true, false)
        }
        ">=" => {
            let mut expr = parse_linear_expr(terms, rhs);
            let lhs_expr = parse_linear_expr(terms, lhs);
            expr.add_scaled(&lhs_expr, &BigRational::from(BigInt::from(-1)));
            (expr, false, false)
        }
        "=" | "distinct" => {
            let mut expr = parse_linear_expr(terms, lhs);
            let rhs_expr = parse_linear_expr(terms, rhs);
            expr.add_scaled(&rhs_expr, &BigRational::from(BigInt::from(-1)));
            (expr, false, true)
        }
        _ => {
            return Err(FarkasValidationError::UnsupportedPredicate {
                term,
                predicate: pred.to_string(),
            });
        }
    };

    if is_equality_like {
        let equality_holds = (pred == "=" && value) || (pred == "distinct" && !value);
        if !equality_holds {
            return Err(FarkasValidationError::DisequalityLiteral {
                term,
                predicate: pred.to_string(),
                value,
            });
        }

        let mut neg = base_expr.clone();
        neg.negate();
        return Ok(vec![
            NormalizedConstraint {
                expr: base_expr,
                strict: false,
            },
            NormalizedConstraint {
                expr: neg,
                strict: false,
            },
        ]);
    }

    if !value {
        base_expr.negate();
    }
    let mut strict = if value { base_strict } else { !base_strict };

    // Integer strengthening (#4666). A strict inequality `e < 0` over an
    // INTEGER-valued linear form `e` is equivalent to `e <= -1`, i.e.
    // `e + 1 <= 0`. Applying this per-strict-literal lets the real-Farkas
    // combination certify conflicts that are UNSAT only over the integers and
    // have NO real refutation — e.g. `j < k ∧ k < j+1` (real-SAT at
    // `j=0, k=0.5`, but integer-UNSAT). The LRA/LIA solver finds these via
    // simplex strict-bound strengthening and emits a plain Farkas annotation;
    // without this rule the real-only combination yields a non-positive
    // constant (here `-1`) and the certificate is rejected.
    //
    // SOUNDNESS (cannot cause a false-accept): the rewrite `e < 0 ⟹ e+1 <= 0`
    // is a logical CONSEQUENCE whenever `e` is integer-valued, so any
    // contradiction derived from the strengthened constraints implies the
    // original conflict is UNSAT; and every integer model of the original
    // strict inequality also satisfies the strengthened one, so a satisfiable
    // set stays satisfiable — no spurious contradiction can arise. The
    // `e`-is-integer-valued gate is the same fail-closed test used by the LIA
    // bound checker (`proof_validation::lia::int_linear_diff`): EVERY variable
    // term must be `Int`-sorted (a `Real` makes `e` rationally valued and the
    // rounding INVALID) and every coefficient and the constant must be
    // integers. Mirrors `parse_int_bound`'s `<` ⟼ `-c0 - 1` rounding.
    if strict && expr_is_integer_valued(terms, &base_expr) {
        base_expr.constant += BigRational::one();
        strict = false;
    }

    Ok(vec![NormalizedConstraint {
        expr: base_expr,
        strict,
    }])
}

/// Whether `expr` is provably integer-valued: every variable term is
/// `Int`-sorted and every coefficient and the constant is an integer. Used to
/// gate the sound integer strengthening of strict inequalities (#4666). Fails
/// closed (returns `false`) on any `Real`/non-`Int` variable or non-integer
/// coefficient — exactly the guard in `proof_validation::lia::int_linear_diff`,
/// so the two integer-reasoning paths cannot drift.
fn expr_is_integer_valued(terms: &TermStore, expr: &LinearExpr) -> bool {
    use crate::Sort;
    if !expr.constant.is_integer() {
        return false;
    }
    for (term, coeff) in &expr.coeffs {
        if !coeff.is_integer() {
            return false;
        }
        if !matches!(terms.sort(*term), Sort::Int) {
            return false;
        }
    }
    true
}

fn is_contradiction(sum: &LinearExpr, strict: bool) -> bool {
    if !sum.coeffs.is_empty() {
        return false;
    }
    if strict {
        sum.constant >= BigRational::zero()
    } else {
        sum.constant > BigRational::zero()
    }
}

include!("farkas/scaled_search.rs");

/// Resolve the SIGNED Alethe `la_generic` coefficients for a Farkas
/// certificate over a conflict that may contain equality literals.
///
/// The internal certificate format keeps all coefficients non-negative and
/// lets the validator search both orientations of each equality literal
/// (`lhs - rhs <= 0` vs `rhs - lhs <= 0`). Alethe's `la_generic` has no such
/// search: the printed coefficient of an equality literal is signed, and the
/// checker (e.g. Carcara) forms the single linear combination the args
/// dictate. Printing the unsigned internal coefficients verbatim therefore
/// yields args Carcara rejects whenever the contradicting combination uses an
/// equality in the `rhs - lhs` direction.
///
/// This function re-runs the exact validation search and returns the
/// coefficient vector with each equality's coefficient NEGATED when the
/// contradicting combination used its second (negated) orientation. It
/// returns `None` — caller keeps the original coefficients — when the
/// conflict contains a literal the linear model cannot orient (disequality
/// or non-arithmetic literal), when the alternative space exceeds the same
/// 1024-combination cap the validator uses, or when no combination
/// contradicts (an invalid certificate is never re-signed into a "fixed"
/// one). Inequality orientations are unique, so their coefficients are
/// returned unchanged; a certificate without equality literals is returned
/// bit-identically.
#[must_use]
pub fn resolve_equality_coefficient_signs(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> Option<Vec<Rational64>> {
    if farkas.coefficients.len() != conflict.len() {
        return None;
    }
    if !farkas.is_valid() {
        return None;
    }

    let lambdas: Vec<BigRational> = farkas
        .coefficients
        .iter()
        .map(rational64_to_bigrational)
        .collect();

    let mut alternatives: Vec<Vec<NormalizedConstraint>> =
        Vec::with_capacity(conflict.len().min(MAX_FARKAS_CONFLICT_LITERALS));
    for (lit, lambda) in conflict.iter().zip(lambdas.iter()) {
        if lambda.is_zero() {
            alternatives.push(vec![NormalizedConstraint {
                expr: LinearExpr::zero(),
                strict: false,
            }]);
            continue;
        }
        match normalized_constraint_alternatives(terms, lit.term, lit.value) {
            Ok(alts) => alternatives.push(alts),
            // Disequalities need a case split (both branches), which a single
            // signed combination cannot express; opaque/non-arithmetic
            // literals cannot be oriented. Fail closed: keep original args.
            Err(_) => return None,
        }
    }

    let search_space: u64 = alternatives
        .iter()
        .map(|a| a.len() as u64)
        .try_fold(1u64, u64::checked_mul)
        .unwrap_or(u64::MAX);
    if search_space > 1024 {
        return None;
    }

    // Exact-length allocation, not a capacity hint: an oversized conflict
    // cannot be absorbed by growth, so it fails closed like every other
    // unsupported shape here.
    if alternatives.len() > MAX_FARKAS_CONFLICT_LITERALS {
        return None;
    }
    let mut choice = vec![0usize; alternatives.len()];
    if !search_recording_choice(&alternatives, &lambdas, &mut choice) {
        return None;
    }

    // Sign mapping. The internal combination is `Σ λᵢ·eᵢ` with every
    // constraint normalized to `eᵢ ≤ 0` (`e = rhs - lhs` for `>=`, etc.), and
    // the equality alternatives are `alt0 = (lhs - rhs) ≤ 0`,
    // `alt1 = (rhs - lhs) ≤ 0`. An Alethe `la_generic` checker forms the
    // MIRROR combination: inequalities are oriented as `... ≥ 0` (the exact
    // negation of the internal `≤ 0` forms), while an equality's signed
    // coefficient `d` contributes `d·(lhs - rhs)` directly. Matching the two
    // sums termwise gives `d = -s·λ`, where `s = +1` for alt0 and `-1` for
    // alt1 — so alt0 prints `-λ` and alt1 prints `+λ`. Inequality
    // coefficients (a single alternative) are printed unchanged (positive).
    Some(
        farkas
            .coefficients
            .iter()
            .zip(choice.iter().zip(alternatives.iter()))
            .map(|(c, (&alt_idx, alts))| {
                if alts.len() < 2 {
                    *c
                } else if alt_idx == 0 {
                    -*c
                } else {
                    *c
                }
            })
            .collect(),
    )
}
