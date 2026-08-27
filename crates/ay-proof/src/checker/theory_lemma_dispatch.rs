// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

struct TheoryLemmaValidation<'a, 'p> {
    terms: &'a TermStore,
    step_id: ProofId,
    clause: &'a [TermId],
    farkas: Option<&'a FarkasAnnotation>,
    lia_ann: Option<&'a LiaAnnotation>,
    dt_decls: Option<datatype_axiom::DatatypeDecls<'a>>,
    ctor_selectors: Option<datatype_axiom::SelectorDecls<'a>>,
    datatype_member_signatures: Option<&'a [DatatypeMemberSignature]>,
    ext_diff: Option<&'a ExtDiffRegistry>,
    empty_sets: Option<&'a EmptySetRegistry>,
    progress: &'p mut dyn FnMut(usize, usize) -> bool,
}

fn validate_theory_core(
    context: &mut TheoryLemmaValidation<'_, '_>,
    kind: TheoryLemmaKind,
) -> Result<bool, ProofCheckError> {
    let terms = context.terms;
    let step_id = context.step_id;
    let clause = context.clause;
    let farkas = context.farkas;
    let lia_ann = context.lia_ann;
    let progress = &mut *context.progress;
    match kind {
        TheoryLemmaKind::EufTransitive => validate_euf_transitive(terms, step_id, clause)?,
        // Reflexivity is checked by the same routine that backs the
        // `eq_reflexive` Alethe rule: exactly one literal, a binary
        // equality, and both sides the SAME term. Nothing about the
        // conflict that produced it is taken on trust.
        TheoryLemmaKind::EufReflexive => {
            boolean_derived::validate_eq_reflexive(terms, step_id, clause)?;
        }
        TheoryLemmaKind::EufCongruent => validate_euf_congruent(terms, step_id, clause)?,
        TheoryLemmaKind::EufCongruentPred => {
            validate_euf_congruent_pred(terms, step_id, clause)?;
        }
        // A congruence-closure EXPLANATION: the hypotheses need not form a
        // syntactic path, and the conclusion may sit anywhere in the clause.
        // The validator re-runs the closure itself; the producer's tag names
        // the rule and carries no authority.
        TheoryLemmaKind::EufCongruenceExplanation => {
            validate_euf_congruence_explanation_schemas(terms, step_id, clause, progress)?;
        }
        TheoryLemmaKind::LraFarkas => {
            lra_farkas::validate_metered(terms, step_id, clause, farkas, progress)?;
        }
        TheoryLemmaKind::LiaGeneric => {
            lia::validate_metered(terms, step_id, clause, farkas, lia_ann, progress)?;
        }
        TheoryLemmaKind::LiaModRange => {
            ay_core::proof_validation::validate_lia_mod_range(terms, clause).map_err(|e| {
                ProofCheckError::InvalidTheoryLemma {
                    step: step_id,
                    reason: e.to_string(),
                }
            })?;
        }
        TheoryLemmaKind::QuantifierNegatedExistsDual => qdual(terms, step_id, clause)?,
        TheoryLemmaKind::BvLiaTautology => {
            bv_lia_query::validate_bv_lia_tautology(
                terms,
                step_id,
                clause,
                farkas.is_some(),
                lia_ann.is_some(),
            )?;
        }
        TheoryLemmaKind::SeqExtensionalCompanionContradiction => {
            seq_extensional_companion::validate(terms, step_id, clause)?;
        }
        // Bounded bit-blast validation (#8820) requires Boolean literals, BV
        // content, and each gate's declared operator. Unsupported or too-wide
        // clauses fail closed pending full proof-bitblaster coverage (#8071).
        TheoryLemmaKind::BvBitBlast => {
            bv_bitblast::validate_bv_bitblast(terms, step_id, clause, None)?;
        }
        // Boolean tautology: a propositional clause true under every bounded
        // assignment (e.g. `(= (not (not p)) p)`). Validated by the same
        // exhaustive bounded evaluator, without the bit-blast BV-content gate.
        TheoryLemmaKind::BoolTautology => {
            bv_bitblast::validate_bool_tautology(terms, step_id, clause)?;
        }
        TheoryLemmaKind::ArithEqTriangle => {
            lia::validate_arith_eq_triangle(terms, step_id, clause)?;
        }
        TheoryLemmaKind::ArithEqImpliesBound => {
            lia::validate_arith_eq_implies_bound(terms, step_id, clause)?;
        }
        TheoryLemmaKind::IntBoundsTautology => {
            lia::validate_int_bounds_tautology(terms, step_id, clause)?;
        }
        // Core re-derived from the clause; no producer payload exists.
        TheoryLemmaKind::IntBoundLatticeGap => {
            lia::validate_int_bound_lattice_gap(terms, step_id, clause)?;
        }
        // Multipliers AND core re-derived from the clause; no payload.
        TheoryLemmaKind::IntCutLatticeGap => {
            lia::validate_int_cut_lattice_gap(terms, step_id, clause)?;
        }
        // Case split AND per-branch certificates re-derived from the clause;
        // no payload.
        TheoryLemmaKind::IntGuardedSplitGap => {
            lia::validate_int_guarded_split_gap(terms, step_id, clause)?;
        }
        TheoryLemmaKind::ArithDisequalitySplit => {
            lia::validate_arith_disequality_split(terms, step_id, clause)?;
        }
        // If-then-else with identical branches: `(= (ite c x x) x)` — a
        // syntactic axiom valid for any condition and any sort of x.
        TheoryLemmaKind::IteSame => {
            ite_axiom::validate_ite_same(terms, step_id, clause)?;
        }
        _ => return Ok(false),
    }
    Ok(true)
}

fn validate_theory_numeric_and_fp(
    context: &mut TheoryLemmaValidation<'_, '_>,
    kind: TheoryLemmaKind,
) -> Result<bool, ProofCheckError> {
    let terms = context.terms;
    let step_id = context.step_id;
    let clause = context.clause;
    let progress = &mut *context.progress;
    match kind {
        TheoryLemmaKind::OrderIteTautology => {
            order_ite::validate_order_ite_tautology(terms, step_id, clause)?;
        }
        TheoryLemmaKind::FpClassification { .. } => {
            fp_bounded::validate_fp_classification(terms, step_id, clause)?;
        }
        TheoryLemmaKind::FpRoundingModeDomain => {
            fp_bounded::validate_fp_rounding_mode_domain(terms, step_id, clause)?;
        }
        // Exact IEEE-754 evaluation (`fp_ground`): the clause is TRUE under
        // every assignment of whatever variables survive its own ground
        // bindings, decided by an INDEPENDENT correctly-rounded
        // integer/rational kernel — not by `f64`, and not by the solver's
        // evaluator. This is a full semantic validation rather than a
        // schema check; unsupported operators, unbounded variable domains
        // and budget exhaustion all fail closed.
        TheoryLemmaKind::FpGroundEval => {
            fp_ground::validate_fp_ground_eval(terms, step_id, clause)?;
        }
        TheoryLemmaKind::RoundingModeDomain => {
            rounding_mode::validate_rounding_mode_domain(terms, step_id, clause)?;
        }
        // FP forward-error lemma: the clause is the disjunction of the
        // NEGATED premises of a rounding-error refutation. The validator
        // independently re-derives the whole analysis from the clause —
        // fact mining, RNE/no-overflow side conditions, exact-rational
        // half-ulp enclosure propagation, mirror-polynomial identity, and
        // the strict claim contradiction — failing closed on anything
        // unrecognized.
        TheoryLemmaKind::FpForwardError => {
            fp_forward_error::validate_fp_forward_error(terms, step_id, clause)?;
        }
        TheoryLemmaKind::BvBitBlastGate { gate_type, width } => {
            bv_bitblast::validate_bv_bitblast(terms, step_id, clause, Some((gate_type, width)))?;
        }
        // Array theory lemmas: semantic ROW validation (#8820).
        //
        // Enforces that read-over-write clauses mention
        // `(select (store ...) ...)` and that the negative case carries a
        // disequality between the indices. Extensionality clauses are
        // handled separately below: their soundness is provenance, not
        // shape, so they need the `ext_diff` registry.
        TheoryLemmaKind::ArraySelectStore { index_eq } => {
            array_axiom::validate_array_select_store(terms, step_id, clause, index_eq)?;
        }
        // n-ary store-commutativity and chain read-over-write: exact
        // schemas with fully-checked side conditions (see array_axiom.rs).
        TheoryLemmaKind::ArrayStorePermutation => {
            array_axiom::validate_array_store_permutation(terms, step_id, clause, progress)?;
        }
        TheoryLemmaKind::ArrayRowChain => {
            array_axiom::validate_array_row_chain(terms, step_id, clause, progress)?;
        }
        TheoryLemmaKind::ArrayDefaultConst => {
            array_axiom::validate_array_default_const(terms, step_id, clause)?;
        }
        _ => return Ok(false),
    }
    Ok(true)
}

fn validate_theory_sets(
    context: &mut TheoryLemmaValidation<'_, '_>,
    kind: TheoryLemmaKind,
) -> Result<bool, ProofCheckError> {
    let terms = context.terms;
    let step_id = context.step_id;
    let clause = context.clause;
    let empty_sets = context.empty_sets;
    match kind {
        TheoryLemmaKind::SetCardNonNegative => {
            set_axiom::validate_set_card_non_negative(terms, step_id, clause)?;
        }
        TheoryLemmaKind::SetCardMemberLowerBound => {
            set_axiom::validate_set_card_member_lower_bound(terms, step_id, clause)?;
        }
        TheoryLemmaKind::SetCardEmpty => {
            set_axiom::validate_set_card_empty(terms, step_id, clause)?;
        }
        TheoryLemmaKind::SetCardMemberCount => {
            set_axiom::validate_set_card_member_count(terms, step_id, clause)?;
        }
        TheoryLemmaKind::SetCardEmptyByAssertion => {
            set_axiom::validate_set_card_empty_by_assertion(terms, step_id, clause, empty_sets)?;
        }
        // Definitional set-cardinality recurrence over an EMPTY-ROOTED
        // store chain. The empty root confines the schema to the finite
        // fragment and is established by a walk of its own -- the
        // membership walk short-circuits at the probed index and can
        // answer without ever seeing the root. See set_card_chain.rs.
        TheoryLemmaKind::SetCardChainRecurrence => {
            set_card_chain::validate_set_card_chain_recurrence(terms, step_id, clause)?;
        }
        // Collection subset schemas: universally valid, re-derived from
        // the clause alone (exact operand identity, native array
        // signature, carrier element sort). See subset_axiom.rs.
        TheoryLemmaKind::SubsetReflexive => {
            subset_axiom::validate_subset_reflexive(terms, step_id, clause)?;
        }
        TheoryLemmaKind::SubsetElementInstance => {
            subset_axiom::validate_subset_element_instance(terms, step_id, clause)?;
        }
        // Transitivity of one collection subset predicate: the chain is
        // re-derived from the clause, so a triple that does not connect is
        // refused. See subset_axiom.rs.
        TheoryLemmaKind::SubsetTransitive => {
            subset_axiom::validate_subset_transitive(terms, step_id, clause)?;
        }
        // One subset atom DECIDED EXACTLY on ground carriers, under the
        // clause's own ground bindings. This is a full semantic decision
        // rather than a schema check: an unrecognized carrier, an unbound
        // operand the decision needs, or a polarity the pointwise decision
        // contradicts all fail closed. See subset_axiom.rs.
        TheoryLemmaKind::SubsetGroundEval => {
            subset_axiom::validate_subset_ground_eval(terms, step_id, clause)?;
        }
        // Skolemized extensionality: NOT a tautology, so shape alone can
        // never license it. Accepted only against the whole-proof
        // `array_ext_diff_intro` provenance registry; `None` (the caller
        // had no problem assertion set to check freshness against) fails
        // closed exactly as this kind always did.
        _ => return Ok(false),
    }
    Ok(true)
}

fn validate_theory_arrays_and_strings(
    context: &mut TheoryLemmaValidation<'_, '_>,
    kind: TheoryLemmaKind,
) -> Result<bool, ProofCheckError> {
    let terms = context.terms;
    let step_id = context.step_id;
    let clause = context.clause;
    let ext_diff = context.ext_diff;
    let dt_decls = context.dt_decls;
    let ctor_selectors = context.ctor_selectors;
    let datatype_member_signatures = context.datatype_member_signatures;
    match kind {
        TheoryLemmaKind::ArrayExtensionality => {
            array_axiom::validate_array_extensionality(terms, step_id, clause, ext_diff)?;
        }
        // Complete finite-carrier array schemas. Unlike Skolemized
        // extensionality, these are theory tautologies and need no witness
        // provenance: the checker independently enumerates the entire
        // carrier from Bool/BV sorts or authenticated nullary constructors.
        TheoryLemmaKind::ArrayFiniteExtensionality => {
            array_finite::validate_array_finite_extensionality(
                terms,
                step_id,
                clause,
                dt_decls,
                ctor_selectors,
                datatype_member_signatures,
            )?;
        }
        TheoryLemmaKind::ArrayFiniteSelectExpansion => {
            array_finite::validate_array_finite_select_expansion(
                terms,
                step_id,
                clause,
                dt_decls,
                ctor_selectors,
                datatype_member_signatures,
            )?;
        }
        // FP→BV lemmas: fail-closed until semantic lowering exists (#8820).
        //
        // Enforces the cheap schema checks first, then rejects because
        // strict IEEE 754 re-verification against the BV circuit is #8075.
        TheoryLemmaKind::FpToBv { operation } => {
            fp_to_bv::validate_fp_to_bv(terms, step_id, clause, operation)?;
        }
        // String theory lemmas: fail-closed semantic validation (#8820).
        //
        // Length lemmas pass only when statically proven true. Content and
        // normal-form lemmas reject until full semantic validation exists
        // (#8074).
        TheoryLemmaKind::StringLengthAxiom => {
            string_axiom::validate_string_length_axiom(terms, step_id, clause)?;
        }
        // Universally-valid str.len theorem over symbolic subjects
        // (#selfcert-strlen): the clause carries a certified length identity
        // (concat-length sum, empty↔zero-length, non-negativity,
        // constant-length, equal-length congruence, or containment bound).
        // The INDEPENDENT structural checker re-derives the exact algebraic
        // identity and fails closed on any near-miss, so the injected length
        // axioms can carry a checkable rule instead of a bare foreign assume.
        TheoryLemmaKind::StringLengthLemma => {
            string_length_identity::validate_string_length_lemma(terms, step_id, clause)?;
        }
        TheoryLemmaKind::StringContentAxiom => {
            string_axiom::validate_string_content_axiom(terms, step_id, clause)?;
        }
        TheoryLemmaKind::StringNormalForm => {
            string_axiom::validate_string_normal_form(terms, step_id, clause)?;
        }
        // Ground string/regex evaluation (#8074 ground fragment): the
        // clause carries a literal whose leaves are all constants and
        // which the INDEPENDENT ground evaluator proves TRUE. A clause
        // with a true literal is a tautology, so this is a full semantic
        // validation — not a schema check. Fail-closed on anything the
        // evaluator cannot decide outright.
        TheoryLemmaKind::StringGroundEval => {
            string_ground::validate_string_ground_eval(terms, step_id, clause)?;
        }
        // Ground sequence identity through one shared symbolic anchor:
        // `(cl ¬(= x S1) (= x S2))` with S1/S2 ground seq terms whose
        // concat-flattened, empty-dropped normal forms are elementwise
        // identical — validated by an INDEPENDENT normalizer, fail-closed
        // on any non-ground leaf or unsupported operator.
        _ => return Ok(false),
    }
    Ok(true)
}

/// Either sub-schema of `EufCongruenceExplanation`, in a fixed order.
///
/// Two DISJOINT sub-schemas share this kind, the way `ArrayRowChain`'s nine
/// share theirs. (E) is the equality conclusion; (P) is the PREDICATE
/// conclusion, entered only by a clause carrying a literal that is NOT a
/// (possibly negated) equality — which is exactly what (E) declines as out of
/// scope. Neither can take the other's clause, so the order between them
/// carries no authority; (E) stays first so its population's diagnostics stay
/// byte-identical.
///
/// A `ResourceLimit` from EITHER schema is propagated unchanged rather than
/// converted into an `InvalidTheoryLemma`: the caller's envelope refusal is a
/// separate, rescuable class and must never be masked by a shape complaint.
fn validate_euf_congruence_explanation_schemas(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let equality_schema_error =
        match validate_euf_congruence_explanation(terms, step_id, clause, progress) {
            Ok(()) => return Ok(()),
            Err(ProofCheckError::ResourceLimit) => return Err(ProofCheckError::ResourceLimit),
            Err(error) => error,
        };
    validate_euf_polarity_congruence(terms, step_id, clause, progress).map_err(|polarity_error| {
        match polarity_error {
            ProofCheckError::ResourceLimit => ProofCheckError::ResourceLimit,
            _ => equality_schema_error,
        }
    })
}
