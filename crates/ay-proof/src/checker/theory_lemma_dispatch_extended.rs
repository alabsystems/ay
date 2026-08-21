// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn validate_theory_ground_and_words(
    context: &mut TheoryLemmaValidation<'_, '_>,
    kind: TheoryLemmaKind,
) -> Result<bool, ProofCheckError> {
    let terms = context.terms;
    let step_id = context.step_id;
    let clause = context.clause;
    let progress = &mut *context.progress;
    match kind {
        TheoryLemmaKind::SeqGroundEval => {
            seq_ground::validate_seq_ground_eval(terms, step_id, clause)?;
        }
        // Standalone linear-arithmetic clause tautology: the negated
        // clause (or-packed literals flattened conjunctively) is an
        // INFEASIBLE constraint system, re-derived by the independent
        // generic-arithmetic refuter. Intrinsically valid — no pedigree
        // needed — exactly like `BoolTautology` propositionally.
        TheoryLemmaKind::ArithClauseTautology => {
            nia_linear_ideal::validate_generic_arithmetic_refutation_with_progress(
                terms, step_id, clause, progress,
            )?;
        }
        // Term-ite branch projection / guarded ROW expansion: intrinsic
        // clausification tautologies, validated purely structurally.
        TheoryLemmaKind::IteBranchProjection => {
            ite_branch::validate_ite_branch_projection(terms, step_id, clause)?;
        }
        TheoryLemmaKind::ArrayGuardedRowExpansion => {
            ite_branch::validate_array_guarded_row_expansion(terms, step_id, clause)?;
        }
        // Equals-for-equals substitution under asserted ground equalities:
        // registry-free, re-derived by a parallel walk of the source and
        // image terms against the hypothesis map (ground_subst.rs).
        TheoryLemmaKind::GroundEqualitySubstitution => {
            ground_subst::validate_ground_equality_substitution(terms, step_id, clause)?;
        }
        // Regex intersection-emptiness over a SYMBOLIC subject (#regex-cert):
        // the clause carries a `str.in_re` literal group over one common
        // term whose jointly-denied intersection is EMPTY, so no value of
        // the term falsifies the group and the clause is a tautology. The
        // INDEPENDENT derivative-product checker re-derives the whole
        // reachability argument — verified total alphabet partition,
        // closure, non-acceptance — and fails closed on anything it cannot
        // establish outright.
        TheoryLemmaKind::RegexIntersectEmpty => {
            regex_empty::validate_regex_intersect_empty(terms, step_id, clause)?;
        }
        // Universally-valid containment/order identity over a SYMBOLIC
        // subject: self-containment/prefix/suffix, `str.<=` reflexivity,
        // `str.<` irreflexivity, or an empty-word containment. The
        // INDEPENDENT structural checker re-derives the exact theorem —
        // the two positions must hold the SAME term, or the empty-string
        // constant in the operator's own contained-word position — and
        // fails closed on every near-miss.
        TheoryLemmaKind::StringContainmentIdentity => {
            string_word_identity::validate_string_containment_identity(terms, step_id, clause)?;
        }
        // Free-monoid cancellation for `str.++`: `u·w = v·w` forces
        // `u = v` and `w·u = w·v` forces `u = v`. The INDEPENDENT
        // structural checker re-derives the shared block and both
        // residuals from the clause alone; a block that is not
        // syntactically identical, sits at the wrong end, or does not
        // leave exactly the conclusion's two sides is rejected.
        TheoryLemmaKind::StringConcatCancellation => {
            string_word_identity::validate_string_concat_cancellation(terms, step_id, clause)?;
        }
        // A containment refuted by the GROUND blocks it names. The
        // INDEPENDENT factor scan re-derives the impossibility from the
        // clause's own constants — a ground block missing from a ground
        // container, or a ground pattern disagreeing with the container's
        // ground boundary block — and never reasons about the symbolic
        // parts.
        TheoryLemmaKind::StringGroundFactorConflict => {
            string_word_identity::validate_string_ground_factor_conflict(terms, step_id, clause)?;
        }
        // A regex membership bounding `str.len` below. The INDEPENDENT
        // compositional minimum-length computation re-derives the bound
        // from the ground regex tree and rejects `re.comp`, every
        // unmodelled operator, a non-ground leaf, a mismatched subject, and
        // any bound stronger than it can support.
        TheoryLemmaKind::RegexLengthLowerBound => {
            regex_length::validate_regex_length_lower_bound(terms, step_id, clause)?;
        }
        // Datatype constructor distinctness (#8419 / trust_count→0).
        //
        // `(not (= C1(..) C2(..)))` for two distinct constructors of the
        // same datatype is a tautology of datatype theory. The checker
        // cannot recover constructor membership from `TermStore` alone
        // (runtime datatype terms carry `Sort::Uninterpreted`), so the
        // executor supplies the `declare-datatype` registry. Without it
        // this kind fails closed rather than assuming distinctness by shape.
        _ => return Ok(false),
    }
    Ok(true)
}

fn validate_theory_datatype_primary(
    context: &mut TheoryLemmaValidation<'_, '_>,
    kind: TheoryLemmaKind,
) -> Result<bool, ProofCheckError> {
    if validate_theory_datatype_congruence_and_ground(context, kind)? {
        return Ok(true);
    }
    let terms = context.terms;
    let step_id = context.step_id;
    let clause = context.clause;
    let dt_decls = context.dt_decls;
    let ctor_selectors = context.ctor_selectors;
    let datatype_member_signatures = context.datatype_member_signatures;
    match kind {
        TheoryLemmaKind::DatatypeDistinct => match (dt_decls, datatype_member_signatures) {
            (Some(decls), Some(_)) => {
                datatype_axiom::validate_datatype_distinct(terms, step_id, clause, decls)?;
            }
            _ => {
                return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                    step: step_id,
                    kind,
                });
            }
        },
        // Direct acyclicity (occurs check), C5b reintroduced: a denied
        // equality whose one side is a registered-constructor application
        // properly containing the other side through constructor
        // applications only. Iterative bounded walk; the registry is the
        // constructor identity authority, so without it the kind fails
        // closed exactly like its siblings.
        TheoryLemmaKind::DatatypeAcyclicDirect => match (dt_decls, datatype_member_signatures) {
            (Some(decls), Some(_)) => {
                datatype_axiom::validate_datatype_acyclic_direct(terms, step_id, clause, decls)?;
            }
            _ => {
                return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                    step: step_id,
                    kind,
                });
            }
        },
        // Finite-enum pigeonhole. Same fail-closed contract as the sibling
        // above: without the datatype registry the checker cannot establish
        // the constructor count or the nullarity the argument rests on, so
        // the kind is rejected rather than assumed.
        TheoryLemmaKind::DatatypeEnumPigeonhole => match (dt_decls, datatype_member_signatures) {
            (Some(decls), Some(_)) => {
                datatype_axiom::validate_datatype_enum_pigeonhole(
                    terms,
                    step_id,
                    clause,
                    decls,
                    ctor_selectors,
                )?;
            }
            _ => {
                return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                    step: step_id,
                    kind,
                });
            }
        },
        // Datatype selector projection (#trust-count→0).
        //
        // `(= (sel_i (C a_0 .. a_n)) a_i)` — reading field `i` of a
        // constructor application yields argument `i` — is a tautology of
        // datatype theory exactly when `sel_i` is `C`'s registered field-`i`
        // selector. The carrier sort is `Sort::Uninterpreted`, so the checker
        // is given the constructor→selector registry; without it this kind
        // fails closed rather than assuming the projection by shape.
        TheoryLemmaKind::DatatypeSelectorProject => {
            match (ctor_selectors, datatype_member_signatures) {
                (Some(selectors), Some(_)) => {
                    datatype_axiom::validate_datatype_selector_project(
                        terms, step_id, clause, selectors,
                    )?;
                }
                _ => {
                    return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                        step: step_id,
                        kind,
                    });
                }
            }
        }
        // Pure-NRA interval refutation (#nra-cert): the checker's OWN
        // bounded exact-rational interval propagation re-refutes the
        // negated clause from the terms alone — no payload, nothing to
        // forge. Fail-closed on any shape/degree/budget surprise.
        _ => return Ok(false),
    }
    Ok(true)
}

fn validate_theory_datatype_congruence_and_ground(
    context: &mut TheoryLemmaValidation<'_, '_>,
    kind: TheoryLemmaKind,
) -> Result<bool, ProofCheckError> {
    let (Some(decls), Some(selectors), Some(_)) = (
        context.dt_decls,
        context.ctor_selectors,
        context.datatype_member_signatures,
    ) else {
        return match kind {
            TheoryLemmaKind::DatatypeValueEqCongruence
            | TheoryLemmaKind::DatatypeGroundConflict => {
                Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                    step: context.step_id,
                    kind,
                })
            }
            _ => Ok(false),
        };
    };
    match kind {
        // Coverage completeness is re-derived from both registries.
        TheoryLemmaKind::DatatypeValueEqCongruence => {
            datatype_axiom::validate_datatype_value_eq_congruence(
                context.terms,
                context.step_id,
                context.clause,
                decls,
                selectors,
            )?;
        }
        // Independently refute the negated clause with congruence closure and
        // sound datatype rules under both registries.
        TheoryLemmaKind::DatatypeGroundConflict => {
            datatype_ground::validate_datatype_ground_conflict(
                context.terms,
                context.step_id,
                context.clause,
                decls,
                selectors,
            )?;
        }
        _ => return Ok(false),
    }
    Ok(true)
}

fn validate_theory_nra_and_tester(
    context: &mut TheoryLemmaValidation<'_, '_>,
    kind: TheoryLemmaKind,
) -> Result<bool, ProofCheckError> {
    let terms = context.terms;
    let step_id = context.step_id;
    let clause = context.clause;
    let dt_decls = context.dt_decls;
    let ctor_selectors = context.ctor_selectors;
    let datatype_member_signatures = context.datatype_member_signatures;
    match kind {
        TheoryLemmaKind::NraIntervalUnsat => {
            nra_interval::validate_nra_interval_unsat(terms, step_id, clause)?;
        }
        // Pure-NRA univariate refutation (#nra-cert): the checker's OWN
        // exact Sturm-based cell decomposition re-decides the negated
        // one-variable system, algebraically correct at irrational roots
        // (the sqrt(2) trap). Fail-closed everywhere.
        TheoryLemmaKind::NraUnivariateUnsat => {
            nra_univariate::validate_nra_univariate_unsat(terms, step_id, clause)?;
        }
        TheoryLemmaKind::DatatypeTesterEval => match (dt_decls, datatype_member_signatures) {
            (Some(decls), Some(_)) => {
                datatype_axiom::validate_datatype_tester_eval(
                    terms,
                    step_id,
                    clause,
                    decls,
                    ctor_selectors,
                    true,
                )?;
            }
            _ => {
                return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                    step: step_id,
                    kind,
                });
            }
        },
        // Datatype tester pairwise exclusivity (#trust-count→0, Wave 2).
        //
        // `(not (is-C t)) ∨ (not (is-D t))` for DISTINCT registered
        // sibling constructors `C`/`D` is a tautology of datatype theory —
        // a value is built by exactly ONE constructor. Distinctness and
        // shared-datatype membership are re-derived from the registry;
        // without it this kind fails closed rather than trusting the
        // clause to have named two siblings.
        _ => return Ok(false),
    }
    Ok(true)
}

fn validate_theory_datatype_remaining(
    context: &mut TheoryLemmaValidation<'_, '_>,
    kind: TheoryLemmaKind,
) -> Result<bool, ProofCheckError> {
    let terms = context.terms;
    let step_id = context.step_id;
    let clause = context.clause;
    let dt_decls = context.dt_decls;
    let ctor_selectors = context.ctor_selectors;
    let datatype_member_signatures = context.datatype_member_signatures;
    match kind {
        TheoryLemmaKind::DatatypeTesterExclusive => match (dt_decls, datatype_member_signatures) {
            (Some(decls), Some(_)) => {
                datatype_axiom::validate_datatype_tester_exclusive(terms, step_id, clause, decls)?;
            }
            _ => {
                return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                    step: step_id,
                    kind,
                });
            }
        },
        // Datatype constructor coverage (#trust-count→0, C5).
        //
        // `(is-C1 t) ∨ .. ∨ (is-Ck t)` over ALL declared constructors of
        // `t`'s datatype is a tautology of datatype theory — every value
        // is built by SOME constructor. The coverage list cannot be
        // recovered from the `TermStore` (carrier sorts are
        // `Sort::Uninterpreted`), so the executor supplies the registry;
        // without it this kind fails closed rather than trusting the
        // clause to have named every constructor.
        TheoryLemmaKind::DatatypeExhaustive => match (dt_decls, datatype_member_signatures) {
            (Some(decls), Some(_)) => {
                datatype_axiom::validate_datatype_exhaustive(terms, step_id, clause, decls)?;
            }
            _ => {
                return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                    step: step_id,
                    kind,
                });
            }
        },
        // Guarded datatype constructor reconstruction (#trust-count→0, C5).
        //
        // `(not (is-C t)) ∨ (= t (C (sel_1 t) .. (sel_k t)))` is a
        // tautology exactly when `sel_1 .. sel_k` is `C`'s FULL declared
        // selector list in declared field order. Both the constructor
        // registry (tester authentication, sort matching) and the
        // constructor→selector registry (field list + order + nullarity)
        // are required; without either this kind fails closed.
        TheoryLemmaKind::DatatypeConstructorReconstruct => {
            match (dt_decls, ctor_selectors, datatype_member_signatures) {
                (Some(decls), Some(selectors), Some(_)) => {
                    datatype_axiom::validate_datatype_constructor_reconstruct(
                        terms, step_id, clause, decls, selectors,
                    )?;
                }
                _ => {
                    return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                        step: step_id,
                        kind,
                    });
                }
            }
        }
        _ => return Ok(false),
    }
    Ok(true)
}

fn validate_theory_fallback(
    context: &mut TheoryLemmaValidation<'_, '_>,
    other: TheoryLemmaKind,
    trust_collector: Option<&mut Vec<(ProofId, Vec<TermId>)>>,
) -> Result<(), ProofCheckError> {
    let terms = context.terms;
    let step_id = context.step_id;
    let clause = context.clause;
    let progress = &mut *context.progress;
    // Retired non-trust kinds, including the inert datatype C5b
    // tags, intentionally reach the fail-closed rejection below.
    // Before falling back to deferral/rejection, try to VALIDATE the
    // lemma outright: an arithmetic conflict whose refutation is a
    // linear combination of equalities over the monomial basis is
    // fully checkable here, and that is the dominant `Generic` shape
    // (loop-invariant consecution, where the nonlinear monomials
    // cancel). This only ever ACCEPTS what the checker reconstructs
    // itself — the lemma carries no payload to forge — and any other
    // outcome falls through to the pre-existing fail-closed handling
    // below, so nothing that used to be rejected becomes trusted.
    //
    // Two rules share ONE normalization of the negated clause: the
    // equality-SPAN fast path (polynomial identities, where the
    // nonlinear monomials cancel) and, when that declines, the
    // ORDER lane — Fourier-Motzkin elimination over the same
    // monomial-abstracted constraints, which reaches the `<`/`<=`
    // conflicts the span rule ignores by construction
    // (antisymmetry, transitivity, scaled bound contradictions).
    if other.is_trust() {
        match nia_linear_ideal::validate_generic_arithmetic_refutation_with_progress(
            terms, step_id, clause, progress,
        ) {
            Ok(()) => {
                return Ok(());
            }
            Err(ProofCheckError::ResourceLimit) => {
                return Err(ProofCheckError::ResourceLimit);
            }
            Err(_) => {}
        }
    }
    // A trust-kind (`Generic`) theory lemma has no dedicated strict
    // validator (e.g. an integer-arithmetic lemma over an `ite` whose
    // proof is not Farkas-pure, so no typed LIA validator can discharge
    // it). In DEFERRED-trust mode (collector present) record its clause
    // for independent re-discharge and fall through to admit it —
    // exactly like a `Step{rule:Trust}`. In plain strict mode it stays
    // a hard rejection.
    match (other.is_trust(), trust_collector) {
        (true, Some(collector)) => collector.push((step_id, clause.to_vec())),
        _ => {
            // The SHAPE of the lemma no Generic lane could decide is
            // the one fact a strict-decline triage needs, and it was
            // unobservable: `UnsupportedTheoryLemmaKind` names the
            // step and the kind, never the clause. Without it a
            // triage cannot tell a CHECKER gap (the clause is a
            // standalone theory tautology nothing validates) from a
            // PRODUCER defect (the clause is a propagation valid
            // only under the other assertions, which must never be
            // admitted). Gated on the existing typed `--debug-cert`
            // carrier, reachable in-process through
            // `ay_core::set_global_misc_cli_flags_with`.
            if ay_core::misc_cli_flags().debug_cert {
                let rendered: Vec<String> = clause
                    .iter()
                    .map(|&t| crate::format_term_alethe(terms, t))
                    .collect();
                ay_core::safe_eprintln!(
                    "c !! GENERIC lemma declined at {step_id:?} kind={other:?} \
                     clause=[{}]",
                    rendered.join(" | ")
                );
            }
            return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                step: step_id,
                kind: other,
            });
        }
    }
    Ok(())
}
