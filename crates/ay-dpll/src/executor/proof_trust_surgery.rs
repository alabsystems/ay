// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Insert-and-remap surgery for proofs whose resolution skeleton is sound.
//! Instead of re-proving the contradiction, this pass replaces each defective
//! site with a certified derivation and remaps its downstream consumers.
//!
//! Four site classes are repaired (the "n-ary distinct + Int trichotomy"
//! trust class plus the normalized-assume print defects, which need NO trust
//! anchor: a proof whose every step is checkable can still be invalid because
//! a preprocessing-normalized `assume` prints unlike the problem premise):
//!
//! 1. **Int trichotomy trust steps** — `(cl (or (= x y) (<= x (+ y (- 1)))
//!    (<= (+ y 1) x))) :rule trust` plus its `or`-split consumer. Replaced by
//!    `la_disequality ⊢ (cl (or (= x y) (not (<= x y)) (not (<= y x))))`, an
//!    `or` split, and two `[1, 1]` `la_generic` Int-strengthening bridges
//!    (each independently re-verified by `verify_farkas_conflict_lits_full`,
//!    fail-closed), closed by a resolution chain that reproduces the
//!    3-literal strengthened clause. The trust step's unit `(cl (or ...))`
//!    conclusion is NOT re-derived — the `or`-split consumer is REWIRED to
//!    consume the derived 3-literal clause directly, and the trust step +
//!    split are dropped.
//!
//! 2. **N-ary `distinct` assumes** — the exported proof assumes the EXPANDED
//!    `(and (not (= x1 x2)) ...)` form, which no checker can match to the
//!    problem's `(distinct x1 .. xn)` premise. Replaced by an assume of the
//!    raw n-ary `distinct` bridged via `distinct_elim` (pairwise `i < j`
//!    conjunct order) + `equiv_pos2` + resolution down to the conjunction,
//!    with each downstream `and_pos`/resolution unit extraction re-derived
//!    against the bridged conjunction.
//!
//! 3. **Arithmetic-normalized `and` assumes** — a bounds assertion like
//!    `(and .. (>= a 0) ..)` is exported with normalized conjuncts
//!    (`(<= 0 a)`), again unmatchable to the problem premise. Replaced by an
//!    assume of the RAW surface conjunction, with each unit extraction
//!    re-derived from the raw conjunct and bridged to the canonical literal
//!    by a re-verified `[1, 1]` `la_generic` orientation lemma (the class-2
//!    raw-assume pattern).
//!
//! 4. **Arithmetic-normalized bound-literal assumes** — a plain bound like
//!    `(> a 5)` exported as the canonical `(< 5 a)`. Replaced by an assume of
//!    the raw surface literal bridged to the canonical unit by a re-verified
//!    `[1, 1]` `la_generic` orientation lemma, with every consumer remapped
//!    onto the derived unit. Skipped when the surviving surface overrides
//!    (ite-lift class) already print the literal like the file.
//!
//! 5. **Substituted-away equality COLLAPSES** — `substitute-and-simplify`
//!    eliminates a defined constant (`(assert (= v0 t))` -> `v0 := t`), so the
//!    assertions justifying an entailed equality never reach the exported
//!    proof as `assume` steps at all and the equality itself is exported as a
//!    premiseless unproved unit. Repaired by re-introducing exactly those
//!    ORIGINAL assertions into the assumption prologue and closing the unit
//!    against them with a certified EUF recipe plus one resolution per
//!    premise; no assertion is invented.
//!
//! A `trust`-kind theory lemma that a LATER, idempotent export stage certifies
//! in place (an array read-over-write schema re-tag, or a Skolemized
//! extensionality axiom's provenance promotion) is not a defect this pass may
//! touch: it is copied through verbatim, and the acceptance gate re-checks it
//! with the SAME predicate those stages use, on a copy with those stages
//! already applied. Before that, a single array backbone leaf vetoed the
//! repair of every genuinely defective leaf sharing the proof with it.
//!
//! The pass hoists assumptions, rebuilds/remaps the step list in one pass, and
//! leaves the proof byte-identical on any unrecognized or unverifiable site.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{
    AletheRule, FarkasAnnotation, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TheoryLemmaKind,
    TheoryLit,
};
use ay_frontend::command::Term as FrontendTerm;

use super::proof_euf_lemma::{EufLemmaPlan, EufTarget};
use super::proof_surface_syntax::strip_frontend_annotations;
use super::proof_trust_surgery_ite::ProvenanceItePlan;
use super::proof_trust_surgery_ite_plan::IteLiftPlan;
use super::proof_trust_surgery_provenance::{
    canonical_term_work as quant_canonical_term_work, prepare_rebuilt_premise_append,
    retained_surface_plan_mix_is_safe, surface_or_decomposition_matches, surface_source_is_bounded,
    surgery_sources_are_bounded, OriginalSourceIndex, SurgeryPlanningBudget,
    MAX_PROVENANCE_REPAIR_TERMS,
};
use super::proof_trust_surgery_provenance_or::{surface_override_policy_allows, ProvenanceOrPlan};
use super::Executor;

#[path = "proof_trust_surgery_quant_plan.rs"]
mod quant_plan;
#[path = "proof_trust_surgery_quant_surface.rs"]
mod quant_surface;
#[path = "proof_trust_surgery_surface_intern.rs"]
mod surface_intern;
#[path = "proof_trust_surgery_surface_plans.rs"]
mod surface_plans;
#[path = "proof_trust_surgery_taut_surface.rs"]
mod taut_surface;
#[path = "proof_trust_surgery_volume.rs"]
mod volume;

/// Whether two terms are equal modulo binary-equality argument orientation
/// (recursively). Carcara's default mode tolerates exactly this difference
/// ("implicit reordering of equalities") everywhere, including `assume`
/// premise matching.
fn eq_flip_equivalent(terms: &ay_core::TermStore, a: TermId, b: TermId) -> bool {
    if a == b {
        return true;
    }
    match (terms.get(a), terms.get(b)) {
        (TermData::Not(x), TermData::Not(y)) => {
            let (x, y) = (*x, *y);
            eq_flip_equivalent(terms, x, y)
        }
        (TermData::App(sa, xa), TermData::App(sb, xb)) => {
            if sa != sb || xa.len() != xb.len() {
                return false;
            }
            let (sa, xa, xb) = (sa.clone(), xa.clone(), xb.clone());
            let straight = xa
                .iter()
                .zip(xb.iter())
                .all(|(&x, &y)| eq_flip_equivalent(terms, x, y));
            if straight {
                return true;
            }
            matches!(sa, Symbol::Named(ref n) if n == "=")
                && xa.len() == 2
                && eq_flip_equivalent(terms, xa[0], xb[1])
                && eq_flip_equivalent(terms, xa[1], xb[0])
        }
        _ => false,
    }
}

/// Fully expand `let` bindings in a surface term (SMT-LIB parallel-binding
/// semantics: binding values are expanded in the OUTER environment). Returns
/// `None` fail-closed on any binder that could capture (`forall`/`exists`/
/// `lambda`/`match` under a non-empty environment) so no incorrect
/// substitution is ever produced.
fn expand_surface_lets(
    term: &FrontendTerm,
    env: &std::collections::HashMap<String, FrontendTerm>,
) -> Option<FrontendTerm> {
    match term {
        FrontendTerm::Let(bindings, body) => {
            let mut inner = env.clone();
            for (name, value) in bindings {
                let expanded = expand_surface_lets(value, env)?;
                inner.insert(name.clone(), expanded);
            }
            expand_surface_lets(body, &inner)
        }
        FrontendTerm::Symbol(name) => Some(match env.get(name) {
            Some(bound) => bound.clone(),
            None => term.clone(),
        }),
        FrontendTerm::App(head, args) => {
            let args = args
                .iter()
                .map(|a| expand_surface_lets(a, env))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::App(head.clone(), args))
        }
        FrontendTerm::IndexedApp(name, indices, args) => {
            let args = args
                .iter()
                .map(|arg| expand_surface_lets(arg, env))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::IndexedApp(
                name.clone(),
                indices.clone(),
                args,
            ))
        }
        FrontendTerm::QualifiedApp(identifier, sort, args) => {
            let args = args
                .iter()
                .map(|arg| expand_surface_lets(arg, env))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::QualifiedApp(
                identifier.clone(),
                sort.clone(),
                args,
            ))
        }
        FrontendTerm::Annotated(inner, notes) => {
            let inner = expand_surface_lets(inner, env)?;
            Some(FrontendTerm::Annotated(Box::new(inner), notes.clone()))
        }
        FrontendTerm::Const(_) => Some(term.clone()),
        _ => {
            // Binders (and any future variant) under an active environment
            // could capture: fail closed. Without bindings in scope the term
            // needs no expansion.
            env.is_empty().then(|| term.clone())
        }
    }
}

#[cfg(test)]
mod surface_let_tests {
    use super::*;
    use ay_frontend::command::Index as FrontendIndex;
    use ay_frontend::parse;

    #[test]
    fn expansion_descends_into_structured_indexed_terms() {
        let zero = FrontendTerm::IndexedApp(
            "bv0".to_string(),
            vec![FrontendIndex::Numeral("8".to_string())],
            Vec::new(),
        );
        let term = FrontendTerm::Let(
            vec![("x".to_string(), zero.clone())],
            Box::new(FrontendTerm::App(
                "=".to_string(),
                vec![
                    FrontendTerm::Symbol("x".to_string()),
                    FrontendTerm::IndexedApp(
                        "bv1".to_string(),
                        vec![FrontendIndex::Numeral("8".to_string())],
                        Vec::new(),
                    ),
                ],
            )),
        );
        let expanded = expand_surface_lets(&term, &std::collections::HashMap::new())
            .expect("binder-free indexed term expands");
        assert!(matches!(
            expanded,
            FrontendTerm::App(ref op, ref args)
                if op == "=" && args.first() == Some(&zero)
        ));
    }

    #[test]
    fn raw_intern_accepts_structured_decimal_bitvector_literal() {
        let mut executor = Executor::new();
        let literal = FrontendTerm::IndexedApp(
            "bv3".to_string(),
            vec![FrontendIndex::Numeral("4".to_string())],
            Vec::new(),
        );
        let raw = executor
            .raw_intern_surface(&literal)
            .expect("structured decimal bitvector literal interns");
        assert_eq!(executor.ctx.terms.sort(raw), &Sort::bitvec(4));

        let ordinary = FrontendTerm::Symbol("(_ bv3 4)".to_string());
        assert!(executor.raw_intern_surface(&ordinary).is_none());

        let character = FrontendTerm::IndexedApp(
            "Char".to_string(),
            vec![FrontendIndex::Numeral("65".to_string())],
            Vec::new(),
        );
        assert!(executor.raw_intern_surface(&character).is_none());
    }

    #[test]
    fn raw_intern_preserves_a_folded_ite_source() {
        use ay_frontend::command::Constant as SurfaceConstant;

        let mut executor = Executor::new();
        let surface = FrontendTerm::App(
            "ite".to_string(),
            vec![
                FrontendTerm::Const(SurfaceConstant::True),
                FrontendTerm::Const(SurfaceConstant::Numeral("1".to_string())),
                FrontendTerm::Const(SurfaceConstant::Numeral("2".to_string())),
            ],
        );
        let canonical = executor
            .ctx
            .elaborate_surface_subterm(&surface)
            .expect("ground ite elaborates");
        let raw = executor
            .raw_intern_surface(&surface)
            .expect("ground ite raw-interns");

        assert_ne!(raw, canonical, "raw source must not inherit ite folding");
        assert!(matches!(
            executor.ctx.terms.get(raw),
            TermData::Ite(condition, then_term, else_term)
                if executor.ctx.terms.is_true(*condition)
                    && then_term != else_term
        ));
    }

    #[test]
    fn raw_intern_preserves_private_identity_for_declared_builtin_spellings() {
        use ay_frontend::command::Constant as SurfaceConstant;

        let cases = [
            (
                "(declare-fun = (Int Int) Bool)",
                "=",
                vec![
                    FrontendTerm::Const(SurfaceConstant::Numeral("0".to_string())),
                    FrontendTerm::Const(SurfaceConstant::Numeral("1".to_string())),
                ],
            ),
            (
                "(declare-fun rem (Int Int) Int)",
                "rem",
                vec![
                    FrontendTerm::Const(SurfaceConstant::Numeral("5".to_string())),
                    FrontendTerm::Const(SurfaceConstant::Numeral("2".to_string())),
                ],
            ),
            (
                "(declare-fun to_int (Real) Int)",
                "to_int",
                vec![FrontendTerm::Const(SurfaceConstant::Decimal(
                    "1.5".to_string(),
                ))],
            ),
        ];

        for (declaration, head, args) in cases {
            let mut executor = Executor::new();
            let commands = parse(declaration).expect("declaration parses");
            executor
                .execute_all(&commands)
                .expect("declaration executes");

            let surface = FrontendTerm::App(head.to_string(), args);
            let elaborated = executor
                .ctx
                .elaborate_surface_subterm(&surface)
                .expect("declared application elaborates");
            let raw = executor
                .raw_intern_surface(&surface)
                .expect("declared application raw-interns");
            let expected_identity = executor
                .ctx
                .symbol_iter()
                .find(|(surface, _)| surface.as_str() == head)
                .map(|(surface, info)| executor.ctx.symbol_identity_name(surface, info))
                .expect("declaration remains live");

            assert_ne!(
                expected_identity, head,
                "builtin-colliding declarations require a private identity"
            );
            assert!(matches!(
                executor.ctx.terms.get(elaborated),
                TermData::App(Symbol::Named(identity), _) if identity == expected_identity
            ));
            assert!(matches!(
                executor.ctx.terms.get(raw),
                TermData::App(Symbol::Named(identity), _) if identity == expected_identity
            ));
        }
    }

    #[test]
    fn raw_ematching_forall_preserves_private_declaration_identity() {
        use ay_frontend::command::Constant as SurfaceConstant;

        let mut executor = Executor::new();
        let commands = parse(
            "(declare-fun rem (Int Int) Int)\n\
             (assert (forall ((x Int)) (= (rem x 2) 0)))",
        )
        .expect("quantified private-UF fixture parses");
        let ay_frontend::Command::Assert(parsed_forall) = &commands[1] else {
            panic!("fixture must contain an asserted forall");
        };
        let parsed_forall = parsed_forall.clone();
        executor
            .execute_all(&commands)
            .expect("quantified private-UF fixture executes");

        let canonical_forall = executor.ctx.assertions[0];
        let private_identity = executor
            .ctx
            .symbol_iter()
            .find(|(surface, _)| surface.as_str() == "rem")
            .map(|(surface, info)| executor.ctx.symbol_identity_name(surface, info).to_string())
            .expect("rem declaration remains live");
        assert_ne!(private_identity, "rem");

        let five = executor.ctx.terms.mk_int(5.into());
        let ground_surface = FrontendTerm::App(
            "=".to_string(),
            vec![
                FrontendTerm::App(
                    "rem".to_string(),
                    vec![
                        FrontendTerm::Const(SurfaceConstant::Numeral("5".to_string())),
                        FrontendTerm::Const(SurfaceConstant::Numeral("2".to_string())),
                    ],
                ),
                FrontendTerm::Const(SurfaceConstant::Numeral("0".to_string())),
            ],
        );
        let ground_instance = executor
            .raw_intern_surface(&ground_surface)
            .expect("authenticated ground instance raw-interns");
        let rebuilt = executor
            .build_raw_ematching_forall_source(
                canonical_forall,
                &parsed_forall,
                &[five],
                ground_instance,
            )
            .expect("binder lifting preserves the authenticated private head");

        let TermData::Forall(_, raw_body, _) = executor.ctx.terms.get(rebuilt).clone() else {
            panic!("proof repair must rebuild a forall");
        };
        let mut pending = vec![raw_body];
        let mut found_private_head = false;
        while let Some(term) = pending.pop() {
            if matches!(
                executor.ctx.terms.get(term),
                TermData::App(Symbol::Named(identity), _) if identity == &private_identity
            ) {
                found_private_head = true;
                break;
            }
            pending.extend(executor.ctx.terms.children(term));
        }
        assert!(
            found_private_head,
            "rebuilt quantified proof source lost private declaration identity"
        );
    }

    #[test]
    fn rebuilt_private_equality_does_not_authorize_canonical_builtin_collision() {
        let mut executor = Executor::new();
        let commands = parse(
            "(declare-fun = (Int Int) Bool)\n\
             (assert (= 0 1))",
        )
        .expect("fixture parses");
        executor.execute_all(&commands).expect("fixture executes");

        // The rebuild captures both the canonical authored root and any raw
        // source reconstruction that proof surgery may assume.
        executor.rebuild_trust_leaf_proof_from_original_assertions(&mut Proof::new());
        let private_equality = executor
            .last_proof_rebuild_originals
            .iter()
            .copied()
            .find(|&term| {
                matches!(
                    executor.ctx.terms.get(term),
                    TermData::App(Symbol::Named(identity), _)
                        if identity != "="
                            && executor.ctx.dt_surface_name(identity) == Some("=")
                )
            })
            .expect("rebuilt authored premise retains the private declaration identity");
        let args = match executor.ctx.terms.get(private_equality).clone() {
            TermData::App(_, args) => args,
            _ => unreachable!("matched an application above"),
        };
        let canonical_builtin = executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), args, Sort::Bool);
        assert!(!executor
            .problem_assertions_for_strict_proof()
            .contains(&canonical_builtin));

        // Source spelling alone must not authorize the canonical builtin: the
        // problem asserted a free UF application instead. Assumption authority
        // is validated before terminal-proof shape, so this minimal proof
        // isolates the exact scope decision under test.
        let mut forged = Proof::new();
        forged.add_assume(canonical_builtin, None);
        assert!(matches!(
            executor.check_proof_strict_with_datatypes(&forged),
            Err(ay_proof::ProofCheckError::UnauthorizedAssumption {
                term,
                ..
            }) if term == canonical_builtin
        ));
    }

    fn normalized_authored_or_fixture() -> (Executor, Vec<(TermId, FrontendTerm)>, TermId, TermId) {
        let mut executor = Executor::new();
        let commands = parse(
            "(declare-const p Bool)\n\
             (declare-const n Int)\n\
             (declare-const x Int)\n\
             (declare-const y Int)\n\
             (declare-const z Int)\n\
             (assert (=> p (=> (< 0 n) (= (+ x 0) (+ y 0)))))",
        )
        .expect("normalized authored-or fixture parses");
        executor
            .execute_all(&commands)
            .expect("normalized authored-or fixture executes");
        let canonical = executor.ctx.assertions[0];
        let parsed = executor.ctx.assertions_parsed()[0].clone();

        let TermData::App(Symbol::Named(source_name), source_disjuncts) =
            executor.ctx.terms.get(canonical).clone()
        else {
            panic!("canonical implication must be a packed or")
        };
        assert_eq!(source_name, "or");
        assert_eq!(source_disjuncts.len(), 3);
        let source_guard = source_disjuncts
            .iter()
            .copied()
            .find(|&term| {
                matches!(
                    executor.ctx.terms.get(term),
                    TermData::Not(atom)
                        if matches!(
                            executor.ctx.terms.get(*atom),
                            TermData::App(Symbol::Named(name), args)
                                if name == "<" && args.len() == 2
                        )
                )
            })
            .expect("canonical implication contains its negated strict guard");
        let guard = match executor.ctx.terms.get(source_guard) {
            TermData::Not(atom) => *atom,
            _ => unreachable!("source guard was matched above"),
        };
        let guard_args = match executor.ctx.terms.get(guard).clone() {
            TermData::App(_, args) => args,
            _ => unreachable!("source guard atom was matched above"),
        };
        // Mirror #7956 exactly: implication clausification dualizes the raw
        // `(not (< 0 n))` disjunct to the equivalent `(<= n 0)` literal.
        let normalized_guard = executor.ctx.terms.mk_app(
            Symbol::named("<="),
            [guard_args[1], guard_args[0]],
            Sort::Bool,
        );
        let raw_not_guard = executor.ctx.terms.mk_not_raw(guard);
        assert_ne!(
            normalized_guard, raw_not_guard,
            "fixture must exercise the checked arithmetic bridge"
        );
        let target_disjuncts: Vec<TermId> = source_disjuncts
            .iter()
            .map(|&term| {
                if term == source_guard {
                    normalized_guard
                } else {
                    term
                }
            })
            .collect();
        let target = executor
            .ctx
            .terms
            .mk_app(Symbol::named("or"), target_disjuncts, Sort::Bool);
        let z = executor
            .ctx
            .terms
            .lookup("z")
            .expect("declared z remains interned");
        (executor, vec![(canonical, parsed)], target, z)
    }

    #[test]
    fn normalized_authored_implication_derives_exact_packed_or() {
        let (mut executor, originals, target, _) = normalized_authored_or_fixture();
        let plan = executor
            .plan_normalized_authored_or(&[target], &originals)
            .expect("the authenticated implication must align with the packed proof target");
        assert!(matches!(
            executor.ctx.terms.get(plan.source_or),
            TermData::App(Symbol::Named(name), _) if name == "or"
        ));
        assert_eq!(
            plan.literals
                .iter()
                .filter(|literal| literal.bridge_atom.is_some())
                .count(),
            1,
            "only the negated strict comparison may need normalization"
        );

        let mut proof = Proof::new();
        let source = proof.add_assume(plan.source_or, None);
        let unit = executor
            .emit_normalized_authored_or(&mut proof, &plan, source)
            .expect("the planned implication/or bridge emits");
        assert!(matches!(
            &proof.steps[unit.0 as usize],
            ProofStep::Step {
                clause,
                rule: AletheRule::Contraction,
                ..
            } if clause.as_slice() == [target]
        ));
        let authenticated = ay_proof::authenticate_premise_clauses_strict_with_context(
            &proof,
            &executor.ctx.terms,
            None,
            None,
            &[plan.source_or],
        )
        .expect("every implication, arithmetic, packing, and resolution step replays");
        assert_eq!(authenticated.clause(unit), Some([target].as_slice()));
        assert_eq!(
            ay_proof::terminal_trust_report(&proof).trust_rule_on_path,
            0
        );
    }

    #[test]
    fn normalized_authored_implication_refuses_forged_guard_or_equality() {
        let (mut executor, originals, target, z) = normalized_authored_or_fixture();
        let TermData::App(Symbol::Named(name), disjuncts) = executor.ctx.terms.get(target).clone()
        else {
            panic!("fixture target must be a packed or")
        };
        assert_eq!(name, "or");
        let eq_pos = disjuncts
            .iter()
            .position(|&term| decode_binary_equality(&executor.ctx.terms, term).is_some())
            .expect("target contains its raw equality");
        let guard_pos = disjuncts
            .iter()
            .position(|&term| {
                matches!(
                    executor.ctx.terms.get(term),
                    TermData::App(Symbol::Named(op), args) if op == "<=" && args.len() == 2
                )
            })
            .expect("target contains its normalized guard");

        let (eq_lhs, _) = decode_binary_equality(&executor.ctx.terms, disjuncts[eq_pos])
            .expect("equality position was checked");
        let wrong_equality = executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [eq_lhs, z], Sort::Bool);
        let guard_args = match executor.ctx.terms.get(disjuncts[guard_pos]).clone() {
            TermData::App(_, args) => args,
            _ => unreachable!("guard position was checked"),
        };
        let one = executor.ctx.terms.mk_int(1.into());
        let wrong_guard =
            executor
                .ctx
                .terms
                .mk_app(Symbol::named("<="), [guard_args[0], one], Sort::Bool);

        for (label, position, replacement) in [
            ("equality", eq_pos, wrong_equality),
            ("guard", guard_pos, wrong_guard),
        ] {
            let mut forged_disjuncts = disjuncts.clone();
            forged_disjuncts[position] = replacement;
            let forged =
                executor
                    .ctx
                    .terms
                    .mk_app(Symbol::named("or"), forged_disjuncts, Sort::Bool);
            assert!(
                executor
                    .plan_normalized_authored_or(&[forged], &originals)
                    .is_none(),
                "a forged {label} must not align with the authenticated source"
            );
        }
    }

    fn authored_array_ite_fixture() -> (Executor, Vec<(TermId, FrontendTerm)>, TermId, TermId) {
        let mut executor = Executor::new();
        let commands = parse(
            "(declare-const a (Array Int Int))\n\
             (declare-const x Int)\n\
             (declare-const v Int)\n\
             (declare-const wrong Int)\n\
             (assert (= a (store ((as const (Array Int Int)) 0) 0 v)))\n\
             (assert (= x 0))",
        )
        .expect("authored array-ite fixture parses");
        executor
            .execute_all(&commands)
            .expect("authored array-ite fixture executes");
        let originals: Vec<(TermId, FrontendTerm)> = executor
            .ctx
            .assertions
            .iter()
            .copied()
            .zip(executor.ctx.assertions_parsed().iter().cloned())
            .collect();
        let array_equality = originals[0].0;
        let guard = originals[1].0;
        let a = executor.ctx.terms.lookup("a").expect("a is interned");
        let x = executor.ctx.terms.lookup("x").expect("x is interned");
        let v = executor.ctx.terms.lookup("v").expect("v is interned");
        let wrong = executor
            .ctx
            .terms
            .lookup("wrong")
            .expect("wrong is interned");
        let zero = executor.ctx.terms.mk_int(0.into());
        let read = executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [a, x], Sort::Int);
        let then_branch = executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [v, read], Sort::Bool);
        let else_branch = executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [zero, read], Sort::Bool);
        let ite = executor.ctx.terms.mk_ite(guard, then_branch, else_branch);
        let not_equality = executor.ctx.terms.mk_not_raw(array_equality);
        let target =
            executor
                .ctx
                .terms
                .mk_app(Symbol::named("or"), [not_equality, ite], Sort::Bool);
        (executor, originals, target, wrong)
    }

    #[test]
    fn authored_array_ite_derives_packed_unit_from_row_chain() {
        let (mut executor, originals, target, _) = authored_array_ite_fixture();
        let plan = executor
            .plan_authored_array_ite(&[target], &originals)
            .expect("the exact authored equality and guard must certify the array ITE");
        assert_eq!(
            ay_proof::recognize_array_theory_lemma(&executor.ctx.terms, &plan.congruence_clause,),
            Some(TheoryLemmaKind::ArrayRowChain)
        );
        assert_eq!(
            ay_proof::recognize_array_select_store(&executor.ctx.terms, &plan.row1_clause),
            Some(true)
        );

        let mut proof = Proof::new();
        let equality_assume = proof.add_assume(plan.array_equality, None);
        let guard_assume = proof.add_assume(plan.guard_source, None);
        let unit = executor
            .emit_authored_array_ite(&mut proof, &plan, equality_assume, guard_assume)
            .expect("the checked ROW/ITE/OR derivation emits");
        let authenticated = ay_proof::authenticate_premise_clauses_strict_with_context(
            &proof,
            &executor.ctx.terms,
            None,
            None,
            &[plan.array_equality, plan.guard_source],
        )
        .expect("every ROW, ITE, OR, and resolution step replays");
        assert_eq!(authenticated.clause(unit), Some([target].as_slice()));
        assert_eq!(
            ay_proof::terminal_trust_report(&proof).trust_rule_on_path,
            0
        );
    }

    #[test]
    fn authored_array_ite_refuses_forged_then_branch() {
        let (mut executor, originals, target, wrong) = authored_array_ite_fixture();
        assert!(
            executor
                .plan_authored_array_ite(&[target], &originals[..1])
                .is_none(),
            "the array equality alone must not authorize the ITE guard"
        );
        assert!(
            executor
                .plan_authored_array_ite(&[target], &originals[1..])
                .is_none(),
            "the guard alone must not authorize the array equality"
        );
        let TermData::App(Symbol::Named(op), disjuncts) = executor.ctx.terms.get(target).clone()
        else {
            panic!("fixture target must be an or")
        };
        assert_eq!(op, "or");
        let ite_position = disjuncts
            .iter()
            .position(|&term| matches!(executor.ctx.terms.get(term), TermData::Ite(..)))
            .expect("fixture target contains its ITE");
        let TermData::Ite(guard, _, else_branch) =
            executor.ctx.terms.get(disjuncts[ite_position]).clone()
        else {
            unreachable!("ITE position was checked")
        };
        let read = match executor.ctx.terms.get(else_branch).clone() {
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => args[1],
            _ => panic!("fixture else branch is an equality"),
        };
        let forged_then = executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [wrong, read], Sort::Bool);
        let forged_ite = executor.ctx.terms.mk_ite(guard, forged_then, else_branch);
        let mut forged_disjuncts = disjuncts;
        forged_disjuncts[ite_position] = forged_ite;
        let forged = executor
            .ctx
            .terms
            .mk_app(Symbol::named("or"), forged_disjuncts, Sort::Bool);
        assert!(
            executor
                .plan_authored_array_ite(&[forged], &originals)
                .is_none(),
            "a forged then branch must not pass the strict ROW matcher"
        );
    }

    #[test]
    fn native_ematching_body_preflight_rejects_excess_depth() {
        let mut terms = ay_core::TermStore::new();
        let mut body = terms.mk_bool(true);
        for _ in 0..=256 {
            body = terms.mk_app(Symbol::named("native_depth"), [body], Sort::Bool);
        }
        assert!(quant_canonical_term_work(&terms, body).is_none());
    }

    #[test]
    fn legacy_ite_scan_preflight_rejects_excess_arity() {
        let mut terms = ay_core::TermStore::new();
        let atom = terms.mk_bool(true);
        let body = terms.mk_app(
            Symbol::named("legacy_ite_wide"),
            vec![atom; 100_001],
            Sort::Bool,
        );
        assert!(quant_canonical_term_work(&terms, body).is_none());
    }
}

/// The two operands of a top-level binary `(= a b)` application, or `None`.
fn decode_binary_equality(terms: &ay_core::TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

fn atom_of(terms: &ay_core::TermStore, lit: TermId) -> TermId {
    match terms.get(lit) {
        TermData::Not(inner) => *inner,
        _ => lit,
    }
}

/// Whether `t` is a PURE linear-arithmetic term: numerals, arithmetic
/// variables / declared constants, and `+`/`-`/`*` applications thereof.
/// The internal Farkas verifier treats any non-arithmetic atom (e.g. an
/// array `select`) as an opaque linear unknown, but external `la_generic`
/// checking evaluates the linear combination syntactically — so promotions
/// that flip a lemma onto `la_generic` must reject impure atoms.
fn term_is_pure_linear_arith(terms: &ay_core::TermStore, t: TermId) -> bool {
    if !matches!(terms.sort(t), Sort::Int | Sort::Real) {
        return false;
    }
    match terms.get(t) {
        TermData::Const(_) | TermData::Var(..) => true,
        TermData::App(Symbol::Named(op), args) => match op.as_str() {
            "+" | "-" | "*" => args.iter().all(|&a| term_is_pure_linear_arith(terms, a)),
            _ => args.is_empty(),
        },
        _ => false,
    }
}

/// Whether both operands of the equality application `eq` are pure
/// linear-arithmetic terms (see [`term_is_pure_linear_arith`]).
fn equality_is_pure_linear_arith(terms: &ay_core::TermStore, eq: TermId) -> bool {
    match terms.get(eq) {
        TermData::App(Symbol::Named(op), args) if op == "=" && args.len() == 2 => {
            let (a, b) = (args[0], args[1]);
            term_is_pure_linear_arith(terms, a) && term_is_pure_linear_arith(terms, b)
        }
        _ => false,
    }
}

/// Complement of a literal without double negation.
fn complement_of(terms: &mut ay_core::TermStore, lit: TermId) -> TermId {
    match terms.get(lit) {
        TermData::Not(inner) => *inner,
        _ => terms.mk_not_raw(lit),
    }
}

include!("proof_trust_surgery/ground_linear_collapse.rs");
include!("proof_trust_surgery/false_collapse_shape.rs");

/// How a defective `assume` gets repaired.
enum AssumePlan {
    /// Surface `(distinct x1 .. xn)`, n >= 3, exported as the expanded
    /// pairwise conjunction: assume the raw `distinct`, bridge via
    /// `distinct_elim` + `equiv_pos2` to the conjunction.
    Distinct {
        /// Raw `(distinct x1 .. xn)` application (prints like the file).
        raw: TermId,
        /// The canonical pairwise conjunction (the old assume's term).
        and_term: TermId,
        /// Conjuncts of `and_term`, in order.
        conjs: Vec<TermId>,
    },
    /// Surface `(and c1 .. cn)` whose conjuncts were arithmetic-normalized
    /// (or binary-`distinct` sugar): assume the raw surface conjunction,
    /// bridge each extracted unit where the raw conjunct differs from the
    /// canonical one.
    AndBounds {
        /// Raw `(and raw_1 .. raw_n)` application.
        raw_and: TermId,
        /// Per conjunct: the raw surface literal and, when it differs from
        /// the canonical conjunct, the raw literal's atom (bridge pivot).
        raws: Vec<(TermId, Option<TermId>)>,
        /// Canonical conjuncts (of the old assume's term), in order.
        conjs: Vec<TermId>,
    },
    /// Surface `(and c1 .. cn)` with binary-`distinct` sugar conjuncts
    /// (exported as canonical `(not (= s t))`, whose print no longer matches
    /// the file): assume the raw surface conjunction and RE-DERIVE the
    /// canonical conjunction as a unit — per-conjunct `and_pos` extraction
    /// (bridged via `distinct_elim` + `equiv_pos2` where sugared, or a
    /// certified orientation lemma where arithmetic-normalized) closed by
    /// `and_neg` — onto which EVERY consumer is remapped (unlike the
    /// bounds class, consumers may resolve the assume anywhere).
    AndDistinct {
        /// Raw `(and raw_1 .. raw_n)` application (prints like the file;
        /// folded-away conjuncts like `(= c c)` reappear here raw).
        raw_and: TermId,
        /// The canonical conjunction (the old assume's term).
        and_term: TermId,
        /// The raw conjuncts that supply canonical conjunct units, in
        /// canonical-conjunct order.
        units: Vec<AndDistinctUnit>,
        /// Canonical conjuncts (of the old assume's term), in order.
        conjs: Vec<TermId>,
    },
    /// A single arithmetic-normalized bound literal (e.g. surface `(> a 5)`
    /// exported as the canonical `(< 5 a)`): assume the raw surface literal,
    /// bridge to the canonical literal by a certified `[1, 1]` orientation
    /// lemma, and remap every consumer onto the derived unit.
    Literal {
        /// Raw surface literal (prints like the file).
        raw: TermId,
        /// The raw literal's atom (the bridge resolution pivot).
        atom: TermId,
        /// The canonical literal (the old assume's term).
        canonical: TermId,
    },
    /// A finite-domain quantifier expansion assume (#quant-expansion-proof):
    /// preprocessing replaced a top-level `forall` assertion in place with
    /// the merged ground-instance conjunction, and the exporter assumed the
    /// conjunction — which no external checker can match to the problem's
    /// `forall` premise. Replaced by an assume of the ORIGINAL `forall`;
    /// every consumed conjunct is re-DERIVED from it: `forall_inst`
    /// (positional binder-value args) + `or` + resolution to the raw
    /// substituted body, `implies_pos` + per-atom unit `la_generic` guard
    /// discharge + `and_neg`, and a certified `[1, 1]` strict-Int
    /// orientation bridge onto the canonical conjunct where the tightening
    /// pass rewrote it. All consumers must be recognized unit-extraction
    /// patterns (like [`AssumePlan::AndBounds`]).
    QuantExpansion {
        /// The original `forall` assertion (a genuine problem premise).
        forall_term: TermId,
        /// Index of its parsed authored source in `originals`.
        assertion_index: usize,
        /// Canonical conjuncts of the expansion (the old assume's term).
        conjs: Vec<TermId>,
        /// Folded instance term -> binder values (in binder order).
        instances: HashMap<TermId, Vec<TermId>>,
    },
}

/// A planned per-instance derivation chain from an original `forall`
/// premise to a single unit clause (#quant-expansion-proof). Every
/// ingredient is validated at plan time: the substituted body is built from
/// the premise's own SURFACE syntax (so the printed `forall_inst`
/// conclusion is exactly the instantiation an external checker recomputes),
/// each guard atom is certified as a ground arithmetic tautology by the
/// independent Farkas checker, and the optional strict-Int bridge is a
/// re-verified `[1, 1]` `la_generic` lemma.
struct QuantInstanceChain {
    /// Binder values, in binder order (the `forall_inst` positional args).
    values: Vec<TermId>,
    /// Raw-interned substituted body (the `forall_inst` instance).
    phi: TermId,
    /// `(guard term, guard atoms)` when `phi` is `(=> g b)`; each atom is a
    /// certified ground arithmetic truth, all atoms distinct.
    guard: Option<(TermId, Vec<TermId>)>,
    /// The consequent literal the chain concludes (`phi` when no guard).
    body_lit: TermId,
    /// The final unit term consumers expect. When it differs from
    /// `body_lit`, the plan-time-validated `[1, 1]` pair lemma
    /// `(cl target (not body_lit))` bridges the two.
    target: TermId,
}

/// A recognized trust unit `(cl L)` that is a preprocessing-folded
/// CONSEQUENCE of a quantifier-expansion instance and up to one original
/// premise (#quant-expansion-proof): e.g. the conjunct
/// `(<= (f 24) (+ (f 25) (- 1)))` folded with the asserted `(= (f 25) 26)`
/// into `(<= (f 24) 25)`. Replaced by the instance derivation chain, an
/// assume per consumed original, and one re-verified `la_generic` lemma
/// `(cl (not inst) (not orig).. L)` closed by resolutions.
struct QuantConsequencePlan {
    /// The original `forall` assertion the instance derives from.
    forall_term: TermId,
    /// The plan-time-built derivation of `(cl chain.target)`.
    chain: QuantInstanceChain,
    /// Original premises consumed by the folding (assumed in the rebuild).
    supports: Vec<TermId>,
    /// The validated lemma clause `(not chain.target) (not s)... L`,
    /// ending in the trust unit `L` the consumers expect.
    lemma: Vec<TermId>,
}

/// A folded trust unit `(cl (not Q))` recovered from one authenticated direct
/// E-matching instance of `Q` and up to one original arithmetic premise.
///
/// The producer emits `forall_inst` as `(not Q) \/ instance`, derives
/// `not(instance)` from the original arithmetic premise with a separately
/// checked Farkas lemma, and resolves the two clauses.  Crucially, it does not
/// assume `Q` while deriving `not Q`; the existing proof's authored `Q`
/// assumption closes the final contradiction.
struct QuantNegationPlan {
    /// Canonical source term carried by the pre-surgery proof.  Its Assume is
    /// replaced with `forall_term` so the repaired negative unit remains an
    /// exact complement at both the internal and external checker layers.
    source_quantifier: TermId,
    /// Authored assertion position used to recover the exact surface spelling.
    assertion_index: usize,
    /// Rebuilt original forall term used by the strict `forall_inst` step.
    forall_term: TermId,
    /// Exact positional values and raw ground instance.
    chain: QuantInstanceChain,
    /// Original arithmetic premises consumed by the conflict (currently at
    /// most one; bounded search and independent Farkas validation below).
    supports: Vec<TermId>,
    /// Validated arithmetic conflict clause `(not instance) (not support)..`.
    lemma: Vec<TermId>,
}

/// Substitute ground surface terms for binder-name symbols in a parsed
/// surface term. Fails closed (`None`) on ANY binding construct
/// (`let`/`forall`/`exists`/`lambda`/`match`) — shadowing or capture would
/// make plain symbol replacement incorrect — so only binder-free bodies are
/// instantiated. Annotations are stripped (external checkers compare the
/// bare term).
fn surface_subst_ground(
    term: &FrontendTerm,
    subst: &HashMap<String, FrontendTerm>,
) -> Option<FrontendTerm> {
    match term {
        FrontendTerm::Annotated(inner, _) => surface_subst_ground(inner, subst),
        FrontendTerm::Const(_) => Some(term.clone()),
        FrontendTerm::Symbol(name) => {
            Some(subst.get(name).cloned().unwrap_or_else(|| term.clone()))
        }
        FrontendTerm::App(head, args) => {
            let new_args = args
                .iter()
                .map(|a| surface_subst_ground(a, subst))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::App(head.clone(), new_args))
        }
        FrontendTerm::IndexedApp(name, indices, args) => {
            let new_args = args
                .iter()
                .map(|a| surface_subst_ground(a, subst))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::IndexedApp(
                name.clone(),
                indices.clone(),
                new_args,
            ))
        }
        FrontendTerm::QualifiedApp(name, sort, args) => {
            let new_args = args
                .iter()
                .map(|a| surface_subst_ground(a, subst))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::QualifiedApp(
                name.clone(),
                sort.clone(),
                new_args,
            ))
        }
        _ => None,
    }
}

/// Reconstruct a raw quantified body from its raw ground surface instance.
///
/// `surface_subst_ground` records exactly where each binder was replaced.
/// Walking the original and substituted surface trees alongside the raw
/// ground term lets us reverse only those binder-origin positions.  Equal
/// ground constants elsewhere are untouched, avoiding the unsound global
/// `value -> variable` reverse substitution.  Only binder-free QF body shapes
/// supported by `raw_intern_surface` are admitted; every mismatch fails closed.
fn lift_surface_binders_from_ground(
    terms: &mut ay_core::TermStore,
    source: &FrontendTerm,
    substituted: &FrontendTerm,
    ground: TermId,
    bound_vars: &HashMap<String, TermId>,
) -> Option<TermId> {
    if let FrontendTerm::Annotated(inner, _) = source {
        return lift_surface_binders_from_ground(terms, inner, substituted, ground, bound_vars);
    }
    if let FrontendTerm::Annotated(inner, _) = substituted {
        return lift_surface_binders_from_ground(terms, source, inner, ground, bound_vars);
    }
    match (source, substituted) {
        (FrontendTerm::Symbol(name), _) if bound_vars.contains_key(name) => {
            bound_vars.get(name).copied()
        }
        (FrontendTerm::Symbol(source_name), FrontendTerm::Symbol(substituted_name))
            if source_name == substituted_name =>
        {
            Some(ground)
        }
        (FrontendTerm::Const(source_const), FrontendTerm::Const(substituted_const))
            if source_const == substituted_const =>
        {
            Some(ground)
        }
        (
            FrontendTerm::App(source_head, source_args),
            FrontendTerm::App(substituted_head, substituted_args),
        ) if source_head == substituted_head && source_args.len() == substituted_args.len() => {
            // `ground` was built by `raw_intern_surface` and authenticated
            // byte-exactly by `build_raw_ematching_forall_source` before this
            // reverse lift. Preserve its exact core symbol: a declaration whose
            // legal surface spelling collides with a builtin deliberately has a
            // private identity, and rebuilding from `source_head` would silently
            // turn that UF back into the builtin during proof repair.
            let (ground_symbol, ground_args): (Option<Symbol>, Vec<TermId>) =
                match terms.get(ground) {
                    TermData::Not(inner) if source_head == "not" && source_args.len() == 1 => {
                        (None, vec![*inner])
                    }
                    TermData::Ite(cond, then_term, else_term)
                        if source_head == "ite" && source_args.len() == 3 =>
                    {
                        (None, vec![*cond, *then_term, *else_term])
                    }
                    TermData::App(symbol, args) if source_head != "not" && source_head != "ite" => {
                        (Some(symbol.clone()), args.clone())
                    }
                    _ => return None,
                };
            if ground_args.len() != source_args.len() {
                return None;
            }
            let rebuilt = source_args
                .iter()
                .zip(substituted_args)
                .zip(ground_args)
                .map(|((source_arg, substituted_arg), ground_arg)| {
                    lift_surface_binders_from_ground(
                        terms,
                        source_arg,
                        substituted_arg,
                        ground_arg,
                        bound_vars,
                    )
                })
                .collect::<Option<Vec<_>>>()?;
            if source_head == "not" {
                return Some(terms.mk_not_raw(rebuilt[0]));
            }
            if source_head == "ite" {
                return Some(terms.mk_ite_raw(rebuilt[0], rebuilt[1], rebuilt[2]));
            }
            let sort = terms.sort(ground).clone();
            Some(terms.mk_app(ground_symbol?, rebuilt, sort))
        }
        (
            FrontendTerm::IndexedApp(source_name, source_indices, source_args),
            FrontendTerm::IndexedApp(substituted_name, substituted_indices, substituted_args),
        ) if source_name == substituted_name
            && source_indices == substituted_indices
            && source_args.len() == substituted_args.len() =>
        {
            let TermData::App(symbol, ground_args) = terms.get(ground).clone() else {
                return None;
            };
            if ground_args.len() != source_args.len() {
                return None;
            }
            let rebuilt = source_args
                .iter()
                .zip(substituted_args)
                .zip(ground_args)
                .map(|((source_arg, substituted_arg), ground_arg)| {
                    lift_surface_binders_from_ground(
                        terms,
                        source_arg,
                        substituted_arg,
                        ground_arg,
                        bound_vars,
                    )
                })
                .collect::<Option<Vec<_>>>()?;
            let sort = terms.sort(ground).clone();
            Some(terms.mk_app(symbol, rebuilt, sort))
        }
        (
            FrontendTerm::QualifiedApp(source_name, source_sort, source_args),
            FrontendTerm::QualifiedApp(substituted_name, substituted_sort, substituted_args),
        ) if source_name == substituted_name
            && source_sort == substituted_sort
            && source_args.len() == substituted_args.len() =>
        {
            let TermData::App(symbol, ground_args) = terms.get(ground).clone() else {
                return None;
            };
            if ground_args.len() != source_args.len() {
                return None;
            }
            let rebuilt = source_args
                .iter()
                .zip(substituted_args)
                .zip(ground_args)
                .map(|((source_arg, substituted_arg), ground_arg)| {
                    lift_surface_binders_from_ground(
                        terms,
                        source_arg,
                        substituted_arg,
                        ground_arg,
                        bound_vars,
                    )
                })
                .collect::<Option<Vec<_>>>()?;
            let sort = terms.sort(ground).clone();
            Some(terms.mk_app(symbol, rebuilt, sort))
        }
        _ => None,
    }
}

/// Check one simultaneous substitution without rebuilding through AY's
/// simplifying constructors.  This deliberately mirrors the structural
/// contract of the strict `forall_inst` checker: a raw surface comparison
/// such as `(> (f x) 0)` must remain `>` after substituting `x`, rather than
/// being canonicalized to `(< 0 (f x))` by the ordinary term builders.
fn raw_instance_matches_substitution(
    terms: &ay_core::TermStore,
    pattern: TermId,
    instance: TermId,
    substitutions: &HashMap<String, TermId>,
) -> bool {
    let mut visited = HashSet::default();
    let mut stack = vec![(pattern, instance)];
    let mut work = 0usize;
    while let Some((expected, actual)) = stack.pop() {
        if !visited.insert((expected, actual)) {
            continue;
        }
        work = work.saturating_add(1);
        if work > 100_000 || terms.sort(expected) != terms.sort(actual) {
            return false;
        }
        match terms.get(expected) {
            TermData::Var(name, _) => {
                if let Some(&replacement) = substitutions.get(name) {
                    if actual != replacement {
                        return false;
                    }
                } else if expected != actual {
                    return false;
                }
            }
            TermData::Const(..) => {
                if expected != actual {
                    return false;
                }
            }
            TermData::Not(inner) => {
                let TermData::Not(actual_inner) = terms.get(actual) else {
                    return false;
                };
                stack.push((*inner, *actual_inner));
            }
            TermData::Ite(condition, then_branch, else_branch) => {
                let TermData::Ite(actual_condition, actual_then, actual_else) = terms.get(actual)
                else {
                    return false;
                };
                stack.extend([
                    (*condition, *actual_condition),
                    (*then_branch, *actual_then),
                    (*else_branch, *actual_else),
                ]);
            }
            TermData::App(symbol, args) => {
                let TermData::App(actual_symbol, actual_args) = terms.get(actual) else {
                    return false;
                };
                if symbol != actual_symbol || args.len() != actual_args.len() {
                    return false;
                }
                stack.extend(args.iter().copied().zip(actual_args.iter().copied()));
            }
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return false,
            _ => return false,
        }
    }
    true
}

/// Surface spelling of a ground binder value (Int and Bool only — the
/// finite-domain sorts whose derivations are validated end-to-end).
/// Negative integers spell as `(- k)`, the SMT-LIB surface form.
fn value_to_surface(terms: &ay_core::TermStore, value: TermId) -> Option<FrontendTerm> {
    use ay_frontend::command::Constant as SurfaceConstant;
    match terms.get(value) {
        TermData::Const(ay_core::term::Constant::Bool(b)) => Some(FrontendTerm::Const(if *b {
            SurfaceConstant::True
        } else {
            SurfaceConstant::False
        })),
        TermData::Const(ay_core::term::Constant::Int(n)) => {
            if n.sign() == num_bigint::Sign::Minus {
                Some(FrontendTerm::App(
                    "-".to_string(),
                    vec![FrontendTerm::Const(SurfaceConstant::Numeral(
                        (-n).to_string(),
                    ))],
                ))
            } else {
                Some(FrontendTerm::Const(SurfaceConstant::Numeral(n.to_string())))
            }
        }
        _ => None,
    }
}

/// One raw conjunct of an [`AssumePlan::AndDistinct`] assume that supplies
/// canonical conjunct unit(s).
#[derive(Clone)]
struct AndDistinctUnit {
    /// Operand position in the raw conjunction (the `and_pos` index).
    pos: u32,
    /// The raw conjunct term.
    raw: TermId,
    kind: AndDistinctKind,
}

/// How an extracted raw conjunct bridges to its canonical conjunct(s).
#[derive(Clone)]
enum AndDistinctKind {
    /// The raw conjunct IS the canonical conjunct.
    Plain,
    /// Arithmetic orientation bridge: certified `[1, 1]` `la_generic` lemma
    /// over the raw literal's atom.
    Arith { atom: TermId },
    /// Binary `(distinct s t)` sugar exported as the canonical
    /// `(not (= s t))`: bridge via `distinct_elim` + `equiv_pos2`.
    DistinctBinary,
    /// N-ary `(distinct ..)` sugar exported as `count` pairwise canonical
    /// conjuncts: `distinct_elim` + `equiv_pos2` to the expansion
    /// conjunction `and_term`, then one `and_pos` per pairwise conjunct.
    DistinctNary { and_term: TermId, count: u32 },
    /// An `or`-conjunct whose canonical export REORDERED the disjuncts
    /// and/or FLIPPED individual binary-equality literals (#C2b): the raw
    /// (file-order, file-orientation) disjunction is re-interned for the
    /// assume, and its unit bridges to the canonical or-term via the `or`
    /// rule, one certified `eq_symmetric` + `equiv_pos1/2` orientation
    /// bridge per flipped literal, and the `or_neg` permutation closure
    /// (the C1 or-split reorder machinery).
    OrPerm {
        /// `(raw disjunct, canonical disjunct)` pairs in RAW disjunct
        /// order; each pair is either identical or a top-level
        /// binary-equality orientation flip (possibly under one `not`).
        lits: Vec<(TermId, TermId)>,
    },
}

/// A recognized preprocessor-derived unit trust step `(cl L)` where an
/// original disjunctive assertion (surface `(or ...)` or De Morgan
/// `(not (and ...))`) contains `L` and every OTHER disjunct is refuted by
/// its complementary original assertion. Replaced by an assume of the
/// disjunction, its `or` decomposition (the printer resugars a De Morgan
/// surface to `not_and`), and one resolution per remaining disjunct against
/// the complementary original's assume.
struct OrUnitPlan {
    /// The original disjunctive assertion (canonical or-term; prints via
    /// the surface overrides).
    orig: TermId,
    /// Its disjuncts, in canonical order (the decomposition step's clause).
    disjuncts: Vec<TermId>,
    /// Per non-`L` disjunct, in decomposition order: (resolution pivot
    /// atom, the complementary ORIGINAL assertion discharging it).
    eliminations: Vec<(TermId, TermId)>,
}

/// A singleton trust clause whose term is the canonical packed `or` form of
/// one exact authored, right-associated implication chain. The canonical
/// authored `or` is assumed and decomposed; independently checked linear
/// bridges normalize comparison literals, and `or_neg` packs the resulting
/// exact disjunct set back into the unit the existing proof consumes. The
/// Alethe printer replays that internal `or` decomposition as `implies_pos`
/// steps so the premise still prints exactly like the authored implication.
///
/// This is deliberately a source-authenticated plan, not a general
/// implication simplifier: `source_or` is the canonical half of an exact
/// authenticated `(canonical, parsed)` entry from `originals`, and every source
/// literal must align one-to-one with an exact target disjunct.
struct NormalizedAuthoredOrPlan {
    /// Canonical `(or (not A0) (not A1) ... C)` for the authored implication.
    source_or: TermId,
    /// Exact disjuncts of `source_or`.
    source_disjuncts: Vec<TermId>,
    /// Canonical packed `(or (not A0) (not A1) ... C)` consumed by the old
    /// proof's downstream steps.
    target_or: TermId,
    /// Exact canonical disjuncts of `target_or`.
    target_disjuncts: Vec<TermId>,
    /// Source literals aligned with the target disjuncts.
    literals: Vec<NormalizedAuthoredOrLiteral>,
}

struct NormalizedAuthoredOrLiteral {
    source: TermId,
    canonical: TermId,
    /// The source literal's atom when a checked two-literal LRA bridge is
    /// needed. `None` means `source == canonical`.
    bridge_atom: Option<TermId>,
}

/// A singleton packed disjunction `(or (not E) (ite G T F))` whose then arm
/// follows from two exact authored premises, the array equality `E` and guard
/// `G`, through the strict `ArrayRowChain` schema.  The else arm is irrelevant
/// once `G` is discharged; ordinary `ite_neg2` and `or_neg` steps lift the
/// certified array fact back to the original singleton term.
struct AuthoredArrayItePlan {
    target_or: TermId,
    array_equality: TermId,
    /// Raw-interned exact source spelling of the authored arithmetic guard.
    /// This remains a distinct proof premise when elaboration normalized the
    /// guard's arithmetic expression.
    guard_source: TermId,
    /// Canonical guard consumed by the certified ROW and ITE rules.
    guard: TermId,
    then_branch: TermId,
    ite_term: TermId,
    select_congruence: TermId,
    store_hit: TermId,
    congruence_clause: Vec<TermId>,
    row1_clause: Vec<TermId>,
    transitivity_clause: Vec<TermId>,
}

/// How a recognized preprocessor-derived EUF-transitivity TAUTOLOGY unit
/// `(cl T)` gets re-derived (T is an `or`-term with exactly one implied
/// positive equality disjunct). Two routes:
enum TautRoute {
    /// `T = (or .. E .. ¬e1 .. ¬en)` where the `¬e` disjuncts' equalities
    /// form a transitivity chain proving `E`: one `eq_transitive` step
    /// `(cl ¬e1 .. ¬en E)`, each `¬ei` eliminated against the `or_neg`
    /// tautology `(cl T (not ¬ei))`, closed by the `E`-position `or_neg`.
    Plain {
        /// The `¬e` disjuncts, in disjunct order (ALL of them: the chain
        /// check requires every edge on the path, mirroring the checker).
        negs: Vec<TermId>,
    },
    /// `T = (or .. E .. A ..)` where `A = (and D1 .. Dm)` and each
    /// `Dj = (or ¬f1 .. ¬fp)` is a De Morganized conjunction whose
    /// equalities chain to `E` (the eq_diamond family's shape): per `Dj` an
    /// `eq_transitive` + `or_neg` elimination derives `(cl E Dj)`, an
    /// `and_neg` step recombines them into `(cl A E)`, and the outer
    /// `or_neg` pair closes `(cl T)`.
    And {
        /// The `and`-disjunct `A`.
        and_term: TermId,
        /// `A`'s conjuncts `D1 .. Dm`, in order.
        conjs: Vec<TermId>,
        /// Per conjunct: its `¬f` disjuncts, in order (chain-verified).
        per_conj_negs: Vec<Vec<TermId>>,
    },
}

/// A recognized preprocessor-derived EUF-transitivity tautology unit: a
/// mid-proof `assume` (or premiseless unit trust step) of an `or`-term `T`
/// that is valid on its own by equality transitivity. Such leaves are
/// checker-invalid (an `assume` that matches no problem premise / an
/// unchecked trust step); the plan re-derives `(cl T)` from NOTHING with
/// certified `eq_transitive` / `or_neg` / `and_neg` / `contraction` /
/// resolution steps, and every consumer is remapped onto the derived unit
/// (same clause content, so no consumer rewiring is needed).
struct OrTautologyPlan {
    /// The tautological `or`-term `T`.
    term: TermId,
    /// The implied positive equality disjunct `E`.
    eq: TermId,
    route: TautRoute,
}

/// A recognized preprocessing-COLLAPSE equality unit `(cl (= L R))`: the
/// assertions that define `L` and `R` were substituted away by
/// substitute-and-simplify, so the equality they entail arrives as a
/// premiseless `trust` leaf with no visible premise at all.
///
/// The repair re-introduces the ORIGINAL equality assertions the collapse
/// consumed (faithful: they ARE assertions of the problem file) and closes
/// the unit against them:
///
/// ```text
/// lemma  (cl (= L R) ¬h1 .. ¬hk)     ; eq_transitive / eq_congruent recipe
/// res    (cl (= L R) ¬h2 .. ¬hk)     ; against `assume h1`
/// …
/// res    (cl (= L R))
/// ```
///
/// The lemma itself is planned by the existing EUF planner
/// ([`Executor::plan_euf_lemma`]), so congruence-through-`store`/`select`
/// (needed whenever the substituted constant sits under a function symbol) is
/// covered by the same independently re-validated toolkit, not by a second
/// bespoke prover.
#[derive(Clone)]
struct SubstEqPlan {
    /// The synthesized lemma clause `[(= L R), ¬h1, .., ¬hk]`.
    lemma: Vec<TermId>,
    /// The ORIGINAL equality assertions `h1 .. hk`, aligned with
    /// `lemma[1..]`. Each is hoisted as an `assume` and resolved away.
    hyps: Vec<TermId>,
    /// The certified derivation recipe for `lemma`.
    euf: EufLemmaPlan,
}

/// A recognized Int-trichotomy trust step and its `or`-split consumer.
struct TrichotomyPlan {
    /// Index of the `or`-split step consuming the trust step.
    or_split_idx: usize,
    /// `(= x y)`.
    eq: TermId,
    /// `(<= x y)` / `(<= y x)` (raw-interned, `la_disequality` operand order).
    le_xy: TermId,
    le_yx: TermId,
    /// Their negations (the split literals).
    not_le_xy: TermId,
    not_le_yx: TermId,
    /// `(or eq (not le_xy) (not le_yx))` — the `la_disequality` conclusion.
    or_term: TermId,
    /// The strengthened literal implied by `(not (<= y x))`
    /// (i.e. `(<= x (+ y (- 1)))` up to normalization).
    strong_from_yx: TermId,
    /// The strengthened literal implied by `(not (<= x y))`.
    strong_from_xy: TermId,
}

impl Executor {
    /// See the module docs. Returns `true` (proof swapped) only when EVERY
    /// reachable defect was repaired with a certified derivation.
    pub(in crate::executor) fn try_rebuild_with_trust_surgery(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        let source_index = OriginalSourceIndex::new(originals);
        if !source_index.is_valid() || !surgery_sources_are_bounded(&self.ctx.terms, originals) {
            return false;
        }
        let n = proof.steps.len();
        if n == 0 || n > 100_000 {
            return false;
        }
        // Subproof anchors are out of scope for index-remap surgery.
        if proof
            .steps
            .iter()
            .any(|s| matches!(s, ProofStep::Anchor { .. }))
        {
            return false;
        }

        // Only steps REACHABLE from an empty-clause step matter: dead steps
        // are never printed, so the surgery neither plans for them nor
        // copies them (a dead defective step must not veto the repair).
        let Some(live) = taut_surface::live_steps(proof) else {
            return false;
        };

        // Consumer map: step index -> indices of LIVE steps that use it.
        let mut consumers: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            match step {
                ProofStep::Step { premises, .. } => {
                    for p in premises {
                        let i = p.0 as usize;
                        if i >= n {
                            return false;
                        }
                        consumers[i].push(idx);
                    }
                }
                ProofStep::Resolution {
                    clause1, clause2, ..
                } => {
                    for p in [clause1, clause2] {
                        let i = p.0 as usize;
                        if i >= n {
                            return false;
                        }
                        consumers[i].push(idx);
                    }
                }
                _ => {}
            }
        }

        // (1) Plan every trust step. Any unrecognizable trust step aborts
        // the surgery (fail-closed). A proof with NO trust step can still be
        // defective — its assumes may be preprocessing-normalized forms no
        // checker can match to the problem premises — so a missing trust
        // anchor does not end the pass: step (2) may still find repairable
        // assumes, and the no-plans-at-all case is rejected after it.
        let mut trichotomies: HashMap<usize, TrichotomyPlan> = HashMap::default();
        let mut ite_lifts: HashMap<usize, IteLiftPlan> = HashMap::default();
        let mut provenance_ite_lifts: HashMap<usize, ProvenanceItePlan> = HashMap::default();
        let mut exact_provenance_or_assumes: HashMap<usize, TermId> = HashMap::default();
        let mut provenance_or_plans: HashMap<usize, ProvenanceOrPlan> = HashMap::default();
        let mut or_units: HashMap<usize, OrUnitPlan> = HashMap::default();
        let mut normalized_authored_ors: HashMap<usize, NormalizedAuthoredOrPlan> =
            HashMap::default();
        let mut authored_array_ites: HashMap<usize, AuthoredArrayItePlan> = HashMap::default();
        let mut taut_units: HashMap<usize, OrTautologyPlan> = HashMap::default();
        let mut euf_lemmas: HashMap<usize, EufLemmaPlan> = HashMap::default();
        let mut quant_negations: HashMap<usize, QuantNegationPlan> = HashMap::default();
        let mut quant_consequences: HashMap<usize, QuantConsequencePlan> = HashMap::default();
        let mut subst_eqs: HashMap<usize, SubstEqPlan> = HashMap::default();
        let mut deferred_leaves: HashSet<usize> = HashSet::default();
        let mut or_split_of: HashMap<usize, usize> = HashMap::default();
        let mut quant_surface_authority = quant_surface::QuantSurfaceAuthority::new(&source_index);
        let mut quant_plan_count = 0usize;
        for idx in 0..n {
            if !live[idx] {
                continue;
            }
            // A defective leaf prints as `:rule trust` from either shape:
            // a generic `Step` with the Trust rule, or a certificate-less
            // `TheoryLemma` whose kind exports as trust (the lazy-EUF lemma
            // export, #C2).
            let clause = match &proof.steps[idx] {
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    ..
                } => clause.as_slice(),
                ProofStep::TheoryLemma { kind, clause, .. } if kind.is_trust() => clause.as_slice(),
                _ => continue,
            };
            if clause.len() > MAX_PROVENANCE_REPAIR_TERMS
                || !quant_surface_authority
                    .planning_budget()
                    .spend_work(clause.len().saturating_add(1))
                || !self.spend_trust_clause_terms(clause, &mut quant_surface_authority)
            {
                return false;
            }
            if let Some(plan) = self.plan_trichotomy(proof, clause, &consumers[idx], idx) {
                or_split_of.insert(plan.or_split_idx, idx);
                trichotomies.insert(idx, plan);
            } else if let Some(plan) = self.plan_provenance_ite_lift(
                clause,
                originals,
                &source_index,
                quant_surface_authority.planning_budget(),
            ) {
                provenance_ite_lifts.insert(idx, plan);
            } else if let Some(plan) = self.plan_ite_lift(
                clause,
                originals,
                &source_index,
                quant_surface_authority.planning_budget(),
            ) {
                ite_lifts.insert(idx, plan);
            } else if let Some(plan) = self.plan_normalized_authored_or(clause, originals) {
                normalized_authored_ors.insert(idx, plan);
            } else if let Some(plan) = self.plan_authored_array_ite(clause, originals) {
                authored_array_ites.insert(idx, plan);
            } else if let Some(orig) = self.plan_exact_provenance_or_assume(
                clause,
                originals,
                &source_index,
                quant_surface_authority.planning_budget(),
            ) {
                exact_provenance_or_assumes.insert(idx, orig);
            } else if let Some(plan) = self.plan_provenance_or(
                clause,
                originals,
                &source_index,
                quant_surface_authority.planning_budget(),
            ) {
                provenance_or_plans.insert(idx, plan);
            } else if let Some(plan) = self.plan_or_unit(
                clause,
                originals,
                &source_index,
                quant_surface_authority.planning_budget(),
            ) {
                or_units.insert(idx, plan);
            } else if let Some(plan) = self.plan_or_transitivity_tautology(clause) {
                taut_units.insert(idx, plan);
            } else if let Some(plan) =
                self.plan_euf_lemma_with_budget(clause, quant_surface_authority.planning_budget())
            {
                // EUF congruence/substitution-chain lemma (bare or
                // or-wrapped), re-derived via the eq_congruent /
                // eq_transitive / eq_congruent_pred toolkit (#C2).
                euf_lemmas.insert(idx, plan);
            } else if let Some(plan) = self.plan_ematching_quant_negation(
                clause,
                originals,
                &mut quant_surface_authority,
                &mut quant_plan_count,
            ) {
                // A direct E-matching instance plus an original arithmetic
                // premise refutes the authored forall.  Rebuild the exact
                // forall_inst + Farkas chain instead of exporting trust.
                quant_negations.insert(idx, plan);
            } else if let Some(plan) = self.plan_quant_consequence(
                clause,
                originals,
                &mut quant_surface_authority,
                &mut quant_plan_count,
            ) {
                // A preprocessing-folded consequence of a quantifier-
                // expansion instance (#quant-expansion-proof): re-derived
                // from the ORIGINAL forall premise via forall_inst plus a
                // re-verified la_generic combination with the consumed
                // original premises.
                quant_consequences.insert(idx, plan);
            } else if let Some(plan) = self.plan_substituted_equality(
                clause,
                originals,
                &source_index,
                quant_surface_authority.planning_budget(),
            ) {
                // A preprocessing COLLAPSE: the assertions defining the two
                // sides were substituted away, so the equality they entail
                // arrives as a premiseless trust unit. Re-derived from the
                // ORIGINAL equality assertions with the certified EUF toolkit
                // (#array-collapse-promotion).
                subst_eqs.insert(idx, plan);
            } else if self.trust_leaf_certified_downstream(&proof.steps[idx], clause) {
                // Not a defect this pass may touch: a LATER, idempotent
                // pipeline stage re-tags this leaf into a strict-checkable
                // theory kind (see `trust_leaf_certified_downstream`). Copy it
                // through verbatim so the array backbone survives the surgery
                // that repairs the genuinely defective leaves around it.
                deferred_leaves.insert(idx);
            } else {
                return false;
            }
        }
        let has_ite_lift_plans = !ite_lifts.is_empty() || !provenance_ite_lifts.is_empty();
        let mut keeps_surface_overrides = has_ite_lift_plans
            || !normalized_authored_ors.is_empty()
            || !authored_array_ites.is_empty()
            || !or_units.is_empty()
            || !exact_provenance_or_assumes.is_empty()
            || !provenance_or_plans.is_empty()
            || !subst_eqs.is_empty()
            || !taut_units.is_empty()
            || !euf_lemmas.is_empty();
        let mut surface_audit = if keeps_surface_overrides {
            let Some(mut audit) = self.plan_retained_surface_audit(
                originals,
                &ite_lifts,
                &provenance_ite_lifts,
                &exact_provenance_or_assumes,
                &provenance_or_plans,
                &or_units,
                &subst_eqs,
            ) else {
                return false;
            };
            for plan in normalized_authored_ors.values() {
                if !audit.require_original(&mut self.ctx, originals, plan.source_or) {
                    return false;
                }
                audit.protect_operand(&mut self.ctx.terms, plan.source_or);
            }
            for plan in authored_array_ites.values() {
                if !audit.require_original(&mut self.ctx, originals, plan.array_equality)
                    || !audit.require_original_as(
                        &mut self.ctx,
                        originals,
                        plan.guard,
                        plan.guard_source,
                    )
                {
                    return false;
                }
                audit.protect_operand(&mut self.ctx.terms, plan.array_equality);
                audit.protect_operand(&mut self.ctx.terms, plan.guard_source);
            }
            // Deferred trust leaves are copied through verbatim and promoted
            // IN PLACE by the two downstream array stages: a kind retag on
            // the SAME clause term
            // (`promote_generic_theory_lemma_kinds_after_rewrite`), plus —
            // for the extensionality class — appended clause-free
            // `array_ext_diff_intro` steps whose args (witness, array_a,
            // array_b) are subterms of that clause
            // (`promote_array_extensionality_axioms`). Every term those
            // stages render therefore lies inside the leaf's clause tree.
            // Registering the clause RIGID makes the retained override map
            // provably unable to respell any of it (`validate_effective`
            // refuses a non-identity override anywhere in a rigid tree): the
            // audited replacement for the previous blanket veto on the
            // retained-overrides + deferred-leaf mix, which killed the
            // #array-collapse-promotion repair (a substituted-equality plan
            // always retains overrides, and the array backbone around it is
            // always deferred).
            for &leaf_idx in &deferred_leaves {
                let leaf_clause = match &proof.steps[leaf_idx] {
                    ProofStep::TheoryLemma { clause, .. } => clause.clone(),
                    _ => return false,
                };
                for lit in leaf_clause {
                    audit.protect_rigid_operand(&mut self.ctx.terms, lit);
                }
            }
            Some(audit)
        } else {
            None
        };
        let mut quant_source_replacements: HashMap<TermId, TermId> = HashMap::default();
        for plan in quant_negations.values() {
            if let Some(previous) =
                quant_source_replacements.insert(plan.source_quantifier, plan.forall_term)
            {
                if previous != plan.forall_term {
                    return false;
                }
            }
        }
        // The ite-lift derivation depends on the surface overrides surviving
        // (its new assume must print like the problem file), while the
        // trichotomy / assume-bridge classes purge them to protect their
        // rigid raw-interned shapes. Mixing the two disciplines in one proof
        // is unsupported: fail closed.
        // (2) Plan every assume: originals-faithful assumes are kept; the
        // two repairable classes get bridge plans; anything else that is not
        // an original assertion aborts.
        let mut assume_plans: HashMap<usize, AssumePlan> = HashMap::default();
        let mut kept_surface_sensitive_assume = false;
        let mut print_faithful_cache: HashMap<TermId, bool> = HashMap::default();
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            let ProofStep::Assume(term) = step else {
                continue;
            };
            let term = *term;
            if quant_source_replacements.contains_key(&term) {
                if !self.spend_quant_source_assume(term, &mut quant_surface_authority) {
                    return false;
                }
                continue;
            }
            if !quant_surface_authority
                .planning_budget()
                .spend_terms(&self.ctx.terms, &[term])
            {
                return false;
            }
            let Some((_, parsed)) = source_index.get(originals, term) else {
                // A mid-proof assume of a PREPROCESSOR-DERIVED formula: no
                // checker can match it to a problem premise. Repairable when
                // it is a recorded finite-domain quantifier expansion (the
                // conjuncts re-derive from the ORIGINAL forall premise,
                // #quant-expansion-proof), a self-contained EUF-transitivity
                // tautology (re-derived from nothing), or an or-wrapped EUF
                // lemma; otherwise fail closed.
                if let Some(plan) = self.classify_quant_expansion(
                    term,
                    originals,
                    &mut quant_surface_authority,
                    &mut quant_plan_count,
                ) {
                    assume_plans.insert(idx, plan);
                    continue;
                }
                if let Some(plan) = self.plan_or_transitivity_tautology(&[term]) {
                    taut_units.insert(idx, plan);
                    continue;
                }
                if let Some(plan) = self
                    .plan_euf_lemma_with_budget(&[term], quant_surface_authority.planning_budget())
                {
                    if plan.or_term().is_some() {
                        euf_lemmas.insert(idx, plan);
                        continue;
                    }
                }
                return false;
            };
            // Surface-preserving repairs (ITE and authored-OR families) keep
            // overrides: an override-covered bound already prints correctly
            // and must not acquire a raw normalization bridge. Override-
            // purging repairs require that bridge instead. Mixing the two
            // disciplines fails closed below.
            let overrides_kept = keeps_surface_overrides;
            match self.classify_assume(term, parsed, overrides_kept) {
                Ok(Some(plan)) => {
                    assume_plans.insert(idx, plan);
                }
                Ok(None) => {
                    if overrides_kept
                        && surface_audit.as_mut().is_none_or(|audit| {
                            !audit.require_original(&mut self.ctx, originals, term)
                        })
                    {
                        return false;
                    }
                    let has_surface = self
                        .last_proof_term_overrides
                        .as_ref()
                        .is_some_and(|overrides| overrides.contains_key(&term));
                    if has_surface {
                        // The surface collector installs a whole-term entry
                        // for every assertion, including terms whose raw
                        // source tree is already the canonical tree modulo
                        // binary-equality orientation (which Carcara permits
                        // implicitly). Purging those redundant spellings is
                        // harmless and is required by the ordinary
                        // trichotomy repair. Veto only when recursive raw
                        // interning proves that the surviving Assume actually
                        // depends on another rewrite (or cannot represent the
                        // source without a binder-aware derivation).
                        let print_faithful = if let Some(&cached) = print_faithful_cache.get(&term)
                        {
                            cached
                        } else {
                            if !quant_surface_authority
                                .planning_budget()
                                .spend_surface(term, parsed)
                                || !quant_surface_authority
                                    .planning_budget()
                                    .spend_terms(&self.ctx.terms, &[term])
                            {
                                return false;
                            }
                            let raw = self.raw_intern_surface(parsed);
                            let rendered = raw.map(|raw| {
                                (raw, ay_proof::format_term_alethe(&self.ctx.terms, raw))
                            });
                            let faithful = rendered.is_some_and(|(raw, rendered)| {
                                self.last_proof_term_overrides
                                    .as_ref()
                                    .and_then(|overrides| overrides.get(&term))
                                    == Some(&rendered)
                                    && eq_flip_equivalent(&self.ctx.terms, raw, term)
                            });
                            print_faithful_cache.insert(term, faithful);
                            faithful
                        };
                        kept_surface_sensitive_assume |= !print_faithful;
                    }
                }
                Err(()) => return false,
            }
        }
        // Standalone tautology/EUF plans can be discovered only while
        // classifying mid-proof assumes. They emit surface-sensitive rules
        // too, so the retained-map decision is finalized only now.
        keeps_surface_overrides |= !taut_units.is_empty() || !euf_lemmas.is_empty();
        // Trichotomy and assume-bridge repairs clear the entire surface
        // override map. A surviving original Assume that depended on one of
        // those spellings would then cease to match the authored premise
        // (implication, xor, binary-distinct, and nested-rewrite surfaces are
        // deliberately outside the bridge classifier). Keep the old proof
        // visible instead of silently stripping its premise identity.
        let has_quant_plans = !quant_negations.is_empty()
            || !quant_consequences.is_empty()
            || assume_plans
                .values()
                .any(|p| matches!(p, AssumePlan::QuantExpansion { .. }));
        let will_purge_overrides = !keeps_surface_overrides
            && subst_eqs.is_empty()
            && (!trichotomies.is_empty() || !assume_plans.is_empty() || has_quant_plans);
        if kept_surface_sensitive_assume && will_purge_overrides {
            return false;
        }
        // See the exclusivity note above: assume bridges require the override
        // purge, while ITE/authored-OR repairs retain overrides. Fail closed on
        // the mix.
        if !surface_override_policy_allows(keeps_surface_overrides, !assume_plans.is_empty()) {
            return false;
        }
        // Quant-expansion plans purge the overrides and re-collect only their
        // own re-added originals; the ite-lift / or-unit classes keep the
        // whole override map. Mixing the two disciplines is unsupported:
        // fail closed.
        // Standalone quant repair prepares its complete replacement map before
        // proof mutation.  Retained-surface repair uses a different rendering
        // discipline, so the two remain deliberately exclusive.
        //
        // A deferred leaf is UNAUDITED only when no retained-surface audit
        // exists to hold its registration: `surface_audit` is `Some` exactly
        // when the audit block above ran, and that block registers every
        // deferred leaf's full clause tree as RIGID (so `validate_effective`
        // refuses any override respelling the material the downstream
        // promotion stages re-tag or introduce). The late
        // `keeps_surface_overrides` upgrade above (taut/EUF plans discovered
        // during assume classification) happens after that block, so those
        // proofs still fail closed here.
        let has_unaudited_deferred = !deferred_leaves.is_empty() && surface_audit.is_none();
        if !retained_surface_plan_mix_is_safe(
            keeps_surface_overrides,
            has_unaudited_deferred,
            has_quant_plans,
        ) {
            return false;
        }
        if has_quant_plans
            && (!trichotomies.is_empty()
                || assume_plans
                    .values()
                    .any(|plan| !matches!(plan, AssumePlan::QuantExpansion { .. })))
        {
            return false;
        }
        // The substituted-equality repair keeps the overrides (see above), so
        // it cannot share a proof with the override-purging assume bridges or
        // the quant-expansion class either.
        if !subst_eqs.is_empty() && (!assume_plans.is_empty() || has_quant_plans) {
            return false;
        }
        if keeps_surface_overrides && !trichotomies.is_empty() {
            return false;
        }
        let mut prepared_surface_overrides = None;
        if keeps_surface_overrides {
            let mut replaced_steps = HashSet::default();
            for index in ite_lifts
                .keys()
                .chain(provenance_ite_lifts.keys())
                .chain(normalized_authored_ors.keys())
                .chain(authored_array_ites.keys())
                .chain(exact_provenance_or_assumes.keys())
                .chain(provenance_or_plans.keys())
                .chain(or_units.keys())
                .chain(taut_units.keys())
                .chain(euf_lemmas.keys())
                .chain(subst_eqs.keys())
            {
                replaced_steps.insert(*index);
            }
            let audit = surface_audit.take().unwrap_or_default();
            let Some(effective) = self.finalize_retained_surface_overrides(
                proof,
                &live,
                &replaced_steps,
                audit,
                &taut_units,
                &euf_lemmas,
            ) else {
                return false;
            };
            prepared_surface_overrides = Some(effective);
        }
        // Nothing to repair at all: keep the proof byte-identical. (The
        // trust-free defective-assume case — the caller's
        // `reachable_non_original_assume` trigger — lands here with a
        // non-empty `assume_plans` and proceeds.)
        if trichotomies.is_empty()
            && ite_lifts.is_empty()
            && provenance_ite_lifts.is_empty()
            && exact_provenance_or_assumes.is_empty()
            && provenance_or_plans.is_empty()
            && or_units.is_empty()
            && assume_plans.is_empty()
            && normalized_authored_ors.is_empty()
            && authored_array_ites.is_empty()
            && taut_units.is_empty()
            && euf_lemmas.is_empty()
            && subst_eqs.is_empty()
            && quant_negations.is_empty()
            && quant_consequences.is_empty()
        {
            return false;
        }

        // (3) Recognize the unit-extraction patterns downstream of each
        // repaired assume: `and_pos` (premiseless) resolved against the
        // assume into a unit clause. Each such resolution is re-derived; the
        // `and_pos` step itself is dropped.
        //
        // `unit_patterns`: resolution idx -> (assume idx, conjunct position).
        let mut unit_patterns: HashMap<usize, (usize, usize)> = HashMap::default();
        let mut dropped_and_pos: Vec<bool> = vec![false; n];
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            // Unit extraction appears either as a `Resolution` step or as a
            // generic `Step` with the (th_)resolution rule.
            let (clause, i1, i2) = match step {
                ProofStep::Resolution {
                    clause,
                    clause1,
                    clause2,
                    ..
                } => (clause, clause1.0 as usize, clause2.0 as usize),
                ProofStep::Step {
                    rule: AletheRule::ThResolution | AletheRule::Resolution,
                    clause,
                    premises,
                    ..
                } if premises.len() == 2 => {
                    (clause, premises[0].0 as usize, premises[1].0 as usize)
                }
                _ => continue,
            };
            if clause.len() != 1 {
                continue;
            }
            let (a_idx, p_idx) = if assume_plans.contains_key(&i1) {
                (i1, i2)
            } else if assume_plans.contains_key(&i2) {
                (i2, i1)
            } else {
                continue;
            };
            let ProofStep::Step {
                rule: AletheRule::AndPos(pos),
                premises,
                ..
            } = &proof.steps[p_idx]
            else {
                continue;
            };
            if !premises.is_empty() {
                continue;
            }
            let pos = *pos as usize;
            let conjs = match &assume_plans[&a_idx] {
                AssumePlan::Distinct { conjs, .. }
                | AssumePlan::AndBounds { conjs, .. }
                | AssumePlan::QuantExpansion { conjs, .. } => conjs,
                // An `AndDistinct` pattern is always remapped onto the plan's
                // independently derived per-conjunct unit. Even when the old
                // clause internally contains a genuine `not(and ...)`, a
                // surface override can print that literal as its De Morgan
                // disjunction, which is not a valid external `and_pos`
                // conclusion. Dropping the old premiseless tautology is safe:
                // the consumer check below requires every use to be one of
                // these exact unit-extraction patterns.
                AssumePlan::AndDistinct { conjs, .. } => conjs,
                // A `Literal` assume has no `and_pos` pattern to recognize:
                // consumers are remapped onto the derived unit directly.
                AssumePlan::Literal { .. } => continue,
            };
            if pos >= conjs.len() || conjs[pos] != clause[0] {
                return false;
            }
            unit_patterns.insert(idx, (a_idx, pos));
            dropped_and_pos[p_idx] = true;
        }
        // Every consumer of an `AndBounds` / `QuantExpansion` assume must be
        // a recognized unit pattern: the term the new assume carries differs
        // from the canonical conjunction, so no other consumer can be
        // remapped.
        for (&a_idx, plan) in &assume_plans {
            if matches!(
                plan,
                AssumePlan::AndBounds { .. } | AssumePlan::QuantExpansion { .. }
            ) && !consumers[a_idx]
                .iter()
                .all(|c| unit_patterns.contains_key(c))
            {
                return false;
            }
        }
        // Prepare the certified derivation chain for every quant-expansion
        // unit pattern up front (fail-closed: an unmatched or underivable
        // conjunct aborts the surgery and keeps the proof byte-identical).
        let mut quant_chains: HashMap<(usize, usize), QuantInstanceChain> = HashMap::default();
        {
            let mut pattern_targets = Vec::new();
            let mut seen_targets = HashSet::default();
            for &(assume_index, position) in unit_patterns.values() {
                if !matches!(
                    assume_plans.get(&assume_index),
                    Some(AssumePlan::QuantExpansion { .. })
                ) {
                    continue;
                }
                if !seen_targets.insert((assume_index, position)) {
                    continue;
                }
                if pattern_targets.len() >= quant_surface::MAX_QUANT_SURFACE_CHAINS {
                    return false;
                }
                pattern_targets.push((assume_index, position));
            }
            pattern_targets.sort_unstable();
            for (a_idx, pos) in pattern_targets {
                let Some(AssumePlan::QuantExpansion {
                    forall_term,
                    assertion_index,
                    conjs,
                    instances,
                }) = assume_plans.get(&a_idx)
                else {
                    continue;
                };
                let Some((source, parsed)) = originals.get(*assertion_index) else {
                    return false;
                };
                if source != forall_term {
                    return false;
                }
                let target = conjs[pos];
                let Some(values) = instances.get(&target).cloned() else {
                    return false;
                };
                if !quant_surface_authority.spend_chain_source(*forall_term, parsed) {
                    return false;
                }
                if !quant_surface_authority.spend_solver_attempt(&self.ctx.terms, &values) {
                    return false;
                }
                let Some(chain) = self.build_quant_instance_chain(parsed, &values, target) else {
                    return false;
                };
                quant_chains.insert((a_idx, pos), chain);
            }
        }
        // A dropped `and_pos` step must have no consumers outside its own
        // unit pattern (its literals reference terms the new proof does not
        // derive).
        for (idx, dropped) in dropped_and_pos.iter().enumerate() {
            if *dropped && !consumers[idx].iter().all(|c| unit_patterns.contains_key(c)) {
                return false;
            }
        }

        let prepared_quant_surface_overrides = if has_quant_plans {
            let Some(overrides) = self.prepare_quant_surface_overrides(
                &mut quant_surface_authority,
                proof,
                &live,
                originals,
                quant_surface::QuantSurfacePlans {
                    assumes: &assume_plans,
                    chains: &quant_chains,
                    consequences: &quant_consequences,
                    negations: &quant_negations,
                },
            ) else {
                return false;
            };
            Some(overrides)
        } else {
            None
        };

        if !volume::emitted_proof_volume_is_bounded(
            proof,
            &live,
            &self.ctx.terms,
            volume::EmittedVolumePlans {
                trichotomies: &trichotomies,
                ite_lifts: &ite_lifts,
                provenance_ite_lifts: &provenance_ite_lifts,
                exact_or_assumes: &exact_provenance_or_assumes,
                provenance_or_plans: &provenance_or_plans,
                or_units: &or_units,
                taut_units: &taut_units,
                euf_lemmas: &euf_lemmas,
                subst_eqs: &subst_eqs,
                quant_negations: &quant_negations,
                quant_consequences: &quant_consequences,
                assume_plans: &assume_plans,
                unit_patterns: &unit_patterns,
                quant_chains: &quant_chains,
            },
        ) {
            return false;
        }

        // (4) Rebuild: hoisted assumes first, then a single ordered walk
        // emitting replacement subgraphs in place and remapping premises.
        let mut new_proof = Proof::new();
        let mut map: Vec<Option<ProofId>> = vec![None; n];
        let mut assume_new_id: HashMap<usize, ProofId> = HashMap::default();
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            let ProofStep::Assume(term) = step else {
                continue;
            };
            // A tautology-planned assume is re-DERIVED, not assumed: no
            // hoisted assume for it (its unit is emitted in the walk below).
            if taut_units.contains_key(&idx) || euf_lemmas.contains_key(&idx) {
                continue;
            }
            let t = match assume_plans.get(&idx) {
                Some(AssumePlan::Distinct { raw, .. }) => *raw,
                Some(AssumePlan::AndBounds { raw_and, .. })
                | Some(AssumePlan::AndDistinct { raw_and, .. }) => *raw_and,
                Some(AssumePlan::Literal { raw, .. }) => *raw,
                Some(AssumePlan::QuantExpansion { forall_term, .. }) => *forall_term,
                None => quant_source_replacements
                    .get(term)
                    .copied()
                    .unwrap_or(*term),
            };
            let id = new_proof.add_assume(t, None);
            assume_new_id.insert(idx, id);
            if !assume_plans.contains_key(&idx) {
                map[idx] = Some(id);
            }
        }
        // The ite-lift plans re-derive from ORIGINAL assertions that the
        // preprocessor consumed: their assumes are absent from the exported
        // proof and must be added to the hoist (deduplicated across plans,
        // reusing an existing assume of the same term when present).
        let mut lift_assume: HashMap<TermId, ProofId> = HashMap::default();
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            if let ProofStep::Assume(term) = step {
                if let Some(&id) = assume_new_id.get(&idx) {
                    lift_assume.entry(*term).or_insert(id);
                }
            }
        }
        // A normalized authored-or plan assumes the exact canonical original.
        // Its surface override retains the authored implication spelling;
        // hoist and deduplicate the premise before emitting any derivation.
        for plan in normalized_authored_ors.values() {
            if !lift_assume.contains_key(&plan.source_or) {
                let id = new_proof.add_assume(plan.source_or, None);
                lift_assume.insert(plan.source_or, id);
            }
        }
        for plan in authored_array_ites.values() {
            for term in [plan.array_equality, plan.guard_source] {
                if !lift_assume.contains_key(&term) {
                    let id = new_proof.add_assume(term, None);
                    lift_assume.insert(term, id);
                }
            }
        }
        for plan in ite_lifts.values() {
            for t in std::iter::once(plan.orig).chain(plan.bound) {
                if !lift_assume.contains_key(&t) {
                    let id = new_proof.add_assume(t, None);
                    lift_assume.insert(t, id);
                }
            }
        }
        for plan in provenance_ite_lifts.values() {
            for t in std::iter::once(plan.orig).chain(plan.supports.iter().copied()) {
                if !lift_assume.contains_key(&t) {
                    let id = new_proof.add_assume(t, None);
                    lift_assume.insert(t, id);
                }
            }
        }
        for &orig in exact_provenance_or_assumes.values() {
            if !lift_assume.contains_key(&orig) {
                let id = new_proof.add_assume(orig, None);
                lift_assume.insert(orig, id);
            }
        }
        for plan in provenance_or_plans.values() {
            for &source in plan.authored_sources() {
                if !lift_assume.contains_key(&source) {
                    let id = new_proof.add_assume(source, None);
                    lift_assume.insert(source, id);
                }
            }
        }
        for plan in or_units.values() {
            for t in
                std::iter::once(plan.orig).chain(plan.eliminations.iter().map(|&(_, comp)| comp))
            {
                if !lift_assume.contains_key(&t) {
                    let id = new_proof.add_assume(t, None);
                    lift_assume.insert(t, id);
                }
            }
        }
        // The substituted-equality repair's premises are ORIGINAL assertions
        // the preprocessor consumed: they carry no `assume` in the exported
        // proof and must be hoisted HERE, into the assumption prologue, before
        // any step is emitted (Alethe requires every `assume` to precede the
        // first `step`; an inline re-introduction makes carcara warn and is
        // not well-formed).
        let mut subst_plans: Vec<&SubstEqPlan> = subst_eqs.values().collect();
        subst_plans.sort_by_key(|p| p.lemma[0]);
        for plan in subst_plans {
            for &h in &plan.hyps {
                if !lift_assume.contains_key(&h) {
                    let id = new_proof.add_assume(h, None);
                    lift_assume.insert(h, id);
                }
            }
        }
        // Quant-expansion assumes were hoisted as the ORIGINAL forall term:
        // register them under that term so consequence plans can share them,
        // then hoist any forall/support original absent from the old proof.
        for (idx, plan) in &assume_plans {
            if let AssumePlan::QuantExpansion { forall_term, .. } = plan {
                if let Some(&id) = assume_new_id.get(idx) {
                    lift_assume.entry(*forall_term).or_insert(id);
                }
            }
        }
        for plan in quant_consequences.values() {
            for term in std::iter::once(plan.forall_term).chain(plan.supports.iter().copied()) {
                if !lift_assume.contains_key(&term) {
                    let id = new_proof.add_assume(term, None);
                    lift_assume.insert(term, id);
                }
            }
        }
        for plan in quant_negations.values() {
            for &support in &plan.supports {
                if !lift_assume.contains_key(&support) {
                    let id = new_proof.add_assume(support, None);
                    lift_assume.insert(support, id);
                }
            }
        }

        // Derived `(cl <conjunction>)` unit per Distinct assume.
        let mut distinct_unit: HashMap<usize, ProofId> = HashMap::default();
        // Derived per-canonical-conjunct units per AndDistinct assume (the
        // targets of that plan's recognized unit patterns).
        let mut anddistinct_units: HashMap<usize, Vec<ProofId>> = HashMap::default();
        // Derived 3-literal strengthened clause per trust step.
        let mut trichotomy_clause: HashMap<usize, ProofId> = HashMap::default();
        // Derived `(cl T)` tautology unit per tautological or-term (shared
        // when several defective leaves carry the same term).
        let mut taut_unit_of_term: HashMap<TermId, ProofId> = HashMap::default();
        // Same sharing for the or-wrapped EUF-lemma units.
        let mut euf_unit_of_term: HashMap<TermId, ProofId> = HashMap::default();
        // Derived quant-expansion instance units, shared per (assume, pos).
        let mut quant_units_emitted: HashMap<(usize, usize), ProofId> = HashMap::default();

        for idx in 0..n {
            if !live[idx] || dropped_and_pos[idx] {
                continue;
            }
            if let Some(&trust_idx) = or_split_of.get(&idx) {
                // The or-split consumer is rewired onto the derived clause.
                map[idx] = trichotomy_clause.get(&trust_idx).copied();
                if map[idx].is_none() {
                    return false;
                }
                continue;
            }
            if let Some(plan) = trichotomies.get(&idx) {
                // la_disequality -> or -> two certified strengthening
                // lemmas -> the 3-literal strengthened clause.
                let la = new_proof.add_rule_step(
                    AletheRule::LaDisequality,
                    vec![plan.or_term],
                    Vec::new(),
                    Vec::new(),
                );
                let or_step = new_proof.add_rule_step(
                    AletheRule::Or,
                    vec![plan.eq, plan.not_le_xy, plan.not_le_yx],
                    vec![la],
                    Vec::new(),
                );
                let lem_yx = Self::add_pair_lemma(&mut new_proof, plan.strong_from_yx, plan.le_yx);
                let r1 = new_proof.add_resolution(
                    vec![plan.eq, plan.not_le_xy, plan.strong_from_yx],
                    plan.le_yx,
                    or_step,
                    lem_yx,
                );
                let lem_xy = Self::add_pair_lemma(&mut new_proof, plan.strong_from_xy, plan.le_xy);
                let r2 = new_proof.add_resolution(
                    vec![plan.eq, plan.strong_from_yx, plan.strong_from_xy],
                    plan.le_xy,
                    r1,
                    lem_xy,
                );
                trichotomy_clause.insert(idx, r2);
                // The trust step itself is never referenced by anything but
                // its or-split (verified during planning): no mapping.
                continue;
            }
            if let Some(plan) = provenance_ite_lifts.get(&idx) {
                let surface = prepared_surface_overrides.as_ref();
                let Some(derived) = self.emit_ite_lift(&mut new_proof, plan, &lift_assume, surface)
                else {
                    return false;
                };
                map[idx] = Some(derived);
                continue;
            }
            if let Some(orig) = exact_provenance_or_assumes.get(&idx) {
                let Some(&assume_id) = lift_assume.get(orig) else {
                    return false;
                };
                map[idx] = Some(assume_id);
                continue;
            }
            if let Some(plan) = provenance_or_plans.get(&idx) {
                let Some(derived) = self.emit_provenance_or(&mut new_proof, plan, &lift_assume)
                else {
                    return false;
                };
                map[idx] = Some(derived);
                continue;
            }
            if let Some(plan) = ite_lifts.get(&idx) {
                let Some(&assume_id) = lift_assume.get(&plan.orig) else {
                    return false;
                };
                let not_intro_eq = self.ctx.terms.mk_not_raw(plan.intro_eq);
                let not_orig = self.ctx.terms.mk_not_raw(plan.orig);
                let not_cond = self.ctx.terms.mk_not_raw(plan.cond);
                let not_eq_then = self.ctx.terms.mk_not_raw(plan.eq_then);
                let not_eq_else = self.ctx.terms.mk_not_raw(plan.eq_else);
                let not_lifted_then = complement_of(&mut self.ctx.terms, plan.lifted_then);
                let not_lifted_else = complement_of(&mut self.ctx.terms, plan.lifted_else);

                // ite_intro ⊢ (cl (= P (and P (ite c (= s u) (= s v)))))
                let intro = new_proof.add_rule_step(
                    AletheRule::IteIntro,
                    vec![plan.intro_eq],
                    Vec::new(),
                    Vec::new(),
                );
                let ep = new_proof.add_rule_step(
                    AletheRule::EquivPos2,
                    vec![not_intro_eq, not_orig, plan.and_term],
                    Vec::new(),
                    Vec::new(),
                );
                let r_eq = new_proof.add_resolution(
                    vec![not_orig, plan.and_term],
                    plan.intro_eq,
                    ep,
                    intro,
                );
                let r_and =
                    new_proof.add_resolution(vec![plan.and_term], plan.orig, r_eq, assume_id);
                let not_and = self.ctx.terms.mk_not_raw(plan.and_term);
                let ap = new_proof.add_rule_step(
                    AletheRule::AndPos(1),
                    vec![not_and, plan.ite_def],
                    Vec::new(),
                    Vec::new(),
                );
                let r_def = new_proof.add_resolution(vec![plan.ite_def], plan.and_term, ap, r_and);
                // ite2 ⊢ (cl (not c) (= s u)); ite1 ⊢ (cl c (= s v))
                let it2 = new_proof.add_rule_step(
                    AletheRule::Ite2,
                    vec![not_cond, plan.eq_then],
                    vec![r_def],
                    Vec::new(),
                );
                let it1 = new_proof.add_rule_step(
                    AletheRule::Ite1,
                    vec![plan.cond, plan.eq_else],
                    vec![r_def],
                    Vec::new(),
                );
                // Certified opaque-atom transfer lemmas (validated during
                // planning): (cl (not (= s u)) (not P) A) and the else twin.
                // The defined-equality variant carries the bound original as
                // a fourth literal, discharged by its own assume below.
                let bound_info = match plan.bound {
                    None => None,
                    Some(bound) => {
                        let Some(&bound_assume) = lift_assume.get(&bound) else {
                            return false;
                        };
                        let not_bound = self.ctx.terms.mk_not_raw(bound);
                        Some((bound, not_bound, bound_assume))
                    }
                };
                let (b_then, b_else) = Self::add_ite_transfer_lemmas(
                    &mut new_proof,
                    plan,
                    not_eq_then,
                    not_eq_else,
                    not_orig,
                    bound_info.map(|(_, not_bound, _)| not_bound),
                );
                // ite_neg2 ⊢ (cl G (not c) (not A)); ite_neg1 ⊢ (cl G c (not B))
                let n2 = new_proof.add_rule_step(
                    AletheRule::IteNeg2,
                    vec![plan.goal, not_cond, not_lifted_then],
                    Vec::new(),
                    Vec::new(),
                );
                let n1 = new_proof.add_rule_step(
                    AletheRule::IteNeg1,
                    vec![plan.goal, plan.cond, not_lifted_else],
                    Vec::new(),
                    Vec::new(),
                );
                let bound_tail = |lits: &[TermId]| -> Vec<TermId> {
                    let mut lits = lits.to_vec();
                    if let Some((_, not_bound, _)) = bound_info {
                        lits.push(not_bound);
                    }
                    lits
                };
                let g1 = new_proof.add_resolution(
                    bound_tail(&[plan.goal, not_cond, not_eq_then, not_orig]),
                    plan.lifted_then,
                    n2,
                    b_then,
                );
                let g2 = new_proof.add_resolution(
                    bound_tail(&[plan.goal, not_cond, not_orig]),
                    plan.eq_then,
                    g1,
                    it2,
                );
                let mut g3 = new_proof.add_resolution(
                    bound_tail(&[plan.goal, not_cond]),
                    plan.orig,
                    g2,
                    assume_id,
                );
                if let Some((bound, _, bound_assume)) = bound_info {
                    g3 = new_proof.add_resolution(
                        vec![plan.goal, not_cond],
                        bound,
                        g3,
                        bound_assume,
                    );
                }
                let h1 = new_proof.add_resolution(
                    bound_tail(&[plan.goal, plan.cond, not_eq_else, not_orig]),
                    plan.lifted_else,
                    n1,
                    b_else,
                );
                let h2 = new_proof.add_resolution(
                    bound_tail(&[plan.goal, plan.cond, not_orig]),
                    plan.eq_else,
                    h1,
                    it1,
                );
                let mut h3 = new_proof.add_resolution(
                    bound_tail(&[plan.goal, plan.cond]),
                    plan.orig,
                    h2,
                    assume_id,
                );
                if let Some((bound, _, bound_assume)) = bound_info {
                    h3 = new_proof.add_resolution(
                        vec![plan.goal, plan.cond],
                        bound,
                        h3,
                        bound_assume,
                    );
                }
                let g = new_proof.add_resolution(vec![plan.goal], plan.cond, g3, h3);
                map[idx] = Some(g);
                continue;
            }
            if let Some(plan) = or_units.get(&idx) {
                let Some(&assume_id) = lift_assume.get(&plan.orig) else {
                    return false;
                };
                // Decompose the disjunction, then eliminate every non-unit
                // disjunct against its complementary original's assume.
                let mut cur = new_proof.add_rule_step(
                    AletheRule::Or,
                    plan.disjuncts.clone(),
                    vec![assume_id],
                    Vec::new(),
                );
                let mut remaining = plan.disjuncts.clone();
                for &(pivot, comp) in &plan.eliminations {
                    let Some(&comp_assume) = lift_assume.get(&comp) else {
                        return false;
                    };
                    remaining.retain(|&l| atom_of(&self.ctx.terms, l) != pivot);
                    cur = new_proof.add_resolution(remaining.clone(), pivot, cur, comp_assume);
                }
                map[idx] = Some(cur);
                continue;
            }
            if let Some(plan) = normalized_authored_ors.get(&idx) {
                let Some(&assume_id) = lift_assume.get(&plan.source_or) else {
                    return false;
                };
                let Some(unit) = self.emit_normalized_authored_or(&mut new_proof, plan, assume_id)
                else {
                    return false;
                };
                map[idx] = Some(unit);
                continue;
            }
            if let Some(plan) = authored_array_ites.get(&idx) {
                let (Some(&equality_assume), Some(&guard_assume)) = (
                    lift_assume.get(&plan.array_equality),
                    lift_assume.get(&plan.guard_source),
                ) else {
                    return false;
                };
                let Some(unit) = self.emit_authored_array_ite(
                    &mut new_proof,
                    plan,
                    equality_assume,
                    guard_assume,
                ) else {
                    return false;
                };
                map[idx] = Some(unit);
                continue;
            }
            if let Some(plan) = taut_units.get(&idx) {
                let unit = match taut_unit_of_term.get(&plan.term) {
                    Some(&u) => u,
                    None => {
                        let u = self.emit_or_tautology_derivation(&mut new_proof, plan);
                        taut_unit_of_term.insert(plan.term, u);
                        u
                    }
                };
                map[idx] = Some(unit);
                continue;
            }
            if let Some(plan) = euf_lemmas.get(&idx) {
                let plan = plan.clone();
                let unit = match plan
                    .or_term()
                    .and_then(|t| euf_unit_of_term.get(&t).copied())
                {
                    Some(u) => u,
                    None => {
                        let u = self.emit_euf_lemma(&mut new_proof, &plan);
                        if let Some(t) = plan.or_term() {
                            euf_unit_of_term.insert(t, u);
                        }
                        u
                    }
                };
                map[idx] = Some(unit);
                continue;
            }
            if let Some(plan) = subst_eqs.get(&idx).cloned() {
                // The certified EUF lemma over the re-introduced ORIGINAL
                // equalities, closed by one resolution per hypothesis.
                let Some(unit) =
                    self.emit_substituted_equality(&mut new_proof, &plan, &lift_assume)
                else {
                    return false;
                };
                map[idx] = Some(unit);
                continue;
            }
            if let Some(plan) = quant_negations.get(&idx) {
                let Some(unit) =
                    self.emit_ematching_quant_negation(&mut new_proof, plan, &lift_assume)
                else {
                    return false;
                };
                map[idx] = Some(unit);
                continue;
            }
            if let Some(plan) = quant_consequences.get(&idx) {
                let Some(&assume_id) = lift_assume.get(&plan.forall_term) else {
                    return false;
                };
                let inst_unit = self.emit_quant_instance_chain(
                    &mut new_proof,
                    plan.forall_term,
                    assume_id,
                    &plan.chain,
                );
                #[allow(clippy::cast_possible_truncation)]
                let coeffs = vec![1i64; plan.lemma.len()];
                let lemma_id = new_proof.add_step(ProofStep::TheoryLemma {
                    theory: "LRA".to_string(),
                    clause: plan.lemma.clone(),
                    farkas: Some(FarkasAnnotation::from_ints(&coeffs)),
                    kind: TheoryLemmaKind::LraFarkas,
                    lia: None,
                });
                let inst_pivot = atom_of(&self.ctx.terms, plan.chain.target);
                let mut current = new_proof.add_resolution(
                    plan.lemma[1..].to_vec(),
                    inst_pivot,
                    lemma_id,
                    inst_unit,
                );
                for (index, &support) in plan.supports.iter().enumerate() {
                    let Some(&support_id) = lift_assume.get(&support) else {
                        return false;
                    };
                    let pivot = atom_of(&self.ctx.terms, support);
                    current = new_proof.add_resolution(
                        plan.lemma[index + 2..].to_vec(),
                        pivot,
                        current,
                        support_id,
                    );
                }
                map[idx] = Some(current);
                continue;
            }
            if let Some(&(a_idx, pos)) = unit_patterns.get(&idx) {
                let Some(&assume_id) = assume_new_id.get(&a_idx) else {
                    return false;
                };
                let unit = match &assume_plans[&a_idx] {
                    AssumePlan::Distinct {
                        and_term, conjs, ..
                    } => {
                        let Some(&and_unit) = distinct_unit.get(&a_idx) else {
                            return false;
                        };
                        let (and_term, conj) = (*and_term, conjs[pos]);
                        let not_and = self.ctx.terms.mk_not_raw(and_term);
                        #[allow(clippy::cast_possible_truncation)]
                        let p = new_proof.add_rule_step(
                            AletheRule::AndPos(pos as u32),
                            vec![not_and, conj],
                            Vec::new(),
                            Vec::new(),
                        );
                        new_proof.add_resolution(vec![conj], and_term, p, and_unit)
                    }
                    AssumePlan::AndBounds {
                        raw_and,
                        raws,
                        conjs,
                    } => {
                        let (raw_and, conj) = (*raw_and, conjs[pos]);
                        let (raw, bridge_atom) = raws[pos];
                        let not_raw_and = self.ctx.terms.mk_not_raw(raw_and);
                        #[allow(clippy::cast_possible_truncation)]
                        let p = new_proof.add_rule_step(
                            AletheRule::AndPos(pos as u32),
                            vec![not_raw_and, raw],
                            Vec::new(),
                            Vec::new(),
                        );
                        let u0 = new_proof.add_resolution(vec![raw], raw_and, p, assume_id);
                        match bridge_atom {
                            None => u0,
                            Some(atom) => {
                                let raw_complement = complement_of(&mut self.ctx.terms, raw);
                                let lemma =
                                    Self::add_pair_lemma(&mut new_proof, conj, raw_complement);
                                new_proof.add_resolution(vec![conj], atom, lemma, u0)
                            }
                        }
                    }
                    AssumePlan::AndDistinct { .. } => {
                        // The plan's per-conjunct units were derived when the
                        // assume itself was walked (assume idx < consumer idx).
                        let Some(units) = anddistinct_units.get(&a_idx) else {
                            return false;
                        };
                        let Some(&unit) = units.get(pos) else {
                            return false;
                        };
                        unit
                    }
                    AssumePlan::QuantExpansion { forall_term, .. } => {
                        // Derive (once per conjunct) the unit from the
                        // ORIGINAL forall's assume via the plan-time-built
                        // forall_inst chain (#quant-expansion-proof).
                        let forall_term = *forall_term;
                        if let Some(&unit) = quant_units_emitted.get(&(a_idx, pos)) {
                            unit
                        } else {
                            let Some(chain) = quant_chains.get(&(a_idx, pos)) else {
                                return false;
                            };
                            let unit = self.emit_quant_instance_chain(
                                &mut new_proof,
                                forall_term,
                                assume_id,
                                chain,
                            );
                            quant_units_emitted.insert((a_idx, pos), unit);
                            unit
                        }
                    }
                    // Unit patterns are never planned against a `Literal`
                    // assume (step 3 skips it).
                    AssumePlan::Literal { .. } => return false,
                };
                map[idx] = Some(unit);
                continue;
            }
            match &proof.steps[idx] {
                ProofStep::Assume(_) => {
                    let Some(plan) = assume_plans.get(&idx) else {
                        continue; // faithful assume, already mapped
                    };
                    match plan {
                        AssumePlan::Distinct {
                            raw,
                            and_term,
                            conjs: _,
                        } => {
                            let (raw, and_term) = (*raw, *and_term);
                            let Some(&assume_id) = assume_new_id.get(&idx) else {
                                return false;
                            };
                            let equiv = self.ctx.terms.mk_app(
                                Symbol::named("="),
                                [raw, and_term],
                                Sort::Bool,
                            );
                            let not_equiv = self.ctx.terms.mk_not_raw(equiv);
                            let not_raw = self.ctx.terms.mk_not_raw(raw);
                            let de = new_proof.add_rule_step(
                                AletheRule::DistinctElim,
                                vec![equiv],
                                Vec::new(),
                                Vec::new(),
                            );
                            let ep = new_proof.add_rule_step(
                                AletheRule::EquivPos2,
                                vec![not_equiv, not_raw, and_term],
                                Vec::new(),
                                Vec::new(),
                            );
                            let r1 =
                                new_proof.add_resolution(vec![not_raw, and_term], equiv, ep, de);
                            let unit = new_proof.add_resolution(vec![and_term], raw, r1, assume_id);
                            distinct_unit.insert(idx, unit);
                            map[idx] = Some(unit);
                        }
                        AssumePlan::AndBounds { .. } => {
                            // Consumers were all verified to be unit
                            // patterns; the raw assume itself was already
                            // emitted in the hoist. Nothing to map.
                        }
                        AssumePlan::QuantExpansion { .. } => {
                            // Same discipline as AndBounds: every consumer is
                            // a unit pattern re-derived from the hoisted
                            // ORIGINAL forall assume. Nothing to map.
                        }
                        AssumePlan::AndDistinct {
                            raw_and,
                            and_term,
                            units,
                            conjs,
                        } => {
                            // Re-derive the canonical conjunction as a unit:
                            // extract every contributing raw conjunct, bridge
                            // the sugared ones, close with `and_neg`; every
                            // consumer is remapped onto the derived unit.
                            let (raw_and, and_term) = (*raw_and, *and_term);
                            let (units, conjs) = (units.clone(), conjs.clone());
                            let Some(&assume_id) = assume_new_id.get(&idx) else {
                                return false;
                            };
                            let not_raw_and = self.ctx.terms.mk_not_raw(raw_and);
                            let mut unit_ids: Vec<ProofId> = Vec::with_capacity(conjs.len());
                            let mut k = 0usize;
                            for u in &units {
                                let p = new_proof.add_rule_step(
                                    AletheRule::AndPos(u.pos),
                                    vec![not_raw_and, u.raw],
                                    Vec::new(),
                                    Vec::new(),
                                );
                                let u0 =
                                    new_proof.add_resolution(vec![u.raw], raw_and, p, assume_id);
                                match &u.kind {
                                    AndDistinctKind::Plain => {
                                        unit_ids.push(u0);
                                        k += 1;
                                    }
                                    AndDistinctKind::Arith { atom } => {
                                        let atom = *atom;
                                        let conj = conjs[k];
                                        let raw_complement =
                                            complement_of(&mut self.ctx.terms, u.raw);
                                        let lemma = Self::add_pair_lemma(
                                            &mut new_proof,
                                            conj,
                                            raw_complement,
                                        );
                                        unit_ids.push(new_proof.add_resolution(
                                            vec![conj],
                                            atom,
                                            lemma,
                                            u0,
                                        ));
                                        k += 1;
                                    }
                                    AndDistinctKind::DistinctBinary => {
                                        let conj = conjs[k];
                                        let equiv = self.ctx.terms.mk_app(
                                            Symbol::named("="),
                                            [u.raw, conj],
                                            Sort::Bool,
                                        );
                                        let not_equiv = self.ctx.terms.mk_not_raw(equiv);
                                        let not_raw = self.ctx.terms.mk_not_raw(u.raw);
                                        let de = new_proof.add_rule_step(
                                            AletheRule::DistinctElim,
                                            vec![equiv],
                                            Vec::new(),
                                            Vec::new(),
                                        );
                                        let ep = new_proof.add_rule_step(
                                            AletheRule::EquivPos2,
                                            vec![not_equiv, not_raw, conj],
                                            Vec::new(),
                                            Vec::new(),
                                        );
                                        let r1 = new_proof.add_resolution(
                                            vec![not_raw, conj],
                                            equiv,
                                            ep,
                                            de,
                                        );
                                        unit_ids.push(new_proof.add_resolution(
                                            vec![conj],
                                            u.raw,
                                            r1,
                                            u0,
                                        ));
                                        k += 1;
                                    }
                                    AndDistinctKind::DistinctNary {
                                        and_term: block,
                                        count,
                                    } => {
                                        let (block, count) = (*block, *count);
                                        let equiv = self.ctx.terms.mk_app(
                                            Symbol::named("="),
                                            [u.raw, block],
                                            Sort::Bool,
                                        );
                                        let not_equiv = self.ctx.terms.mk_not_raw(equiv);
                                        let not_raw = self.ctx.terms.mk_not_raw(u.raw);
                                        let not_block = self.ctx.terms.mk_not_raw(block);
                                        let de = new_proof.add_rule_step(
                                            AletheRule::DistinctElim,
                                            vec![equiv],
                                            Vec::new(),
                                            Vec::new(),
                                        );
                                        let ep = new_proof.add_rule_step(
                                            AletheRule::EquivPos2,
                                            vec![not_equiv, not_raw, block],
                                            Vec::new(),
                                            Vec::new(),
                                        );
                                        let r1 = new_proof.add_resolution(
                                            vec![not_raw, block],
                                            equiv,
                                            ep,
                                            de,
                                        );
                                        let block_unit =
                                            new_proof.add_resolution(vec![block], u.raw, r1, u0);
                                        for j in 0..count {
                                            let conj = conjs[k];
                                            let ap = new_proof.add_rule_step(
                                                AletheRule::AndPos(j),
                                                vec![not_block, conj],
                                                Vec::new(),
                                                Vec::new(),
                                            );
                                            unit_ids.push(new_proof.add_resolution(
                                                vec![conj],
                                                block,
                                                ap,
                                                block_unit,
                                            ));
                                            k += 1;
                                        }
                                    }
                                    AndDistinctKind::OrPerm { lits } => {
                                        // (cl r_1 .. r_n) from the raw unit
                                        // (full duplicate-preserving disjunct
                                        // list), contracted to the unique
                                        // literals the alignment covers.
                                        let conj = conjs[k];
                                        let TermData::App(_, full) = self.ctx.terms.get(u.raw)
                                        else {
                                            return false;
                                        };
                                        let full = full.clone();
                                        let mut clause: Vec<TermId> =
                                            lits.iter().map(|&(r, _)| r).collect();
                                        let mut cur = new_proof.add_rule_step(
                                            AletheRule::Or,
                                            full.clone(),
                                            vec![u0],
                                            Vec::new(),
                                        );
                                        if full.len() != clause.len() {
                                            cur = new_proof.add_rule_step(
                                                AletheRule::Contraction,
                                                clause.clone(),
                                                vec![cur],
                                                Vec::new(),
                                            );
                                        }
                                        // Flip each misoriented literal via a
                                        // certified eq_symmetric bridge.
                                        for (i, &(r, c)) in lits.iter().enumerate() {
                                            if r == c {
                                                continue;
                                            }
                                            let (pivot, bridge) =
                                                self.add_eq_flip_bridge(&mut new_proof, r, c);
                                            clause[i] = c;
                                            cur = new_proof.add_resolution(
                                                clause.clone(),
                                                pivot,
                                                cur,
                                                bridge,
                                            );
                                        }
                                        // or_neg permutation closure onto the
                                        // canonical or-term.
                                        for &(_, c) in lits.iter() {
                                            let not_c = self.ctx.terms.mk_not_raw(c);
                                            let on = new_proof.add_rule_step(
                                                AletheRule::OrNeg,
                                                vec![conj, not_c],
                                                Vec::new(),
                                                Vec::new(),
                                            );
                                            if let Some(p) = clause.iter().position(|&l| l == c) {
                                                // Resolution surgery: the removed
                                                // literal is the pivot `c`, already
                                                // in hand — its id is not needed.
                                                let _ = clause.remove(p);
                                            }
                                            clause.push(conj);
                                            cur = new_proof.add_resolution(
                                                clause.clone(),
                                                c,
                                                cur,
                                                on,
                                            );
                                        }
                                        unit_ids.push(new_proof.add_rule_step(
                                            AletheRule::Contraction,
                                            vec![conj],
                                            vec![cur],
                                            Vec::new(),
                                        ));
                                        k += 1;
                                    }
                                }
                            }
                            if k != conjs.len() || unit_ids.len() != conjs.len() {
                                return false;
                            }
                            anddistinct_units.insert(idx, unit_ids.clone());
                            let mut clause: Vec<TermId> = Vec::with_capacity(conjs.len() + 1);
                            clause.push(and_term);
                            for &c in &conjs {
                                clause.push(self.ctx.terms.mk_not_raw(c));
                            }
                            let mut cur = new_proof.add_rule_step(
                                AletheRule::AndNeg,
                                clause.clone(),
                                Vec::new(),
                                Vec::new(),
                            );
                            for (&conj, &unit) in conjs.iter().zip(unit_ids.iter()) {
                                let not_conj = self.ctx.terms.mk_not_raw(conj);
                                if let Some(pos) = clause.iter().position(|&l| l == not_conj) {
                                    let _ = clause.remove(pos);
                                }
                                cur = new_proof.add_resolution(clause.clone(), conj, cur, unit);
                            }
                            map[idx] = Some(cur);
                        }
                        AssumePlan::Literal {
                            raw,
                            atom,
                            canonical,
                        } => {
                            // Certified orientation bridge (validated during
                            // planning): (cl canonical (not raw)) resolved
                            // against the raw assume yields the canonical
                            // unit every downstream consumer expects.
                            let (raw, atom, canonical) = (*raw, *atom, *canonical);
                            let Some(&assume_id) = assume_new_id.get(&idx) else {
                                return false;
                            };
                            let raw_complement = complement_of(&mut self.ctx.terms, raw);
                            let lemma =
                                Self::add_pair_lemma(&mut new_proof, canonical, raw_complement);
                            let unit =
                                new_proof.add_resolution(vec![canonical], atom, lemma, assume_id);
                            map[idx] = Some(unit);
                        }
                    }
                }
                ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => {
                    let mut new_premises = Vec::with_capacity(premises.len());
                    for p in premises {
                        let Some(mapped) = map[p.0 as usize] else {
                            return false;
                        };
                        new_premises.push(mapped);
                    }
                    // An `or` decomposition of a re-derived tautology unit
                    // may list the disjuncts in a scrambled (solver-trail)
                    // order that the Alethe `or` rule rejects: reorder the
                    // clause to the or-term's own disjunct order when it is
                    // a permutation of it (set-equivalent, so every
                    // downstream resolution still checks), fail-closed
                    // otherwise.
                    let mut clause = clause.clone();
                    if matches!(rule, AletheRule::Or) && premises.len() == 1 {
                        let src = premises[0].0 as usize;
                        let taut_term = taut_units
                            .get(&src)
                            .map(|plan| plan.term)
                            .or_else(|| euf_lemmas.get(&src).and_then(EufLemmaPlan::or_term));
                        if let Some(taut_term) = taut_term {
                            let TermData::App(Symbol::Named(op), disjuncts) =
                                self.ctx.terms.get(taut_term)
                            else {
                                return false;
                            };
                            if op != "or" {
                                return false;
                            }
                            let disjuncts = disjuncts.clone();
                            let mut want = disjuncts.clone();
                            let mut have = clause.clone();
                            want.sort_unstable();
                            have.sort_unstable();
                            if want != have {
                                return false;
                            }
                            clause = disjuncts;
                        }
                    }
                    let id =
                        new_proof.add_rule_step(rule.clone(), clause, new_premises, args.clone());
                    map[idx] = Some(id);
                }
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => {
                    let (Some(c1), Some(c2)) = (map[clause1.0 as usize], map[clause2.0 as usize])
                    else {
                        return false;
                    };
                    let pivot = quant_source_replacements
                        .get(pivot)
                        .copied()
                        .unwrap_or(*pivot);
                    let id = new_proof.add_resolution(clause.clone(), pivot, c1, c2);
                    map[idx] = Some(id);
                }
                ProofStep::TheoryLemma { .. } => {
                    let id = new_proof.add_step(proof.steps[idx].clone());
                    map[idx] = Some(id);
                }
                _ => return false,
            }
        }

        // (5) The rebuilt proof must be trust-free (that was the point) —
        // except for the leaves a LATER export stage certifies in place, which
        // this pass deliberately copied through. Those are re-checked with the
        // same predicate on the REBUILT step list, so a copy that lost the
        // shape (or a leaf that only looked deferred-certifiable before the
        // rebuild) still fails closed.
        let report = ay_proof::terminal_trust_report(&new_proof);
        if report.trust_rule_on_path > 0 || report.trust_theory_lemma_on_path > 0 {
            if deferred_leaves.is_empty() || report.trust_rule_on_path > 0 {
                return false;
            }
            let Some(live_new) = taut_surface::live_steps(&new_proof) else {
                return false;
            };
            for (i, step) in new_proof.steps.iter().enumerate() {
                if !live_new[i] {
                    continue;
                }
                let clause = match step {
                    ProofStep::TheoryLemma { kind, clause, .. } if kind.is_trust() => {
                        clause.clone()
                    }
                    _ => continue,
                };
                if !self.trust_leaf_certified_downstream(&new_proof.steps[i], &clause) {
                    return false;
                }
            }
        }

        // (5b) EUF-lemma surgeries re-validate the WHOLE rebuilt proof with
        // the strict checker before swapping it in: any construction miss
        // keeps the original proof (fail-closed; USER LAW: never a wrong
        // proof step).
        let has_or_perm = assume_plans.values().any(|p| {
            matches!(p, AssumePlan::AndDistinct { units, .. }
                if units.iter().any(|u| matches!(u.kind, AndDistinctKind::OrPerm { .. })))
        });
        // The two classes added for the array collapse — a copied-through
        // deferred leaf and a re-derived substituted equality — are gated the
        // same way. A deferred leaf especially: without a whole-proof check
        // this pass would hand the export a `Generic` leaf on nothing but a
        // PREDICTION that a later stage re-tags it, and a wrong prediction
        // would publish an unproved step where the pre-existing rebuild
        // backbones (which run only if this pass declines) would have produced
        // a certified one.
        if !euf_lemmas.is_empty()
            || has_or_perm
            || !deferred_leaves.is_empty()
            || !subst_eqs.is_empty()
            || !normalized_authored_ors.is_empty()
            || !authored_array_ites.is_empty()
            || has_quant_plans
            || has_ite_lift_plans
            || !exact_provenance_or_assumes.is_empty()
            || !provenance_or_plans.is_empty()
            || !or_units.is_empty()
        {
            // Deferred-certified leaves are still `Generic` at this point in
            // the pipeline, and the strict checker rightly refuses that kind.
            // Validate a COPY on which the two downstream stages have already
            // run — exactly the document the export will produce — so the gate
            // measures the real thing instead of an intermediate shape. The
            // copy is discarded; `new_proof` is swapped in unchanged.
            if deferred_leaves.is_empty() {
                if ay_proof::check_proof_strict(&new_proof, &self.ctx.terms).is_err() {
                    return false;
                }
            } else {
                let mut gate_proof = new_proof.clone();
                // #trust->0 C3: same registries the mint-time check uses.
                let c3_dt_data = crate::theory_inference::dt_funnel_registry_data(&self.ctx);
                let c3_dt = c3_dt_data
                    .as_ref()
                    .map(crate::theory_inference::DatatypeRegistries::from_data);
                Self::promote_generic_theory_lemma_kinds_after_rewrite(
                    &self.ctx.terms,
                    &mut gate_proof,
                    c3_dt.as_ref(),
                );
                self.promote_array_extensionality_axioms(&mut gate_proof);
                // The contextual variant supplies the datatype/selector
                // registries and the array-witness freshness scope the
                // context-free entry point cannot know; without them a
                // correct extensionality lemma fails closed for lack of a
                // problem assertion set.
                if self
                    .check_proof_strict_derivation_with_datatypes(&gate_proof)
                    .is_err()
                {
                    return false;
                }
            }
        }

        // The assume-bridge plans above reconstruct these terms directly from
        // parsed problem assertions, then validate the exact bridge that uses
        // each one. They are therefore genuine authored premises even when
        // recursive raw interning gives them a different id from both the
        // folded canonical assertion and the shallow top-level raw form
        // captured by the ordinary original-rebuild setup. Collect only those
        // typed plan fields; never infer authority by scanning the rebuilt
        // proof's Assume leaves.
        let mut rebuilt_authored_premises: Vec<TermId> = assume_plans
            .values()
            .filter_map(|plan| match plan {
                AssumePlan::Distinct { raw, .. } | AssumePlan::Literal { raw, .. } => Some(*raw),
                AssumePlan::AndBounds { raw_and, .. } | AssumePlan::AndDistinct { raw_and, .. } => {
                    Some(*raw_and)
                }
                AssumePlan::QuantExpansion { .. } => None,
            })
            .collect();
        // The defined-equality ite-lift variant likewise re-interns the exact
        // parsed defining equality as `orig`; the ordinary variant uses its
        // canonical original directly and needs no additional registration.
        rebuilt_authored_premises.extend(
            ite_lifts
                .values()
                .filter(|plan| plan.defining_source.is_some())
                .map(|plan| plan.orig),
        );
        rebuilt_authored_premises.extend(
            provenance_ite_lifts
                .values()
                .filter(|plan| plan.defining_source.is_some())
                .map(|plan| plan.orig),
        );
        rebuilt_authored_premises.extend(quant_negations.values().map(|plan| plan.forall_term));
        rebuilt_authored_premises.extend(
            authored_array_ites
                .values()
                .filter(|plan| plan.guard_source != plan.guard)
                .map(|plan| plan.guard_source),
        );
        // Success. Override-purge discipline: every term the trichotomy /
        // assume-bridge surgery prints is raw-interned or canonical; a stale
        // surface override collected during the ordinary export could corrupt
        // the rigid `la_disequality` / `distinct_elim` / `and_pos` literal
        // shapes. Surface-preserving ITE/authored-OR surgery is the opposite:
        // each re-added original Assume must print with the problem file's
        // syntax (Carcara matches assumes syntactically), so overrides remain.
        // Their derivations use the same canonical subterms throughout.
        let mut next_surface_overrides = if keeps_surface_overrides {
            let Some(overrides) = prepared_surface_overrides else {
                return false;
            };
            Some(overrides)
        } else if has_quant_plans {
            let Some(overrides) = prepared_quant_surface_overrides else {
                return false;
            };
            Some(overrides)
        } else if !trichotomies.is_empty() || !assume_plans.is_empty() {
            None
        } else {
            self.last_proof_term_overrides.clone()
        };
        // The array-ITE repair re-introduces its exact authored array equality
        // and guard after preprocessing consumed them. Recollect ONLY their
        // root spellings: the assumes must match the input, while recursive
        // source overrides would alter the canonical array/index operands of
        // the independently certified ROW derivation at Alethe export.
        if !authored_array_ites.is_empty() {
            let Some(overrides) = next_surface_overrides.as_mut() else {
                return false;
            };
            let authored_roots: HashSet<TermId> = originals.iter().map(|(term, _)| *term).collect();
            for plan in authored_array_ites.values() {
                // Existing export state may already contain recursively
                // collected spellings from these assertions. Strip every
                // non-premise node in the certified fragment so ROW/chain/ITE
                // printers see precisely the terms the strict checker saw.
                // Whole authored roots are preserved and restored below.
                let mut stack = vec![plan.target_or, plan.ite_term];
                stack.extend(plan.congruence_clause.iter().copied());
                stack.extend(plan.row1_clause.iter().copied());
                stack.extend(plan.transitivity_clause.iter().copied());
                let mut visited = HashSet::default();
                while let Some(term) = stack.pop() {
                    if !visited.insert(term) {
                        continue;
                    }
                    if !authored_roots.contains(&term) {
                        overrides.remove(&term);
                    }
                    stack.extend(self.ctx.terms.children(term));
                }
                if plan.guard_source != plan.guard {
                    overrides.remove(&plan.guard);
                }
                let canonical = plan.array_equality;
                let Some((_, parsed)) = originals.iter().find(|(term, _)| *term == canonical)
                else {
                    return false;
                };
                super::proof_surface_syntax::collect_root_surface_term_override(
                    &mut self.ctx,
                    canonical,
                    parsed,
                    overrides,
                );
                super::proof_surface_syntax::collect_deep_array_surface_overrides(
                    &mut self.ctx,
                    parsed,
                    overrides,
                );
            }
        }
        // The canonical source premise must retain the exact authored
        // implication spelling.  Conversely, the independently derived target
        // must print as its packed `or`; a stale whole-term override would turn
        // the `or_neg`/resolution conclusion back into an implication.  Do this
        // last so the substitution and quantifier collectors above cannot
        // accidentally restore the target override.  Planning already rejects
        // targets that are themselves authored canonical premises.
        if !normalized_authored_ors.is_empty() {
            let Some(overrides) = next_surface_overrides.as_mut() else {
                return false;
            };
            for plan in normalized_authored_ors.values() {
                let Some((_, parsed)) = originals.iter().find(|(term, _)| *term == plan.source_or)
                else {
                    return false;
                };
                if !super::proof_surface_syntax::collect_surface_term_overrides(
                    &mut self.ctx,
                    plan.source_or,
                    parsed,
                    overrides,
                ) {
                    return false;
                }
            }
            for plan in normalized_authored_ors.values() {
                overrides.remove(&plan.target_or);
            }
        }
        if next_surface_overrides.as_ref().is_some_and(|overrides| {
            !super::proof_surface_syntax::surface_override_map_is_bounded(overrides)
        }) {
            return false;
        }
        let Some(rebuilt_authored_premises) = prepare_rebuilt_premise_append(
            &mut self.last_proof_rebuild_originals,
            &rebuilt_authored_premises,
        ) else {
            return false;
        };
        *proof = new_proof;
        self.last_proof_term_overrides = next_surface_overrides;
        self.last_proof_rebuild_originals
            .extend(rebuilt_authored_premises);
        true
    }

    /// Recognize a trust step's clause as an Int trichotomy lemma
    /// `(cl (or (= x y) S1 S2))` with a single `or`-split consumer, and
    /// pre-verify both `[1, 1]` strengthening bridges (fail-closed).
    fn plan_trichotomy(
        &mut self,
        proof: &Proof,
        clause: &[TermId],
        consumers: &[usize],
        trust_idx: usize,
    ) -> Option<TrichotomyPlan> {
        if clause.len() != 1 {
            return None;
        }
        let TermData::App(Symbol::Named(name), disjuncts) = self.ctx.terms.get(clause[0]) else {
            return None;
        };
        if name != "or" || disjuncts.len() != 3 {
            return None;
        }
        let disjuncts = disjuncts.clone();
        // Exactly one equality disjunct over Int operands.
        let mut eq_pos: Option<usize> = None;
        for (i, &d) in disjuncts.iter().enumerate() {
            if let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(d) {
                if op == "=" && args.len() == 2 {
                    if eq_pos.is_some() {
                        return None;
                    }
                    eq_pos = Some(i);
                }
            }
        }
        let eq_pos = eq_pos?;
        let eq = disjuncts[eq_pos];
        let TermData::App(_, eq_args) = self.ctx.terms.get(eq) else {
            return None;
        };
        let (x, y) = (eq_args[0], eq_args[1]);
        if *self.ctx.terms.sort(x) != Sort::Int || *self.ctx.terms.sort(y) != Sort::Int {
            return None;
        }
        let mut strengthened = disjuncts
            .iter()
            .enumerate()
            .filter(|&(i, _)| i != eq_pos)
            .map(|(_, &d)| d);
        let (s1, s2) = (strengthened.next()?, strengthened.next()?);

        // The `la_disequality` split literals (raw operand order is the
        // rule's rigid shape; fail-closed on constant-fold surprises).
        let le_xy = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [x, y], Sort::Bool);
        let le_yx = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [y, x], Sort::Bool);
        for le in [le_xy, le_yx] {
            let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(le) else {
                return None;
            };
            if op != "<=" || args.len() != 2 {
                return None;
            }
        }
        let not_le_xy = self.ctx.terms.mk_not_raw(le_xy);
        let not_le_yx = self.ctx.terms.mk_not_raw(le_yx);
        let or_term =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), [eq, not_le_xy, not_le_yx], Sort::Bool);

        // Pair each strengthened disjunct with the split literal that
        // implies it, VERIFYING the `[1, 1]` certificate both ways
        // (never pattern-match what a checker can decide).
        let (strong_from_yx, strong_from_xy) =
            if self.pair_lemma_valid(s1, le_yx) && self.pair_lemma_valid(s2, le_xy) {
                (s1, s2)
            } else if self.pair_lemma_valid(s2, le_yx) && self.pair_lemma_valid(s1, le_xy) {
                (s2, s1)
            } else {
                return None;
            };

        // Exactly one consumer: the `or` split of this trust step, whose
        // clause is the same 3-literal set the derivation reproduces.
        let mut uniq: Vec<usize> = consumers.to_vec();
        uniq.sort_unstable();
        uniq.dedup();
        if uniq.len() != 1 {
            return None;
        }
        let or_split_idx = uniq[0];
        let ProofStep::Step {
            rule: AletheRule::Or,
            clause: split_clause,
            premises,
            ..
        } = &proof.steps[or_split_idx]
        else {
            return None;
        };
        if premises.len() != 1 || premises[0].0 as usize != trust_idx {
            return None;
        }
        let mut want = vec![eq, strong_from_yx, strong_from_xy];
        let mut have = split_clause.clone();
        want.sort_unstable();
        have.sort_unstable();
        if want != have {
            return None;
        }

        Some(TrichotomyPlan {
            or_split_idx,
            eq,
            le_xy,
            le_yx,
            not_le_xy,
            not_le_yx,
            or_term,
            strong_from_yx,
            strong_from_xy,
        })
    }

    /// Recognize exact term-ITE lifting from an authored assertion and
    /// pre-verify both branch transfers as Farkas certificates.
    fn plan_ite_lift(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<IteLiftPlan> {
        if clause.len() != 1 {
            return None;
        }
        let goal = clause[0];
        let TermData::Ite(cond, lifted_then, lifted_else) = *self.ctx.terms.get(goal) else {
            return None;
        };
        for (orig, parsed) in originals {
            let orig = *orig;
            if !source_index.contains(orig) {
                continue;
            }
            if !planning.spend_surface(orig, parsed)
                || !planning.spend_terms(&self.ctx.terms, &[orig])
            {
                return None;
            }
            // Collect the term-level ite subterms of `orig` that share the
            // lifted condition.
            let candidates = self.term_ite_candidates_with_cond(orig, cond);
            for (ite_term, u, v) in candidates {
                if !planning.spend_terms(&self.ctx.terms, &[orig, orig]) {
                    return None;
                }
                let then_subst = self.ctx.terms.substitute(orig, &[ite_term], &[u]);
                let else_subst = self.ctx.terms.substitute(orig, &[ite_term], &[v]);
                if then_subst != lifted_then || else_subst != lifted_else {
                    continue;
                }
                let Some((eq_then, eq_else, ite_def, and_term, intro_eq)) =
                    self.build_ite_lift_connectives(orig, cond, ite_term, u, v)
                else {
                    continue;
                };
                // Verify both transfer lemmas (fail-closed; never
                // pattern-match what a checker can decide).
                if !self.triple_lemma_valid(eq_then, orig, lifted_then)
                    || !self.triple_lemma_valid(eq_else, orig, lifted_else)
                {
                    continue;
                }
                return Some(IteLiftPlan {
                    orig,
                    defining_source: None,
                    bound: None,
                    cond,
                    lifted_then,
                    lifted_else,
                    goal,
                    ite_term,
                    eq_then,
                    eq_else,
                    ite_def,
                    and_term,
                    intro_eq,
                    then_coeffs: FarkasAnnotation::from_ints(&[1, 1, 1]),
                    else_coeffs: FarkasAnnotation::from_ints(&[1, 1, 1]),
                });
            }
        }
        // Defined-equality variant: `(= d (ite c u v))` plus an authored
        // bound `P(d)` derives the two lifted branches through `ite_intro`.
        for (canonical, parsed) in originals {
            let canonical = *canonical;
            if !source_index.contains(canonical) {
                continue;
            }
            if !planning.spend_surface(canonical, parsed) {
                return None;
            }
            let stripped = strip_frontend_annotations(parsed);
            let FrontendTerm::App(op, sides) = stripped else {
                continue;
            };
            if op != "=" || sides.len() != 2 {
                continue;
            }
            for ite_side in [0usize, 1] {
                let ite_surface = strip_frontend_annotations(&sides[ite_side]);
                let def_surface = strip_frontend_annotations(&sides[1 - ite_side]);
                let FrontendTerm::App(iop, iargs) = ite_surface else {
                    continue;
                };
                if iop != "ite" || iargs.len() != 3 {
                    continue;
                }
                let (Some(c), Some(u), Some(v), Some(defined)) = (
                    self.ctx.elaborate_surface_subterm(&iargs[0]),
                    self.ctx.elaborate_surface_subterm(&iargs[1]),
                    self.ctx.elaborate_surface_subterm(&iargs[2]),
                    self.ctx.elaborate_surface_subterm(def_surface),
                ) else {
                    continue;
                };
                if c != cond {
                    continue;
                }
                let ite_term = self.ctx.terms.mk_ite(cond, u, v);
                if *self.ctx.terms.sort(ite_term) == Sort::Bool
                    || !matches!(
                        self.ctx.terms.get(ite_term),
                        TermData::Ite(ic, iu, iv) if *ic == cond && *iu == u && *iv == v
                    )
                {
                    continue;
                }
                // The defining equality, re-interned in SURFACE operand order
                // (fail-closed if interning folds it away from that shape).
                let ordered = if ite_side == 0 {
                    [ite_term, defined]
                } else {
                    [defined, ite_term]
                };
                let p_raw = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), ordered, Sort::Bool);
                if !matches!(
                    self.ctx.terms.get(p_raw),
                    TermData::App(Symbol::Named(eop), eargs)
                        if eop == "=" && eargs.as_slice() == ordered
                ) {
                    continue;
                }
                let Some(authored_raw) = self.raw_intern_surface(stripped) else {
                    continue;
                };
                if authored_raw != p_raw {
                    // The lift below treats `p_raw` as an authored premise.
                    // Nested folds inside the condition, either branch, or
                    // the defined side need their own derivation; a
                    // whole-term print override is not proof authority.
                    continue;
                }
                for &(bound, _) in originals {
                    if bound == canonical || !source_index.contains(bound) {
                        continue;
                    }
                    if !planning.spend_terms(&self.ctx.terms, &[bound, bound]) {
                        return None;
                    }
                    let then_subst = self.ctx.terms.substitute(bound, &[defined], &[u]);
                    let else_subst = self.ctx.terms.substitute(bound, &[defined], &[v]);
                    if then_subst != lifted_then || else_subst != lifted_else {
                        continue;
                    }
                    let Some((eq_then, eq_else, ite_def, and_term, intro_eq)) =
                        self.build_ite_lift_connectives(p_raw, cond, ite_term, u, v)
                    else {
                        continue;
                    };
                    if !self.quad_lemma_valid(eq_then, p_raw, bound, lifted_then)
                        || !self.quad_lemma_valid(eq_else, p_raw, bound, lifted_else)
                    {
                        continue;
                    }
                    return Some(IteLiftPlan {
                        orig: p_raw,
                        defining_source: Some(canonical),
                        bound: Some(bound),
                        cond,
                        lifted_then,
                        lifted_else,
                        goal,
                        ite_term,
                        eq_then,
                        eq_else,
                        ite_def,
                        and_term,
                        intro_eq,
                        then_coeffs: FarkasAnnotation::from_ints(&[1, 1, 1, 1]),
                        else_coeffs: FarkasAnnotation::from_ints(&[1, 1, 1, 1]),
                    });
                }
            }
        }
        self.plan_ite_lift_over_substituted_bound(originals, cond, lifted_then, lifted_else, goal)
    }

    /// Build and shape-check the `ite_intro` derivation's connective terms
    /// for `orig` containing the term-level `ite_term = (ite cond u v)`.
    /// Fail-closed: `None` when any raw application does not intern with the
    /// exact expected shape.
    pub(super) fn build_ite_lift_connectives(
        &mut self,
        orig: TermId,
        cond: TermId,
        ite_term: TermId,
        u: TermId,
        v: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId, TermId)> {
        let eq_then = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [ite_term, u], Sort::Bool);
        let eq_else = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [ite_term, v], Sort::Bool);
        let eq_shape = |terms: &ay_core::TermStore, t: TermId, l: TermId, r: TermId| {
            matches!(
                terms.get(t),
                TermData::App(Symbol::Named(op), args)
                    if op == "=" && args.len() == 2 && args[0] == l && args[1] == r
            )
        };
        if !eq_shape(&self.ctx.terms, eq_then, ite_term, u)
            || !eq_shape(&self.ctx.terms, eq_else, ite_term, v)
        {
            return None;
        }
        let ite_def = self.ctx.terms.mk_ite(cond, eq_then, eq_else);
        if !matches!(
            self.ctx.terms.get(ite_def),
            TermData::Ite(c, a, b) if *c == cond && *a == eq_then && *b == eq_else
        ) {
            return None;
        }
        let and_term = self
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [orig, ite_def], Sort::Bool);
        if !matches!(
            self.ctx.terms.get(and_term),
            TermData::App(Symbol::Named(op), args)
                if op == "and" && args.len() == 2 && args[0] == orig && args[1] == ite_def
        ) {
            return None;
        }
        let intro_eq = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [orig, and_term], Sort::Bool);
        if !eq_shape(&self.ctx.terms, intro_eq, orig, and_term) {
            return None;
        }
        Some((eq_then, eq_else, ite_def, and_term, intro_eq))
    }

    /// Recognize a singleton trust clause as the packed canonical `or` of an
    /// exact authored right-associated implication chain.
    ///
    /// Authority comes from the immutable `(canonical, parsed)` original pair.
    /// The canonical half is the exact internal premise; the parsed half must
    /// still be a right-associated implication chain of the same width.  This
    /// separation is intentional: the strict checker sees the canonical
    /// packed `or`, while the Alethe printer replays its decomposition through
    /// `implies_pos` so the external premise retains the authored spelling.
    /// Only an exact comparison dual may differ between source and target, and
    /// that two-literal bridge is independently Farkas-validated.
    fn plan_normalized_authored_or(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
    ) -> Option<NormalizedAuthoredOrPlan> {
        let [target_or] = clause else {
            return None;
        };
        let target_or = *target_or;
        let TermData::App(Symbol::Named(op), target_disjuncts) = self.ctx.terms.get(target_or)
        else {
            return None;
        };
        if op != "or" || target_disjuncts.len() < 2 {
            return None;
        }
        let target_disjuncts = target_disjuncts.clone();
        if !matches!(self.ctx.terms.sort(target_or), Sort::Bool)
            || target_disjuncts
                .iter()
                .any(|&term| !matches!(self.ctx.terms.sort(term), Sort::Bool))
        {
            return None;
        }
        let mut distinct = target_disjuncts.clone();
        distinct.sort_unstable();
        distinct.dedup();
        if distinct.len() != target_disjuncts.len() {
            return None;
        }

        // Removing the target's whole-term surface override is necessary for
        // the derived packed `or` to print as an `or`.  Never do that when the
        // same term is itself an authored premise: a shared TermId would make
        // the surviving assume print differently from the input assertion.
        if originals
            .iter()
            .any(|(canonical, _)| *canonical == target_or)
        {
            return None;
        }

        for (source_or, parsed) in originals {
            // Re-authenticate the pair locally.  The caller already assembled
            // it from the immutable parsed/original stacks, but this check
            // prevents a forged `(TermId, surface)` tuple from granting premise
            // authority to the plan.
            if self.ctx.elaborate_surface_subterm(parsed) != Some(*source_or) {
                continue;
            }
            let Some(plan) = self.plan_normalized_authored_or_from_source(
                *source_or,
                target_or,
                &target_disjuncts,
                parsed,
            ) else {
                continue;
            };
            return Some(plan);
        }
        None
    }

    fn plan_normalized_authored_or_from_source(
        &mut self,
        source_or: TermId,
        target_or: TermId,
        target_disjuncts: &[TermId],
        parsed: &FrontendTerm,
    ) -> Option<NormalizedAuthoredOrPlan> {
        if source_or == target_or {
            return None;
        }

        let TermData::App(Symbol::Named(source_op), source_disjuncts) =
            self.ctx.terms.get(source_or)
        else {
            return None;
        };
        if source_op != "or" || source_disjuncts.len() != target_disjuncts.len() {
            return None;
        }
        let source_disjuncts = source_disjuncts.clone();
        if source_disjuncts.len() < 2
            || !matches!(self.ctx.terms.sort(source_or), Sort::Bool)
            || source_disjuncts
                .iter()
                .any(|&term| !matches!(self.ctx.terms.sort(term), Sort::Bool))
        {
            return None;
        }
        let mut distinct_source = source_disjuncts.clone();
        distinct_source.sort_unstable();
        distinct_source.dedup();
        if distinct_source.len() != source_disjuncts.len() {
            return None;
        }

        // Retain the source-language guard: an arbitrary authored `or` with
        // the same canonical term must not enter the implication-specific
        // printer bridge.  The final consequent accounts for the last
        // disjunct, hence links + 1 must equal the flat canonical width.
        let mut current_surface = strip_frontend_annotations(parsed);
        let mut implication_links = 0usize;
        while let FrontendTerm::App(head, operands) = current_surface {
            if head != "=>" || operands.len() != 2 {
                break;
            }
            implication_links = implication_links.checked_add(1)?;
            current_surface = strip_frontend_annotations(&operands[1]);
        }
        if implication_links == 0 || implication_links + 1 != source_disjuncts.len() {
            return None;
        }

        let mut used_target = vec![false; target_disjuncts.len()];
        let mut aligned: Vec<Option<(TermId, Option<TermId>)>> = vec![None; source_disjuncts.len()];

        // Exact identities always win.  Doing this as a separate pass prevents
        // an earlier arithmetic literal from consuming a target that a later
        // source literal shares exactly.
        for (source_position, &source) in source_disjuncts.iter().enumerate() {
            if let Some(position) = target_disjuncts
                .iter()
                .enumerate()
                .position(|(position, &target)| !used_target[position] && target == source)
            {
                used_target[position] = true;
                aligned[source_position] = Some((source, None));
            }
        }

        // The sole non-exact alignment is an exact syntactic comparison dual
        // (`not (< a b)` versus `(<= b a)`, and the seven polarity/head
        // variants).  No general arithmetic-equivalence search is admitted.
        for (source_position, &source) in source_disjuncts.iter().enumerate() {
            if aligned[source_position].is_some() {
                continue;
            }
            let mut bridged = None;
            for (position, &target) in target_disjuncts.iter().enumerate() {
                if used_target[position] {
                    continue;
                }
                let Some(bridge_atom) = self.comparison_dual_source_literal(source, target) else {
                    continue;
                };
                bridged = Some((position, target, bridge_atom));
                break;
            }
            let (position, canonical, bridge_atom) = bridged?;
            used_target[position] = true;
            aligned[source_position] = Some((canonical, Some(bridge_atom)));
        }
        if used_target.iter().any(|used| !*used) {
            return None;
        }
        let literals: Option<Vec<NormalizedAuthoredOrLiteral>> = source_disjuncts
            .iter()
            .copied()
            .zip(aligned)
            .map(|(source, alignment)| {
                alignment.map(|(canonical, bridge_atom)| NormalizedAuthoredOrLiteral {
                    source,
                    canonical,
                    bridge_atom,
                })
            })
            .collect();

        Some(NormalizedAuthoredOrPlan {
            source_or,
            source_disjuncts,
            target_or,
            target_disjuncts: target_disjuncts.to_vec(),
            literals: literals?,
        })
    }

    /// Emit a [`NormalizedAuthoredOrPlan`], returning the exact singleton
    /// `(cl target_or)` unit consumed by the old trust step's users.
    fn emit_normalized_authored_or(
        &mut self,
        new_proof: &mut Proof,
        plan: &NormalizedAuthoredOrPlan,
        source_assume: ProofId,
    ) -> Option<ProofId> {
        let mut clause = plan.source_disjuncts.clone();
        let mut current = new_proof.add_rule_step(
            AletheRule::Or,
            clause.clone(),
            vec![source_assume],
            Vec::new(),
        );

        // Normalize only the comparison literals whose pair certificates were
        // independently checked during planning.
        for literal in &plan.literals {
            let Some(bridge_atom) = literal.bridge_atom else {
                continue;
            };
            let position = clause.iter().position(|&term| term == literal.source)?;
            let _ = clause.remove(position);
            if !clause.contains(&literal.canonical) {
                clause.push(literal.canonical);
            }
            let source_complement = complement_of(&mut self.ctx.terms, literal.source);
            let bridge = Self::add_pair_lemma(new_proof, literal.canonical, source_complement);
            current = new_proof.add_resolution(clause.clone(), bridge_atom, current, bridge);
        }
        if clause.len() != plan.target_disjuncts.len()
            || clause
                .iter()
                .any(|term| !plan.target_disjuncts.contains(term))
        {
            return None;
        }

        // Pack the exact flat clause back into the singleton or-term.  This is
        // the same checked `or_neg` + contraction recipe used by the existing
        // or-wrapped EUF tautology emitter.
        for &disjunct in &plan.target_disjuncts {
            let position = clause.iter().position(|&term| term == disjunct)?;
            let _ = clause.remove(position);
            let not_disjunct = self.ctx.terms.mk_not_raw(disjunct);
            let or_neg = new_proof.add_rule_step(
                AletheRule::OrNeg,
                vec![plan.target_or, not_disjunct],
                Vec::new(),
                Vec::new(),
            );
            clause.push(plan.target_or);
            current = new_proof.add_resolution(clause.clone(), disjunct, current, or_neg);
        }
        let unit = new_proof.add_rule_step(
            AletheRule::Contraction,
            vec![plan.target_or],
            vec![current],
            Vec::new(),
        );
        Some(unit)
    }

    /// Recognize a preprocessor-produced Boolean ITE wrapper around one exact
    /// read-over-write consequence of two authored premises.
    fn plan_authored_array_ite(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
    ) -> Option<AuthoredArrayItePlan> {
        let [target_or] = clause else {
            return None;
        };
        let target_or = *target_or;
        let TermData::App(Symbol::Named(op), disjuncts) = self.ctx.terms.get(target_or) else {
            return None;
        };
        if op != "or"
            || disjuncts.len() != 2
            || !matches!(self.ctx.terms.sort(target_or), Sort::Bool)
        {
            return None;
        }
        let disjuncts = disjuncts.clone();
        if originals
            .iter()
            .any(|(canonical, _)| *canonical == target_or)
        {
            return None;
        }
        let (array_equality, ite_term) = match (
            self.ctx.terms.get(disjuncts[0]),
            self.ctx.terms.get(disjuncts[1]),
        ) {
            (TermData::Not(equality), TermData::Ite(..)) => (*equality, disjuncts[1]),
            (TermData::Ite(..), TermData::Not(equality)) => (*equality, disjuncts[0]),
            _ => return None,
        };
        let (array_lhs, array_rhs) = decode_binary_equality(&self.ctx.terms, array_equality)?;
        let TermData::Ite(guard, then_branch, else_branch) = self.ctx.terms.get(ite_term).clone()
        else {
            return None;
        };
        if [array_equality, guard, then_branch, else_branch, ite_term]
            .into_iter()
            .any(|term| !matches!(self.ctx.terms.sort(term), Sort::Bool))
        {
            return None;
        }

        // Both discharged units must be immutable authored assertions, not
        // merely terms with a convenient spelling. Re-elaborate each exact
        // `(canonical, parsed)` pair locally before granting premise authority.
        let mut guard_surface = None;
        for required in [array_equality, guard] {
            let mut authenticated = false;
            for (canonical, parsed) in originals {
                if *canonical == required
                    && self.ctx.elaborate_surface_subterm(parsed) == Some(required)
                {
                    authenticated = true;
                    if required == guard {
                        guard_surface = Some(parsed.clone());
                    }
                    break;
                }
            }
            if !authenticated {
                return None;
            }
        }
        let guard_source = self.raw_intern_surface(&guard_surface?)?;
        if !matches!(self.ctx.terms.sort(guard_source), Sort::Bool) {
            return None;
        }
        if guard_source != guard {
            let source_complement = complement_of(&mut self.ctx.terms, guard_source);
            if !self.pair_lemma_valid(guard, source_complement) {
                return None;
            }
        }

        let (guard_lhs, guard_rhs) = decode_binary_equality(&self.ctx.terms, guard)?;
        let (then_lhs, then_rhs) = decode_binary_equality(&self.ctx.terms, then_branch)?;
        let same_pair =
            |a: TermId, b: TermId, c: TermId, d: TermId| (a == c && b == d) || (a == d && b == c);

        // Identify exactly one orientation in which the authored array
        // equality relates an array root to `store(base, i, v)`, the ITE guard
        // equates `i` with the read index, and the then arm equates `v` with a
        // read of that same root.  Ambiguous shapes fail closed.
        let mut shapes = Vec::new();
        for (array, stored) in [(array_lhs, array_rhs), (array_rhs, array_lhs)] {
            let TermData::App(Symbol::Named(store_op), store_args) = self.ctx.terms.get(stored)
            else {
                continue;
            };
            if store_op != "store" || store_args.len() != 3 {
                continue;
            }
            let store_index = store_args[1];
            let store_value = store_args[2];
            for (value, read) in [(then_lhs, then_rhs), (then_rhs, then_lhs)] {
                if value != store_value {
                    continue;
                }
                let TermData::App(Symbol::Named(select_op), select_args) = self.ctx.terms.get(read)
                else {
                    continue;
                };
                if select_op != "select" || select_args.len() != 2 || select_args[0] != array {
                    continue;
                }
                let read_index = select_args[1];
                if !same_pair(guard_lhs, guard_rhs, store_index, read_index) {
                    continue;
                }
                let shape = (stored, store_index, store_value, read, read_index);
                if !shapes.contains(&shape) {
                    shapes.push(shape);
                }
            }
        }
        let [(stored, _store_index, store_value, array_read, read_index)] = shapes.as_slice()
        else {
            return None;
        };
        let (stored, store_value, array_read, read_index) =
            (*stored, *store_value, *array_read, *read_index);

        let not_equality = self.ctx.terms.mk_not_raw(array_equality);
        let not_guard = self.ctx.terms.mk_not_raw(guard);
        if !disjuncts.contains(&not_equality)
            || !matches!(self.ctx.terms.get(not_equality), TermData::Not(inner) if *inner == array_equality)
            || !matches!(self.ctx.terms.get(not_guard), TermData::Not(inner) if *inner == guard)
        {
            return None;
        }
        let stored_read = self.ctx.terms.mk_app(
            Symbol::named("select"),
            [stored, read_index],
            self.ctx.terms.sort(store_value).clone(),
        );
        let select_congruence =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [array_read, stored_read], Sort::Bool);
        let store_hit =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [stored_read, store_value], Sort::Bool);
        let not_select_congruence = self.ctx.terms.mk_not_raw(select_congruence);
        let not_store_hit = self.ctx.terms.mk_not_raw(store_hit);
        let congruence_clause = vec![not_equality, select_congruence];
        let row1_clause = vec![not_guard, store_hit];
        let transitivity_clause = vec![not_select_congruence, not_store_hit, then_branch];

        if ay_proof::recognize_array_theory_lemma(&self.ctx.terms, &congruence_clause)
            != Some(TheoryLemmaKind::ArrayRowChain)
            || ay_proof::recognize_array_select_store(&self.ctx.terms, &row1_clause) != Some(true)
        {
            return None;
        }

        // Plan-time validation uses the same strict fragment checker as the
        // final whole-proof gate. The emitter cannot widen the recognized
        // congruence, conditional ROW1, or transitivity shapes merely by
        // attaching the desired rule tags.
        let mut fragment = Proof::new();
        let congruence = fragment.add_theory_lemma_with_kind(
            "array",
            congruence_clause.clone(),
            TheoryLemmaKind::ArrayRowChain,
        );
        let row1 = fragment.add_theory_lemma_with_kind(
            "array",
            row1_clause.clone(),
            TheoryLemmaKind::ArraySelectStore { index_eq: true },
        );
        let transitivity = fragment.add_rule_step(
            AletheRule::EqTransitive,
            transitivity_clause.clone(),
            Vec::new(),
            Vec::new(),
        );
        let authenticated = ay_proof::authenticate_premise_clauses_strict_with_context(
            &fragment,
            &self.ctx.terms,
            None,
            None,
            &[],
        )
        .ok()?;
        if authenticated.clause(congruence) != Some(congruence_clause.as_slice())
            || authenticated.clause(row1) != Some(row1_clause.as_slice())
            || authenticated.clause(transitivity) != Some(transitivity_clause.as_slice())
        {
            return None;
        }

        Some(AuthoredArrayItePlan {
            target_or,
            array_equality,
            guard_source,
            guard,
            then_branch,
            ite_term,
            select_congruence,
            store_hit,
            congruence_clause,
            row1_clause,
            transitivity_clause,
        })
    }

    /// Emit the strict ROW consequence, discharge its two authored premises,
    /// then lift the resulting then-arm unit through `ite_neg2` and `or_neg`.
    fn emit_authored_array_ite(
        &mut self,
        new_proof: &mut Proof,
        plan: &AuthoredArrayItePlan,
        equality_assume: ProofId,
        guard_assume: ProofId,
    ) -> Option<ProofId> {
        let [not_equality, select_congruence]: [TermId; 2] =
            plan.congruence_clause.clone().try_into().ok()?;
        let [not_guard, store_hit]: [TermId; 2] = plan.row1_clause.clone().try_into().ok()?;
        let [not_select_congruence, not_store_hit, then_branch]: [TermId; 3] =
            plan.transitivity_clause.clone().try_into().ok()?;
        if select_congruence != plan.select_congruence
            || store_hit != plan.store_hit
            || then_branch != plan.then_branch
            || !matches!(self.ctx.terms.get(not_equality), TermData::Not(inner) if *inner == plan.array_equality)
            || !matches!(self.ctx.terms.get(not_guard), TermData::Not(inner) if *inner == plan.guard)
            || !matches!(self.ctx.terms.get(not_select_congruence), TermData::Not(inner) if *inner == plan.select_congruence)
            || !matches!(self.ctx.terms.get(not_store_hit), TermData::Not(inner) if *inner == plan.store_hit)
        {
            return None;
        }
        let guard_unit = if plan.guard_source == plan.guard {
            guard_assume
        } else {
            let source_complement = complement_of(&mut self.ctx.terms, plan.guard_source);
            if !self.pair_lemma_valid(plan.guard, source_complement) {
                return None;
            }
            let bridge = Self::add_pair_lemma(new_proof, plan.guard, source_complement);
            new_proof.add_resolution(
                vec![plan.guard],
                atom_of(&self.ctx.terms, plan.guard_source),
                guard_assume,
                bridge,
            )
        };
        let congruence = new_proof.add_theory_lemma_with_kind(
            "array",
            plan.congruence_clause.clone(),
            TheoryLemmaKind::ArrayRowChain,
        );
        let congruence_unit = new_proof.add_resolution(
            vec![plan.select_congruence],
            plan.array_equality,
            congruence,
            equality_assume,
        );
        let row1 = new_proof.add_theory_lemma_with_kind(
            "array",
            plan.row1_clause.clone(),
            TheoryLemmaKind::ArraySelectStore { index_eq: true },
        );
        let store_hit_unit =
            new_proof.add_resolution(vec![plan.store_hit], plan.guard, row1, guard_unit);
        let transitivity = new_proof.add_rule_step(
            AletheRule::EqTransitive,
            plan.transitivity_clause.clone(),
            Vec::new(),
            Vec::new(),
        );
        let without_congruence = new_proof.add_resolution(
            vec![not_store_hit, plan.then_branch],
            plan.select_congruence,
            transitivity,
            congruence_unit,
        );
        let then_unit = new_proof.add_resolution(
            vec![plan.then_branch],
            plan.store_hit,
            without_congruence,
            store_hit_unit,
        );

        let not_then = self.ctx.terms.mk_not_raw(plan.then_branch);
        let ite_neg2 = new_proof.add_rule_step(
            AletheRule::IteNeg2,
            vec![plan.ite_term, not_guard, not_then],
            Vec::new(),
            Vec::new(),
        );
        let ite_without_guard = new_proof.add_resolution(
            vec![plan.ite_term, not_then],
            plan.guard,
            ite_neg2,
            guard_unit,
        );
        let ite_unit = new_proof.add_resolution(
            vec![plan.ite_term],
            plan.then_branch,
            ite_without_guard,
            then_unit,
        );

        let not_ite = self.ctx.terms.mk_not_raw(plan.ite_term);
        let or_neg = new_proof.add_rule_step(
            AletheRule::OrNeg,
            vec![plan.target_or, not_ite],
            Vec::new(),
            Vec::new(),
        );
        Some(new_proof.add_resolution(vec![plan.target_or], plan.ite_term, ite_unit, or_neg))
    }

    /// Recognize the exact Boolean dual of one canonical arithmetic
    /// comparison literal and return its resolution pivot atom.
    fn comparison_dual_source_literal(&mut self, source: TermId, target: TermId) -> Option<TermId> {
        let (source_atom, negated) = match self.ctx.terms.get(source) {
            TermData::Not(atom) => (*atom, true),
            _ => (source, false),
        };
        let TermData::App(Symbol::Named(head), args) = self.ctx.terms.get(source_atom) else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let head = head.clone();
        let args = args.clone();
        let (dual_head, swap) = match head.as_str() {
            "<" => ("<=", true),
            "<=" => ("<", true),
            ">" => ("<=", false),
            ">=" => ("<", false),
            _ => return None,
        };
        if self.ctx.terms.sort(args[0]) != self.ctx.terms.sort(args[1])
            || !matches!(self.ctx.terms.sort(args[0]), Sort::Int | Sort::Real)
            || !matches!(self.ctx.terms.sort(source), Sort::Bool)
            || !matches!(self.ctx.terms.sort(target), Sort::Bool)
        {
            return None;
        }
        let (lhs, rhs) = if swap {
            (args[1], args[0])
        } else {
            (args[0], args[1])
        };
        let dual_atom = self
            .ctx
            .terms
            .mk_app(Symbol::named(dual_head), [lhs, rhs], Sort::Bool);
        let exact_target = if negated {
            dual_atom
        } else {
            self.ctx.terms.mk_not_raw(dual_atom)
        };
        if exact_target != target {
            return None;
        }
        let source_complement = complement_of(&mut self.ctx.terms, source);
        self.pair_lemma_valid(target, source_complement)
            .then_some(source_atom)
    }

    /// Recognize a preprocessor-derived unit trust step `(cl L)`: an
    /// original disjunctive assertion contains `L`, and every OTHER disjunct
    /// is the syntactic complement of another original assertion (so plain
    /// resolutions against their assumes derive the unit). Fail-closed: the
    /// disjunct atoms must be pairwise distinct (unambiguous pivots) with
    /// `L` among them exactly once.
    fn plan_or_unit(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<OrUnitPlan> {
        if clause.len() != 1 {
            return None;
        }
        let lit = clause[0];
        'orig: for (orig, parsed) in originals {
            if !planning.spend_work(1) {
                return None;
            }
            let orig = *orig;
            if !source_index.contains(orig) {
                continue;
            }
            let TermData::App(Symbol::Named(op), ds) = self.ctx.terms.get(orig) else {
                continue;
            };
            if op != "or"
                || ds.len() < 2
                || ds.len() > MAX_PROVENANCE_REPAIR_TERMS
                || !ds.contains(&lit)
            {
                continue;
            }
            if !planning.spend_surface(orig, parsed)
                || !planning.spend_terms(&self.ctx.terms, &[orig])
            {
                return None;
            }
            let disjuncts = ds.clone();
            if !surface_or_decomposition_matches(&mut self.ctx, parsed, &disjuncts) {
                continue;
            }
            let mut atoms: Vec<TermId> = disjuncts
                .iter()
                .map(|&d| atom_of(&self.ctx.terms, d))
                .collect();
            atoms.sort_unstable();
            atoms.dedup();
            if atoms.len() != disjuncts.len() {
                continue;
            }
            let mut eliminations: Vec<(TermId, TermId)> = Vec::new();
            for &d in &disjuncts {
                if d == lit {
                    continue;
                }
                let comp = complement_of(&mut self.ctx.terms, d);
                if !source_index.contains(comp) {
                    continue 'orig;
                }
                eliminations.push((atom_of(&self.ctx.terms, d), comp));
            }
            return Some(OrUnitPlan {
                orig,
                disjuncts,
                eliminations,
            });
        }
        None
    }

    /// Recognize a PREPROCESSING-COLLAPSE equality unit `(cl (= L R))` and
    /// plan its re-derivation from the problem's ORIGINAL equality assertions
    /// (see [`SubstEqPlan`]).
    ///
    /// The substitute-and-simplify preprocessor eliminates a defined constant
    /// (`(assert (= v0 t))` -> `v0 := t`), so the assertions that justify the
    /// equality never reach the exported proof as `assume` steps and the
    /// equality itself is exported as a premiseless `trust` unit. Every
    /// premise the repair introduces is an assertion of the input file, and
    /// the derivation is the existing EUF toolkit's `eq_transitive` /
    /// `eq_congruent` recipe plus one resolution per re-introduced premise —
    /// no invented premise, no weakened clause.
    ///
    /// Fail-closed: the conclusion must be a binary equality, the hypotheses
    /// must be top-level positive binary-equality ORIGINALS, and the whole
    /// derivation must be plannable by [`Self::plan_euf_lemma`], which only
    /// admits a conclusion its own congruence closure actually entails.
    fn plan_substituted_equality(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<SubstEqPlan> {
        if clause.len() != 1 {
            return None;
        }
        let target = clause[0];
        let (lhs, rhs) = decode_binary_equality(&self.ctx.terms, target)?;
        if lhs == rhs {
            // A reflexive conclusion needs no premise at all; that is a
            // different (and unobserved) shape. Decline.
            return None;
        }
        // Hypothesis candidates: the problem's own top-level positive binary
        // equalities, deduplicated so one assertion cannot supply two clause
        // literals (the EUF planner rejects duplicated literals anyway).
        let mut hyps: Vec<TermId> = Vec::new();
        let mut seen = HashSet::default();
        for (canonical, parsed) in originals {
            if !planning.spend_work(1) {
                return None;
            }
            if *canonical == target
                || !source_index.contains(*canonical)
                || !seen.insert(*canonical)
            {
                continue;
            }
            let Some((a, b)) = decode_binary_equality(&self.ctx.terms, *canonical) else {
                continue;
            };
            if a == b {
                continue;
            }
            if !planning.spend_surface(*canonical, parsed)
                || !planning.spend_terms(&self.ctx.terms, &[*canonical])
            {
                return None;
            }
            if !self.surface_equality_source_is_print_faithful(*canonical, parsed) {
                continue;
            }
            if hyps.len() >= MAX_PROVENANCE_REPAIR_TERMS {
                return None;
            }
            hyps.push(*canonical);
        }
        if hyps.is_empty() {
            return None;
        }
        let plan = self.plan_substituted_equality_over(target, &hyps, planning)?;
        // Second pass over only the hypotheses the recipe actually used: it
        // keeps the emitted lemma minimal (no `weakening` over unrelated
        // assertions) and avoids re-introducing assumes the derivation never
        // reads. Falls back to the full-hypothesis plan if the narrowed set
        // no longer entails the conclusion.
        let EufTarget::Bare { extras } = &plan.euf.target else {
            return Some(plan);
        };
        if extras.is_empty() {
            return Some(plan);
        }
        let used: Vec<TermId> = plan
            .hyps
            .iter()
            .copied()
            .zip(plan.lemma[1..].iter())
            .filter(|(_, neg)| !extras.contains(neg))
            .map(|(h, _)| h)
            .collect();
        if used.is_empty() || used.len() == plan.hyps.len() {
            return Some(plan);
        }
        Some(
            self.plan_substituted_equality_over(target, &used, planning)
                .unwrap_or(plan),
        )
    }

    /// Plan `(cl target)` against exactly `hyps`: synthesize the lemma clause
    /// `[target, (not h1), .., (not hk)]` and hand it to the EUF planner.
    fn plan_substituted_equality_over(
        &mut self,
        target: TermId,
        hyps: &[TermId],
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<SubstEqPlan> {
        let mut lemma = Vec::with_capacity(hyps.len() + 1);
        lemma.push(target);
        for &h in hyps {
            let neg = self.ctx.terms.mk_not_raw(h);
            // `mk_not_raw` must give back a literal negation: a folded result
            // would make the resolution pivots disagree with the lemma.
            if atom_of(&self.ctx.terms, neg) != h || neg == h {
                return None;
            }
            if lemma.contains(&neg) {
                return None;
            }
            lemma.push(neg);
        }
        let euf = self.plan_euf_lemma_with_budget(&lemma, planning)?;
        // Only the bare (flat-clause) target reproduces the synthesized clause
        // literal-for-literal; an `OrUnit` plan would derive a different term.
        if !matches!(euf.target, EufTarget::Bare { .. }) {
            return None;
        }
        Some(SubstEqPlan {
            lemma,
            hyps: hyps.to_vec(),
            euf,
        })
    }

    /// Emit a [`SubstEqPlan`]'s derivation, returning the id of the derived
    /// unit `(cl (= L R))`. `assume_of` must resolve every hypothesis to its
    /// hoisted `assume` step.
    fn emit_substituted_equality(
        &mut self,
        new_proof: &mut Proof,
        plan: &SubstEqPlan,
        assume_of: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let mut cur = self.emit_euf_lemma(new_proof, &plan.euf);
        let mut remaining: Vec<TermId> = plan.lemma.clone();
        for (i, &h) in plan.hyps.iter().enumerate() {
            let assume_id = *assume_of.get(&h)?;
            let neg = plan.lemma[i + 1];
            remaining.retain(|&l| l != neg);
            cur = new_proof.add_resolution(remaining.clone(), h, cur, assume_id);
        }
        (remaining == vec![plan.lemma[0]]).then_some(cur)
    }

    /// True when a `trust`-kind leaf is NOT this pass's business because a
    /// LATER, idempotent export stage certifies it in place.
    ///
    /// Deliberately restricted to the ARRAY backbone, which is the class this
    /// exists for: an array refutation's ROW / extensionality leaves are still
    /// `Generic` at surface-rewrite time and are certified afterwards, and
    /// before this arm a single such leaf vetoed the repair of every genuinely
    /// defective leaf sharing the proof with it. Two downstream stages:
    ///
    /// * `promote_generic_theory_lemma_kinds_after_rewrite` re-tags a `Generic`
    ///   theory lemma whose clause matches an exact array schema
    ///   (read-over-write, row chain, store permutation) — recognized here by
    ///   the checker's OWN matcher, `ay_proof::recognize_array_theory_lemma`,
    ///   which is what that stage consults;
    /// * `promote_array_extensionality_axioms` promotes a recorded Skolemized
    ///   extensionality claim to `ArrayExtensionality` plus its witness
    ///   provenance step.
    ///
    /// Everything else — the arithmetic, string, regex and datatype funnels —
    /// stays a defect: those stages are conditional on certificate synthesis
    /// or independent re-verification succeeding, and predicting them here
    /// would let this pass pre-empt the later rebuild backbones with an
    /// unproved leaf. A `Step`-form trust leaf is never waved through either;
    /// neither stage touches that shape.
    ///
    /// This is a PREDICTION about a later stage, so it is never the last word:
    /// the acceptance gate re-validates the whole rebuilt proof with those
    /// stages actually applied.
    fn trust_leaf_certified_downstream(&self, step: &ProofStep, clause: &[TermId]) -> bool {
        let ProofStep::TheoryLemma { kind, .. } = step else {
            return false;
        };
        if !kind.is_trust() {
            return false;
        }
        if ay_proof::recognize_array_theory_lemma(&self.ctx.terms, clause)
            .is_some_and(|inferred| !inferred.is_trust())
        {
            return true;
        }
        let [unit] = clause else {
            return false;
        };
        self.recorded_array_extensionality_chain(*unit).is_some()
    }

    /// Recognize a preprocessor-derived unit `(cl T)` as an EUF-transitivity
    /// TAUTOLOGY (see [`OrTautologyPlan`]): `T` is an `or`-term with exactly
    /// one positive binary-equality disjunct `E`, implied by the remaining
    /// disjuncts via equality transitivity. Two recognized shapes, both
    /// verified with the same all-edges-used chain check the strict
    /// `eq_transitive` checker enforces (never emit what a checker rejects):
    ///
    /// - **Plain**: every other disjunct is `(not (= s t))` and the
    ///   equalities chain from `E`'s lhs to `E`'s rhs.
    /// - **De Morgan (eq_diamond family)**: some other disjunct is
    ///   `(and D1 .. Dm)` with each `Dj = (or (not (= ..)) ..)` chaining to
    ///   `E` on its own (the unused sibling disjuncts of `T` are simply
    ///   never eliminated — the derivation reaches the `T` literal without
    ///   them).
    fn plan_or_transitivity_tautology(&mut self, clause: &[TermId]) -> Option<OrTautologyPlan> {
        if clause.len() != 1 {
            return None;
        }
        let term = clause[0];
        let terms = &self.ctx.terms;
        let TermData::App(Symbol::Named(op), disjuncts) = terms.get(term) else {
            return None;
        };
        if op != "or"
            || disjuncts.len() < 2
            || disjuncts.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH
        {
            return None;
        }
        let disjuncts = disjuncts.clone();
        let decode_eq = |terms: &ay_core::TermStore, t: TermId| -> Option<(TermId, TermId)> {
            match terms.get(t) {
                TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2 => {
                    Some((args[0], args[1]))
                }
                _ => None,
            }
        };
        // Exactly one POSITIVE disjunct, and it must be a binary equality
        // (any additional positive disjunct could never be eliminated by the
        // derivation, and an ambiguous `E` is rejected outright).
        let mut eq_pos: Option<usize> = None;
        for (i, &d) in disjuncts.iter().enumerate() {
            if !matches!(terms.get(d), TermData::Not(_)) {
                if decode_eq(terms, d).is_none()
                    && !matches!(terms.get(d), TermData::App(s, _) if s.name() == "and")
                {
                    return None;
                }
                if decode_eq(terms, d).is_some() {
                    if eq_pos.is_some() {
                        return None;
                    }
                    eq_pos = Some(i);
                }
            }
        }
        let eq_pos = eq_pos?;
        let eq = disjuncts[eq_pos];
        let (lhs, rhs) = decode_eq(terms, eq)?;
        // Collect a disjunct list as negated-equality edges; `None` when any
        // entry is not `(not (= s t))`.
        let neg_edges =
            |terms: &ay_core::TermStore, lits: &[TermId]| -> Option<Vec<(TermId, TermId)>> {
                let mut edges = Vec::with_capacity(lits.len());
                for &l in lits {
                    let TermData::Not(inner) = terms.get(l) else {
                        return None;
                    };
                    edges.push(decode_eq(terms, *inner)?);
                }
                Some(edges)
            };
        // Route 1: every other disjunct is a negated equality and the whole
        // set chains lhs -> rhs.
        let others: Vec<TermId> = disjuncts
            .iter()
            .enumerate()
            .filter(|&(i, _)| i != eq_pos)
            .map(|(_, &d)| d)
            .collect();
        if let Some(edges) = neg_edges(terms, &others) {
            if Self::transitivity_chain_covers(&edges, lhs, rhs) {
                return Some(OrTautologyPlan {
                    term,
                    eq,
                    route: TautRoute::Plain { negs: others },
                });
            }
            return None;
        }
        // Route 2: an `and`-disjunct whose every conjunct is an or-term of
        // negated equalities chaining lhs -> rhs.
        'cand: for &d in &others {
            let TermData::App(Symbol::Named(n), conjs) = terms.get(d) else {
                continue;
            };
            if n != "and"
                || conjs.is_empty()
                || conjs.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH
            {
                continue;
            }
            let conjs = conjs.clone();
            let mut per_conj_negs: Vec<Vec<TermId>> = Vec::with_capacity(conjs.len());
            for &c in &conjs {
                let TermData::App(Symbol::Named(cn), lits) = terms.get(c) else {
                    continue 'cand;
                };
                if cn != "or"
                    || lits.is_empty()
                    || lits.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH
                {
                    continue 'cand;
                }
                let lits = lits.clone();
                let Some(edges) = neg_edges(terms, &lits) else {
                    continue 'cand;
                };
                if !Self::transitivity_chain_covers(&edges, lhs, rhs) {
                    continue 'cand;
                }
                per_conj_negs.push(lits);
            }
            return Some(OrTautologyPlan {
                term,
                eq,
                route: TautRoute::And {
                    and_term: d,
                    conjs,
                    per_conj_negs,
                },
            });
        }
        None
    }

    /// Whether `edges` (undirected equalities) form a path from `lhs` to
    /// `rhs` that uses EVERY edge — exactly the strict `eq_transitive`
    /// checker's acceptance condition (BFS shortest path covering all
    /// premises; a redundant premise is rejected there and so must be
    /// rejected here).
    fn transitivity_chain_covers(edges: &[(TermId, TermId)], lhs: TermId, rhs: TermId) -> bool {
        if edges.is_empty() || lhs == rhs {
            return false;
        }
        let mut adj: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for &(a, b) in edges {
            adj.entry(a).or_default().push(b);
            adj.entry(b).or_default().push(a);
        }
        let mut parent: HashMap<TermId, TermId> = HashMap::default();
        parent.insert(lhs, lhs);
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(lhs);
        while let Some(cur) = queue.pop_front() {
            if cur == rhs {
                break;
            }
            if let Some(next) = adj.get(&cur) {
                for &n in next {
                    if !parent.contains_key(&n) {
                        parent.insert(n, cur);
                        queue.push_back(n);
                    }
                }
            }
        }
        if !parent.contains_key(&rhs) {
            return false;
        }
        let mut path_len = 0usize;
        let mut cur = rhs;
        while cur != lhs {
            cur = parent[&cur];
            path_len += 1;
        }
        path_len == edges.len()
    }

    /// Emit the certified derivation of `(cl T)` for a recognized
    /// transitivity tautology (see [`OrTautologyPlan`]; the plan was
    /// chain-verified, so every emitted step passes the strict checker).
    /// Returns the id of the final unit step.
    fn emit_or_tautology_derivation(
        &mut self,
        new_proof: &mut Proof,
        plan: &OrTautologyPlan,
    ) -> ProofId {
        let (t, e) = (plan.term, plan.eq);
        // Derive `(cl E <target>)` from `negs` (the ¬e literals whose
        // equalities chain to E) against the or-term `target` that lists
        // them as disjuncts: eq_transitive + one or_neg elimination per ¬e,
        // then contraction of the accumulated duplicate `target` literals.
        let derive_eq_or = |exec: &mut Self,
                            new_proof: &mut Proof,
                            negs: &[TermId],
                            target: TermId|
         -> ProofId {
            let mut clause: Vec<TermId> = negs.to_vec();
            clause.push(e);
            let mut cur = new_proof.add_rule_step(
                AletheRule::EqTransitive,
                clause.clone(),
                Vec::new(),
                Vec::new(),
            );
            for &d in negs {
                let not_d = exec.ctx.terms.mk_not_raw(d);
                let on = new_proof.add_rule_step(
                    AletheRule::OrNeg,
                    vec![target, not_d],
                    Vec::new(),
                    Vec::new(),
                );
                if let Some(pos) = clause.iter().position(|&l| l == d) {
                    // Resolution surgery: the removed literal is the pivot `d`,
                    // already in hand — its id is not needed.
                    let _ = clause.remove(pos);
                }
                clause.push(target);
                cur = new_proof.add_resolution(clause.clone(), d, cur, on);
            }
            if negs.len() > 1 {
                clause = vec![e, target];
                cur =
                    new_proof.add_rule_step(AletheRule::Contraction, clause, vec![cur], Vec::new());
            }
            cur
        };
        // `(cl E X)` where X is the disjunct of T the outer wiring
        // eliminates (T itself on the Plain route, the and-term on the De
        // Morgan route).
        let (eq_x_unit, x) = match &plan.route {
            TautRoute::Plain { negs } => (derive_eq_or(self, new_proof, negs, t), t),
            TautRoute::And {
                and_term,
                conjs,
                per_conj_negs,
            } => {
                let (and_term, conjs) = (*and_term, conjs.clone());
                let units: Vec<ProofId> = conjs
                    .iter()
                    .zip(per_conj_negs.iter())
                    .map(|(&dj, negs)| derive_eq_or(self, new_proof, negs, dj))
                    .collect();
                let mut clause: Vec<TermId> = vec![and_term];
                for &c in &conjs {
                    clause.push(self.ctx.terms.mk_not_raw(c));
                }
                let mut cur = new_proof.add_rule_step(
                    AletheRule::AndNeg,
                    clause.clone(),
                    Vec::new(),
                    Vec::new(),
                );
                for (&dj, &unit) in conjs.iter().zip(units.iter()) {
                    let not_dj = self.ctx.terms.mk_not_raw(dj);
                    if let Some(pos) = clause.iter().position(|&l| l == not_dj) {
                        // Resolution surgery: the removed literal is `not_dj`,
                        // already in hand — its id is not needed.
                        let _ = clause.remove(pos);
                    }
                    clause.push(e);
                    cur = new_proof.add_resolution(clause.clone(), dj, cur, unit);
                }
                if conjs.len() > 1 {
                    clause = vec![and_term, e];
                    cur = new_proof.add_rule_step(
                        AletheRule::Contraction,
                        clause,
                        vec![cur],
                        Vec::new(),
                    );
                }
                (cur, and_term)
            }
        };
        // Outer wiring: `(cl T (not X))` and `(cl T (not E))` or_neg
        // tautologies eliminate X and E, contraction closes `(cl T)`.
        let mut cur = eq_x_unit;
        if x != t {
            let not_x = self.ctx.terms.mk_not_raw(x);
            let on_x =
                new_proof.add_rule_step(AletheRule::OrNeg, vec![t, not_x], Vec::new(), Vec::new());
            cur = new_proof.add_resolution(vec![e, t], x, cur, on_x);
        }
        let not_e = self.ctx.terms.mk_not_raw(e);
        let on_e =
            new_proof.add_rule_step(AletheRule::OrNeg, vec![t, not_e], Vec::new(), Vec::new());
        cur = new_proof.add_resolution(vec![t, t], e, cur, on_e);
        new_proof.add_rule_step(AletheRule::Contraction, vec![t], vec![cur], Vec::new())
    }

    /// Whether `(cl (not eq) (not p) concl)` is a valid `[1, 1, 1]`
    /// `la_generic` lemma per the independent Farkas checker (the equality
    /// `eq` and atom `p` asserted true, `concl` asserted false).
    fn triple_lemma_valid(&self, eq: TermId, p: TermId, concl: TermId) -> bool {
        self.triple_lemma_valid_with(eq, p, concl, &FarkasAnnotation::from_ints(&[1, 1, 1]))
    }

    /// [`Self::triple_lemma_valid`] against EXPLICIT Farkas coefficients (the
    /// coefficients the emitter will print, so validation and export cannot
    /// diverge).
    fn triple_lemma_valid_with(
        &self,
        eq: TermId,
        p: TermId,
        concl: TermId,
        farkas: &FarkasAnnotation,
    ) -> bool {
        let lits: Vec<TheoryLit> = [eq, p]
            .iter()
            .map(|&l| match self.ctx.terms.get(l) {
                TermData::Not(inner) => TheoryLit::new(*inner, false),
                _ => TheoryLit::new(l, true),
            })
            .chain(std::iter::once(match self.ctx.terms.get(concl) {
                TermData::Not(inner) => TheoryLit::new(*inner, true),
                _ => TheoryLit::new(concl, false),
            }))
            .collect();
        // `_linear`, NOT `_full`: the lemma exports as `la_generic`, and
        // external checkers perform no congruence reasoning inside
        // `la_generic` — the opaque ite term must cancel purely linearly.
        ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &lits,
            farkas,
        )
        .is_ok()
    }

    /// Emit a `la_generic` theory lemma `(cl a b c)` carrying `farkas`. Only
    /// called for triples already validated by [`Self::triple_lemma_valid`]
    /// / [`Self::triple_lemma_valid_with`] against THESE coefficients.
    fn add_triple_lemma(
        new_proof: &mut Proof,
        a: TermId,
        b: TermId,
        c: TermId,
        farkas: FarkasAnnotation,
    ) -> ProofId {
        new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![a, b, c],
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    fn add_ite_transfer_lemmas(
        proof: &mut Proof,
        plan: &IteLiftPlan,
        not_eq_then: TermId,
        not_eq_else: TermId,
        not_orig: TermId,
        not_bound: Option<TermId>,
    ) -> (ProofId, ProofId) {
        match not_bound {
            None => (
                Self::add_triple_lemma(
                    proof,
                    not_eq_then,
                    not_orig,
                    plan.lifted_then,
                    plan.then_coeffs.clone(),
                ),
                Self::add_triple_lemma(
                    proof,
                    not_eq_else,
                    not_orig,
                    plan.lifted_else,
                    plan.else_coeffs.clone(),
                ),
            ),
            Some(bound) => (
                Self::add_quad_lemma(
                    proof,
                    not_eq_then,
                    not_orig,
                    bound,
                    plan.lifted_then,
                    plan.then_coeffs.clone(),
                ),
                Self::add_quad_lemma(
                    proof,
                    not_eq_else,
                    not_orig,
                    bound,
                    plan.lifted_else,
                    plan.else_coeffs.clone(),
                ),
            ),
        }
    }

    /// Whether `(cl (not eq) (not p) (not q) concl)` is a valid
    /// `[1, 1, 1, 1]` `la_generic` lemma per the independent Farkas checker
    /// (the equality `eq` and atoms `p`, `q` asserted true, `concl` asserted
    /// false).
    fn quad_lemma_valid(&self, eq: TermId, p: TermId, q: TermId, concl: TermId) -> bool {
        self.quad_lemma_valid_with(eq, p, q, concl, &FarkasAnnotation::from_ints(&[1, 1, 1, 1]))
    }

    /// [`Self::quad_lemma_valid`] against EXPLICIT Farkas coefficients.
    pub(super) fn quad_lemma_valid_with(
        &self,
        eq: TermId,
        p: TermId,
        q: TermId,
        concl: TermId,
        farkas: &FarkasAnnotation,
    ) -> bool {
        let lits: Vec<TheoryLit> = [eq, p, q]
            .iter()
            .map(|&l| match self.ctx.terms.get(l) {
                TermData::Not(inner) => TheoryLit::new(*inner, false),
                _ => TheoryLit::new(l, true),
            })
            .chain(std::iter::once(match self.ctx.terms.get(concl) {
                TermData::Not(inner) => TheoryLit::new(*inner, true),
                _ => TheoryLit::new(concl, false),
            }))
            .collect();
        // `_linear`, NOT `_full` (see `triple_lemma_valid`).
        ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &lits,
            farkas,
        )
        .is_ok()
    }

    /// Emit a `la_generic` theory lemma `(cl a b c d)` carrying `farkas`.
    /// Only called for quads already validated by [`Self::quad_lemma_valid`]
    /// / [`Self::quad_lemma_valid_with`] against THESE coefficients.
    fn add_quad_lemma(
        new_proof: &mut Proof,
        a: TermId,
        b: TermId,
        c: TermId,
        d: TermId,
        farkas: FarkasAnnotation,
    ) -> ProofId {
        new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![a, b, c, d],
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Whether `(cl a b)` is a valid `[1, 1]` `la_generic` lemma per the
    /// independent Farkas checker (Int strengthening included).
    /// NORMALIZED-ASSUME MISMATCH fallback (the CAV09 QF_LIA class):
    /// [`Self::surface_bound_raw_term`] handles only pure orientation flips;
    /// here the canonical export REWROTE the linear atom itself — unary-minus
    /// spelling for `(* (- 1) x)`, elided `(* 1 x)` monomials, dropped
    /// `(* 0 x)` monomials, duplicate monomials folded into `(* x k)`,
    /// reordered sums, singleton-sum collapse. The surface comparison is
    /// re-interned PRINT-FAITHFULLY (so the `assume` spells exactly like the
    /// problem file) and bridged to the canonical literal with a certified
    /// `[1, 1]` `la_generic` orientation lemma: a raw linear atom and its
    /// canonicalization are mutually implying linear facts.
    ///
    /// Fail-closed (`None`) unless (a) the surface elaborates to EXACTLY the
    /// canonical literal (alignment gate) and (b) the independent Farkas
    /// checker certifies the bridge lemma up front.
    fn surface_linear_raw_term(
        &mut self,
        surf: &FrontendTerm,
        canonical: TermId,
    ) -> Option<(TermId, Option<TermId>)> {
        if !surface_source_is_bounded(surf) {
            return None;
        }
        let stripped = strip_frontend_annotations(surf);
        let (inner, negated) = match stripped {
            FrontendTerm::App(op, operands) if op == "not" && operands.len() == 1 => {
                (strip_frontend_annotations(&operands[0]), true)
            }
            _ => (stripped, false),
        };
        let FrontendTerm::App(head, operands) = inner else {
            return None;
        };
        if operands.len() != 2 || !matches!(head.as_str(), "<=" | "<" | ">=" | ">") {
            return None;
        }
        // Alignment gate: same atom, different spelling — nothing else.
        if self.ctx.elaborate_surface_subterm(stripped)? != canonical {
            return None;
        }
        let a = self.raw_intern_surface(&operands[0])?;
        let b = self.raw_intern_surface(&operands[1])?;
        let raw_atom = self
            .ctx
            .terms
            .mk_app(Symbol::named(head.as_str()), [a, b], Sort::Bool);
        let raw = if negated {
            self.ctx.terms.mk_not_raw(raw_atom)
        } else {
            raw_atom
        };
        if raw == canonical {
            return Some((raw, None));
        }
        let raw_complement = complement_of(&mut self.ctx.terms, raw);
        if !self.pair_lemma_valid(canonical, raw_complement) {
            return None;
        }
        Some((raw, Some(raw_atom)))
    }

    /// [`Self::surface_bound_raw_term`] with the normalized-linear-atom
    /// fallback ([`Self::surface_linear_raw_term`]).
    fn surface_bound_or_linear_raw_term(
        &mut self,
        surf: &FrontendTerm,
        canonical: TermId,
    ) -> Option<(TermId, Option<TermId>)> {
        match self.surface_bound_raw_term(surf, canonical) {
            Some((raw, None)) if raw == canonical => {
                // The ELABORATED operands reproduced the canonical term, but
                // that alone does not prove the assume would print like the
                // problem file: elaboration may have canonicalized the linear
                // operands (the CAV09 class). Only a print-faithful re-intern
                // decides; when it differs, take the certified bridge.
                if let Some(hit) = self.surface_linear_raw_term(surf, canonical) {
                    return Some(hit);
                }
                Some((raw, None))
            }
            Some(hit) => Some(hit),
            None => self.surface_linear_raw_term(surf, canonical),
        }
    }

    fn pair_lemma_valid(&self, a: TermId, b: TermId) -> bool {
        let farkas = FarkasAnnotation::from_ints(&[1, 1]);
        let lits: Vec<TheoryLit> = [a, b]
            .iter()
            .map(|&l| match self.ctx.terms.get(l) {
                TermData::Not(inner) => TheoryLit::new(*inner, true),
                _ => TheoryLit::new(l, false),
            })
            .collect();
        ay_core::proof_validation::verify_farkas_conflict_lits_full(&self.ctx.terms, &lits, &farkas)
            .is_ok()
    }

    /// Emit a `[1, 1]` `la_generic` theory lemma `(cl a b)`. Only called for
    /// pairs already validated by [`Self::pair_lemma_valid`].
    fn add_pair_lemma(new_proof: &mut Proof, a: TermId, b: TermId) -> ProofId {
        new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![a, b],
            farkas: Some(FarkasAnnotation::from_ints(&[1, 1])),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Certified orientation bridge for a top-level binary-equality flip
    /// `r` → `c` (#C2b): emits `(cl (= x y)) :rule eq_symmetric` composed
    /// with `equiv_pos1`/`equiv_pos2` and one resolution into the clause
    /// `(cl (not r) c)` (positive literals) / `(cl e' c)` with `r = (not e)`,
    /// `c = (not e')` (negated literals — the clause the caller resolves on
    /// pivot `e`). Returns `(outer resolution pivot, bridge step)`. Callers
    /// guarantee the top-level equality-flip shape.
    fn add_eq_flip_bridge(
        &mut self,
        new_proof: &mut Proof,
        r: TermId,
        c: TermId,
    ) -> (TermId, ProofId) {
        // (x, y): derive (cl (not x) y); pivot: the literal the OUTER
        // resolution eliminates from the caller's working clause.
        let (x, y, pivot) = match (self.ctx.terms.get(r), self.ctx.terms.get(c)) {
            (TermData::Not(e), TermData::Not(e_flip)) => {
                let (e, e_flip) = (*e, *e_flip);
                (e_flip, e, e)
            }
            _ => (r, c, r),
        };
        let equiv = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [x, y], Sort::Bool);
        let sym =
            new_proof.add_rule_step(AletheRule::EqSymmetric, vec![equiv], Vec::new(), Vec::new());
        let not_equiv = self.ctx.terms.mk_not_raw(equiv);
        let not_x = self.ctx.terms.mk_not_raw(x);
        // The `=` intern may have reoriented the equivalence itself: pick the
        // equiv_pos side whose conclusion is (cl (not x) y) either way.
        let interned_straight = matches!(
            self.ctx.terms.get(equiv),
            TermData::App(Symbol::Named(op), args) if op == "=" && args.len() == 2 && args[0] == x
        );
        let ep = if interned_straight {
            new_proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equiv, not_x, y],
                Vec::new(),
                Vec::new(),
            )
        } else {
            new_proof.add_rule_step(
                AletheRule::EquivPos1,
                vec![not_equiv, y, not_x],
                Vec::new(),
                Vec::new(),
            )
        };
        let bridge = new_proof.add_resolution(vec![not_x, y], equiv, ep, sym);
        (pivot, bridge)
    }

    /// Whether any assume REACHABLE from an empty-clause step is an original
    /// assertion whose exported (canonical) form would not print like the
    /// problem file — i.e. it classifies into one of the repairable assume
    /// bridge plans (expanded n-ary `distinct`, arithmetic-normalized `and`).
    /// Such proofs are checker-invalid even with ZERO trust steps: the
    /// caller uses this as a rebuild trigger alongside the trust report.
    pub(in crate::executor) fn reachable_normalized_assume(
        &mut self,
        proof: &Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        let source_index = OriginalSourceIndex::new(originals);
        if !source_index.is_valid() {
            return true;
        }
        let Some(live) = taut_surface::live_steps(proof) else {
            return true;
        };
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            let ProofStep::Assume(term) = step else {
                continue;
            };
            let Some((_, parsed)) = source_index.get(originals, *term) else {
                if source_index.is_ambiguous(*term) {
                    return true;
                }
                continue; // non-original assumes are the sibling trigger's job
            };
            // A whole-term override can make the Assume itself match while
            // leaving its downstream canonical `and_pos`/distinct steps
            // inconsistent with that printed spelling (notably a
            // deduplicated conjunction). Classification, not the presence of
            // an override, decides whether a bridge is required.
            if matches!(self.classify_assume(*term, parsed, true), Ok(Some(_))) {
                return true;
            }
        }
        false
    }

    /// Classify a (verified-original) assume for repair. `Ok(None)` = keep
    /// as-is; `Err(())` = a repair is needed but cannot be built
    /// (fail-closed: abort the whole surgery).
    fn classify_assume(
        &mut self,
        term: TermId,
        parsed: &FrontendTerm,
        overrides_kept: bool,
    ) -> Result<Option<AssumePlan>, ()> {
        if !surface_source_is_bounded(parsed) {
            return Err(());
        }
        // A `let`-wrapped surface (common in SMT-COMP inputs) hides the
        // repairable shape: expand the bindings first (pure substitution;
        // fail-closed on any capture risk). External checkers compare
        // against the same expansion (carcara: `--expand-let-bindings`).
        let expanded;
        let parsed = if matches!(strip_frontend_annotations(parsed), FrontendTerm::Let(..)) {
            match expand_surface_lets(
                strip_frontend_annotations(parsed),
                &std::collections::HashMap::new(),
            ) {
                Some(e) => {
                    expanded = e;
                    &expanded
                }
                None => return Ok(None),
            }
        } else {
            parsed
        };
        let stripped = strip_frontend_annotations(parsed);
        let FrontendTerm::App(head, operands) = stripped else {
            return Ok(None);
        };
        match head.as_str() {
            "distinct" if operands.len() >= 3 => {
                let pair_count = operands
                    .len()
                    .checked_mul(operands.len() - 1)
                    .map(|count| count / 2)
                    .ok_or(())?;
                if pair_count > taut_surface::MAX_EMITTED_CLAUSE_WIDTH {
                    return Err(());
                }
                let mut xs = Vec::with_capacity(operands.len());
                for op in operands {
                    xs.push(self.ctx.elaborate_surface_subterm(op).ok_or(())?);
                }
                let raw_xs = operands
                    .iter()
                    .map(|op| self.raw_intern_surface(op))
                    .collect::<Option<Vec<TermId>>>()
                    .ok_or(())?;
                if raw_xs != xs {
                    // The bridge below proves only the `distinct_elim` of
                    // these exact operands. A nested source rewrite needs its
                    // own derivation; never authorize the canonicalized
                    // shallow surrogate as an authored premise.
                    return Err(());
                }
                // The exported assume must be the pairwise `i < j` expansion
                // (exactly the `distinct_elim` conjunct order).
                let TermData::App(Symbol::Named(name), conjs) = self.ctx.terms.get(term) else {
                    return Err(());
                };
                if name != "and" {
                    return Err(());
                }
                if conjs.len() != pair_count {
                    return Err(());
                }
                let conjs = conjs.clone();
                let mut k = 0;
                for i in 0..xs.len() {
                    for j in (i + 1)..xs.len() {
                        let TermData::Not(inner) = self.ctx.terms.get(conjs[k]) else {
                            return Err(());
                        };
                        let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(*inner)
                        else {
                            return Err(());
                        };
                        if op != "=" || args.len() != 2 || args[0] != xs[i] || args[1] != xs[j] {
                            return Err(());
                        }
                        k += 1;
                    }
                }
                let raw = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("distinct"), raw_xs, Sort::Bool);
                if !matches!(
                    self.ctx.terms.get(raw),
                    TermData::App(Symbol::Named(op), args) if op == "distinct" && args.len() == xs.len()
                ) {
                    return Err(());
                }
                Ok(Some(AssumePlan::Distinct {
                    raw,
                    and_term: term,
                    conjs,
                }))
            }
            "and" => {
                if operands.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH {
                    return Err(());
                }
                let TermData::App(Symbol::Named(name), conjs) = self.ctx.terms.get(term) else {
                    return Err(());
                };
                if name != "and" || conjs.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH {
                    return Err(());
                }
                let conjs = conjs.clone();
                // A `distinct`-sugar operand (exported canonically as
                // `(not (= s t))` / its pairwise expansion, whose print no
                // longer matches the file) switches the scan into the
                // full-alignment `AndDistinct` mode. Without distinct sugar
                // the historical bounds-only behavior below is preserved
                // byte-for-byte.
                if operands.iter().any(|surf| {
                    matches!(strip_frontend_annotations(surf),
                        FrontendTerm::App(h, args) if h == "distinct" && args.len() >= 2)
                }) {
                    return self.classify_and_distinct(term, &conjs, operands);
                }
                if conjs.len() != operands.len() {
                    // Canonicalization FOLDED or DEDUPLICATED whole conjuncts
                    // away (e.g. a duplicated linear atom kept once): the
                    // positional bounds pairing below is impossible, but the
                    // alignment-capable `AndDistinct` classifier handles the
                    // skew (fail-open to keeping the assume as-is).
                    return self.classify_and_distinct(term, &conjs, operands);
                }
                let mut raws: Vec<(TermId, Option<TermId>)> = Vec::with_capacity(conjs.len());
                let mut any_bridge = false;
                let mut any_unshaped = false;
                for (surf, &conj) in operands.iter().zip(conjs.iter()) {
                    let Some((raw, bridge)) = self.surface_bound_or_linear_raw_term(surf, conj)
                    else {
                        // Not a bound-literal conjunct (e.g. an `or`-term in
                        // a CNF-shaped conjunction). Whether this vetoes the
                        // surgery is decided after the scan: a conjunction
                        // with NO orientation-bridged conjunct at all is not
                        // the arithmetic-normalized-bounds class and is kept
                        // as-is; a MIX of bridged and unshaped conjuncts is
                        // unrepairable (fail-closed, as before).
                        any_unshaped = true;
                        continue;
                    };
                    // Verify the orientation bridge certificate up front
                    // (fail-closed before any emission).
                    if bridge.is_some() {
                        let raw_complement = complement_of(&mut self.ctx.terms, raw);
                        if !self.pair_lemma_valid(conj, raw_complement) {
                            return Err(());
                        }
                        any_bridge = true;
                    } else if raw != conj {
                        return Err(());
                    }
                    raws.push((raw, bridge));
                }
                if any_unshaped {
                    if any_bridge {
                        return Err(());
                    }
                    // No conjunct needs repair: the assume prints as it
                    // always did — keep it rather than vetoing the whole
                    // surgery (other defect classes in the same proof may
                    // still be repairable).
                    return Ok(None);
                }
                if !any_bridge {
                    // Every conjunct already IS its canonical form: the
                    // exported assume prints like the file. Keep it.
                    return Ok(None);
                }
                let raw_and = self.ctx.terms.mk_app(
                    Symbol::named("and"),
                    raws.iter().map(|&(r, _)| r).collect::<Vec<_>>(),
                    Sort::Bool,
                );
                if !matches!(
                    self.ctx.terms.get(raw_and),
                    TermData::App(Symbol::Named(op), args) if op == "and" && args.len() == raws.len()
                ) {
                    return Err(());
                }
                Ok(Some(AssumePlan::AndBounds {
                    raw_and,
                    raws,
                    conjs,
                }))
            }
            "<" | "<=" | ">" | ">=" | "not" => {
                // A plain bound literal whose canonical orientation differs
                // from the surface spelling (e.g. `(> a 5)` vs `(< 5 a)`).
                // When surface overrides survive the surgery (ite-lift
                // class), an override-covered literal already prints
                // correctly and must not be planned (a plan would trip the
                // ite-lift exclusivity abort and leave the WHOLE proof
                // unrepaired). When overrides are purged, the same literal
                // MUST be bridged: its canonical print no longer matches.
                // No bridge needed when the raw term IS the canonical one;
                // unsupported shapes are kept as-is (they printed without
                // the surgery's help before, and the surgery fails closed on
                // its trust-free check if that ever stops holding).
                if overrides_kept
                    && self
                        .last_proof_term_overrides
                        .as_ref()
                        .is_some_and(|m| m.contains_key(&term))
                {
                    return Ok(None);
                }
                match self.surface_bound_or_linear_raw_term(parsed, term) {
                    Some((raw, Some(atom))) => {
                        let raw_complement = complement_of(&mut self.ctx.terms, raw);
                        if !self.pair_lemma_valid(term, raw_complement) {
                            return Err(());
                        }
                        Ok(Some(AssumePlan::Literal {
                            raw,
                            atom,
                            canonical: term,
                        }))
                    }
                    Some((_, None)) | None => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }

    /// Authenticate the declaration identity selected while elaborating one
    /// surface application.
    ///
    /// `Ok(Some(symbol))` means elaboration retained the exact identity of one
    /// live declaration with this surface name. `Ok(None)` means no live
    /// declaration has the spelling, so rebuilding a builtin-shaped raw head
    /// is safe. A live declaration whose identity is absent or ambiguous is an
    /// authority mismatch and returns `Err(())`.
    fn authenticated_surface_application_symbol(
        &self,
        surface_head: &str,
        elaborated: TermId,
    ) -> Result<Option<Symbol>, ()> {
        let elaborated_symbol = match self.ctx.terms.get(elaborated) {
            TermData::App(symbol @ Symbol::Named(_), _) => Some(symbol.clone()),
            _ => None,
        };
        let elaborated_identity = match elaborated_symbol.as_ref() {
            Some(Symbol::Named(identity)) => Some(identity.as_str()),
            _ => None,
        };

        let mut has_surface_declaration = false;
        let mut exact_matches = 0_usize;
        for (surface, info) in self.ctx.symbol_iter() {
            if surface.as_str() != surface_head {
                continue;
            }
            has_surface_declaration = true;
            if elaborated_identity
                .is_some_and(|identity| self.ctx.symbol_identity_name(surface, info) == identity)
            {
                exact_matches += 1;
            }
        }

        match (has_surface_declaration, exact_matches) {
            (false, 0) => Ok(None),
            (true, 1) => elaborated_symbol.map(Some).ok_or(()),
            // A declaration is live but elaboration either folded/expanded it
            // away or did not select one unique identity. Reconstructing the
            // source spelling as a canonical builtin would grant the wrong
            // premise semantics, so proof repair must fail closed.
            _ => Err(()),
        }
    }

    /// Classify a surface conjunction containing `distinct` sugar against
    /// its canonical export (see [`AssumePlan::AndDistinct`]). The canonical
    /// conjunction may have FOLDED trivial operands away (`(= c c)` ->
    /// `true`), DEDUPLICATED repeated conjuncts, and EXPANDED n-ary
    /// `distinct` operands into pairwise blocks — the scan aligns the
    /// surface operands with the canonical conjuncts in order, fail-open to
    /// `Ok(None)` (keep the assume as-is; the surgery's trust-free check
    /// still decides overall success) on anything unalignable.
    fn classify_and_distinct(
        &mut self,
        term: TermId,
        conjs: &[TermId],
        operands: &[FrontendTerm],
    ) -> Result<Option<AssumePlan>, ()> {
        if conjs.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH
            || operands.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH
        {
            return Err(());
        }
        let mut units: Vec<AndDistinctUnit> = Vec::new();
        let mut raws: Vec<TermId> = Vec::with_capacity(operands.len());
        let mut k = 0usize;
        for (pos, surf) in operands.iter().enumerate() {
            #[allow(clippy::cast_possible_truncation)]
            let pos = pos as u32;
            let stripped = strip_frontend_annotations(surf);
            if let FrontendTerm::App(head, ops) = stripped {
                if head == "distinct" && ops.len() >= 2 {
                    let m = ops
                        .len()
                        .checked_mul(ops.len() - 1)
                        .map(|count| count / 2)
                        .ok_or(())?;
                    if m > taut_surface::MAX_EMITTED_CLAUSE_WIDTH
                        || k.checked_add(m).is_none_or(|end| end > conjs.len())
                    {
                        return Err(());
                    }
                    let Some(xs) = ops
                        .iter()
                        .map(|op| self.ctx.elaborate_surface_subterm(op))
                        .collect::<Option<Vec<TermId>>>()
                    else {
                        return Ok(None);
                    };
                    let Some(raw_xs) = ops
                        .iter()
                        .map(|op| self.raw_intern_surface(op))
                        .collect::<Option<Vec<TermId>>>()
                    else {
                        return Ok(None);
                    };
                    // `distinct_elim` below bridges the raw `distinct` only
                    // when its operands are the exact canonical operands used
                    // by the expansion. If a nested source operand itself
                    // folds/reorders, admitting the canonicalized term as an
                    // authored premise would be a provenance violation; such
                    // a case needs an additional explicit rewrite proof.
                    if raw_xs != xs {
                        return Err(());
                    }
                    let raw = self
                        .ctx
                        .terms
                        .mk_app(Symbol::named("distinct"), raw_xs, Sort::Bool);
                    if !matches!(
                        self.ctx.terms.get(raw),
                        TermData::App(Symbol::Named(op), args)
                            if op == "distinct" && args.len() == xs.len()
                    ) {
                        return Ok(None);
                    }
                    // The canonical export is the pairwise `i < j` block.
                    let mut kk = k;
                    for i in 0..xs.len() {
                        for j in (i + 1)..xs.len() {
                            let TermData::Not(inner) = self.ctx.terms.get(conjs[kk]) else {
                                return Ok(None);
                            };
                            let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(*inner)
                            else {
                                return Ok(None);
                            };
                            if op != "=" || args.len() != 2 || args[0] != xs[i] || args[1] != xs[j]
                            {
                                return Ok(None);
                            }
                            kk += 1;
                        }
                    }
                    let kind = if xs.len() == 2 {
                        AndDistinctKind::DistinctBinary
                    } else {
                        // The expansion conjunction itself (for the
                        // `distinct_elim` equivalence + `and_pos` splits).
                        let Some(block) = self.ctx.elaborate_surface_subterm(surf) else {
                            return Ok(None);
                        };
                        let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(block)
                        else {
                            return Ok(None);
                        };
                        if op != "and" || args.as_slice() != &conjs[k..k + m] {
                            return Ok(None);
                        }
                        #[allow(clippy::cast_possible_truncation)]
                        AndDistinctKind::DistinctNary {
                            and_term: block,
                            count: m as u32,
                        }
                    };
                    units.push(AndDistinctUnit { pos, raw, kind });
                    raws.push(raw);
                    k += m;
                    continue;
                }
            }
            let Some(elab) = self.ctx.elaborate_surface_subterm(surf) else {
                return Ok(None);
            };
            if self.ctx.terms.is_true(elab) || conjs[..k].contains(&elab) {
                // Folded-away (`(= c c)`) or deduplicated conjunct: present
                // in the raw print only, supplies no unit.
                let Some(raw) = self.raw_intern_surface(surf) else {
                    return Ok(None);
                };
                raws.push(raw);
                continue;
            }
            if k < conjs.len() && elab == conjs[k] {
                let conj = conjs[k];
                if let Some((raw, bridge)) = self.surface_bound_or_linear_raw_term(surf, conj) {
                    let kind = match bridge {
                        Some(atom) => {
                            let raw_complement = complement_of(&mut self.ctx.terms, raw);
                            if !self.pair_lemma_valid(conj, raw_complement) {
                                return Ok(None);
                            }
                            AndDistinctKind::Arith { atom }
                        }
                        None => {
                            if raw != conj {
                                return Ok(None);
                            }
                            AndDistinctKind::Plain
                        }
                    };
                    units.push(AndDistinctUnit { pos, raw, kind });
                    raws.push(raw);
                } else {
                    // A plain conjunct: keep the CANONICAL term as the raw
                    // conjunct (the strict checker then sees a fully
                    // id-consistent proof), accepted only when its print
                    // differs from the file by AT MOST binary-equality
                    // orientation — the one difference carcara's default
                    // mode tolerates everywhere. Anything else (`distinct`
                    // sugar, canonicalization that reordered an `or`, ...)
                    // would print unlike the file: keep the assume as-is.
                    let Some(raw) = self.raw_intern_surface(surf) else {
                        return Ok(None);
                    };
                    if !eq_flip_equivalent(&self.ctx.terms, raw, conj) {
                        // Last chance (#C2b): an `or`-conjunct whose
                        // canonical export reordered the disjuncts and/or
                        // flipped binary-equality orientations. The RAW
                        // disjunction (file order + orientations) is kept
                        // for the assume and bridged per-literal.
                        let Some(lits) = taut_surface::or_perm_lits(&self.ctx.terms, raw, conj)
                        else {
                            return Ok(None);
                        };
                        units.push(AndDistinctUnit {
                            pos,
                            raw,
                            kind: AndDistinctKind::OrPerm { lits },
                        });
                        raws.push(raw);
                        k += 1;
                        continue;
                    }
                    units.push(AndDistinctUnit {
                        pos,
                        raw: conj,
                        kind: AndDistinctKind::Plain,
                    });
                    raws.push(conj);
                }
                k += 1;
                continue;
            }
            return Ok(None);
        }
        if k != conjs.len() {
            return Ok(None);
        }
        if units
            .iter()
            .all(|u| matches!(u.kind, AndDistinctKind::Plain))
            && raws.len() == conjs.len()
        {
            // Nothing to repair: the canonical print already matches.
            return Ok(None);
        }
        let raw_and = self
            .ctx
            .terms
            .mk_app(Symbol::named("and"), raws.clone(), Sort::Bool);
        if !matches!(
            self.ctx.terms.get(raw_and),
            TermData::App(Symbol::Named(op), args) if op == "and" && args.len() == raws.len()
        ) {
            return Ok(None);
        }
        Ok(Some(AssumePlan::AndDistinct {
            raw_and,
            and_term: term,
            units,
            conjs: conjs.to_vec(),
        }))
    }

    /// Preprocessor fold-to-`false` collapse repair (#trust-count→0,
    /// carcara-invalid→valid). When the PREPROCESSOR itself derives the
    /// contradiction (e.g. `(assert (distinct x x))`, `(assert (= 1 2))`,
    /// `(assert (and p (not p)))`), the exported proof degenerates to the
    /// 3-step shape
    ///
    /// ```text
    /// (assume t0 X)
    /// (step t1 (cl (not X)) :rule false :args (X))   ; NOT the Alethe `false`
    /// (step t2 (cl) :rule resolution :premises (t0 t1))
    /// ```
    ///
    /// whose `:rule false` step misuses the Alethe `false` rule (`⊢ (cl (not
    /// false))`) and is rejected by external checkers. This pass recognizes
    /// the whole-proof shape and re-proves `(cl (not X))` from the ORIGINAL
    /// assertion `X`'s own structure with certified steps:
    ///
    /// - **`(distinct .. t .. t ..)` with a syntactically duplicated operand**
    ///   — `distinct_elim` + `equiv_pos2` (+ `and_pos` for the n-ary
    ///   conjunction form) down to `(not (= t t))`, refuted by
    ///   `eq_reflexive`.
    /// - **ground linear-arithmetic literal falsity** — derive the complement
    ///   of an authored `=`, `<`, `<=`, `>`, or `>=` atom (optionally under one
    ///   `not`) through either a sign-resolved, independently re-verified
    ///   `la_generic` row or a primitive checked `evaluate` derivation.
    /// - **`(and .. p .. (not p) ..)` with a syntactically complementary
    ///   conjunct pair** — two `and_pos` extractions resolved to `⊥`.
    ///
    /// Fail-closed: any other assertion shape (or a failed certificate)
    /// leaves the proof byte-identical, keeping the honest defective step
    /// visible rather than fabricating an unchecked derivation.
    ///
    /// The collapse's assume holds the FOLDED canonical term (`false`), so
    /// shape dispatch uses the parsed ORIGINAL assertion whose canonical form
    /// is that assumed term. Repairs either use the immutable, index-aligned
    /// authored root directly or reconstruct exact raw source syntax; a
    /// normalized re-elaboration is never admitted as premise authority.
    pub(in crate::executor) fn try_rebuild_false_collapse(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
        authored_originals: &[(TermId, FrontendTerm)],
        allow_premise_binding_fallback: bool,
    ) -> bool {
        let Some(FalseCollapseShape {
            assume,
            assume_count,
            false_step,
            trust_false,
            lia_lemma,
        }) = self.recognize_false_collapse_shape(proof)
        else {
            return false;
        };
        // Substitution-chain shape: equality assumes closed by ONE
        // `lia_generic` lemma (an external checker HOLE). Re-prove from the
        // original equalities with a synthesized, re-verified `la_generic`
        // certificate (fail-closed: any non-equality original keeps the
        // proof unchanged).
        if lia_lemma {
            if trust_false || false_step.is_some() || assume_count == 0 {
                return false;
            }
            return self.rebuild_consumed_equalities_collapse(proof, originals);
        }
        // Shape C: the preprocessor consumed the assertions entirely — the
        // proof is the bare `(cl false) :rule trust` (no assume, no
        // derivation). Re-prove from the ORIGINAL arithmetic-equality
        // assertions with a synthesized, re-verified Farkas certificate.
        if trust_false {
            // Any accompanying `false` step must be the proper-form wiring
            // `(cl (not false))` for `(cl false)`'s refutation.
            let wiring_ok = match false_step {
                None => true,
                Some((lit, arg)) => {
                    matches!(
                        self.ctx.terms.get(arg),
                        TermData::Const(ay_core::term::Constant::Bool(false))
                    ) && atom_of(&self.ctx.terms, lit) == arg
                        && lit != arg
                }
            };
            if assume_count == 0 && wiring_ok {
                return self.rebuild_consumed_equalities_collapse(proof, originals)
                    || self.rebuild_congruence_collapse(proof, originals)
                    // Last resort (#dt-premise-binding): neither certified
                    // rebuild applies (e.g. a DATATYPE refutation — Alethe has
                    // no datatype rules, and neither does any checker). Still
                    // bind the premises: see the doc comment.
                    || (allow_premise_binding_fallback
                        && self.rebuild_premise_binding_collapse(proof, originals));
            }
            return false;
        }
        if assume_count != 1 {
            return false;
        }
        let (Some(x), Some((neg_lit, arg))) = (assume, false_step) else {
            return false;
        };
        if arg != x || atom_of(&self.ctx.terms, neg_lit) != x || neg_lit == x {
            return false;
        }

        self.try_rebuild_false_collapse_from_originals(proof, x, originals, authored_originals)
    }

    /// `(distinct ..)` with a syntactically duplicated operand: derive
    /// `(not (= t t))` via `distinct_elim` + `equiv_pos2` (+ `and_pos` for
    /// n-ary) and refute it with `eq_reflexive`.
    fn rebuild_duplicate_distinct_collapse(
        &mut self,
        proof: &mut Proof,
        operands: &[FrontendTerm],
    ) -> bool {
        let mut args = Vec::with_capacity(operands.len());
        for op in operands {
            let Some(t) = self.ctx.elaborate_surface_subterm(op) else {
                return false;
            };
            args.push(t);
        }
        let args = &args[..];
        // Re-intern the folded `distinct` application RAW: the new assume
        // must print like the problem file. Fail-closed if the interner
        // folds it (the derivation would not match the premise).
        let x = self
            .ctx
            .terms
            .mk_app(Symbol::named("distinct"), args, Sort::Bool);
        if !matches!(
            self.ctx.terms.get(x),
            TermData::App(Symbol::Named(op), a) if op == "distinct" && a.len() == args.len()
        ) {
            return false;
        }
        let n = args.len();
        let Some((di, dj)) = (0..n)
            .flat_map(|i| ((i + 1)..n).map(move |j| (i, j)))
            .find(|&(i, j)| args[i] == args[j])
        else {
            return false;
        };
        // Carcara's `distinct_elim` special-cases >2 Bool operands (they
        // collapse to `false`, a different bridge): out of scope.
        if n > 2 && matches!(self.ctx.terms.sort(args[0]), Sort::Bool) {
            return false;
        }
        let terms = &mut self.ctx.terms;
        let dup = args[di];
        let eq_dup = terms.mk_app(Symbol::named("="), [dup, dup], Sort::Bool);
        if !matches!(
            terms.get(eq_dup),
            TermData::App(Symbol::Named(op), a) if op == "=" && a.len() == 2 && a[0] == dup && a[1] == dup
        ) {
            return false;
        }
        let not_eq_dup = terms.mk_not_raw(eq_dup);
        let not_x = terms.mk_not_raw(x);

        let mut new_proof = Proof::new();
        let assume_id = new_proof.add_assume(x, None);
        if n == 2 {
            // (= (distinct t t) (not (= t t)))
            let equiv = terms.mk_app(Symbol::named("="), [x, not_eq_dup], Sort::Bool);
            let not_equiv = terms.mk_not_raw(equiv);
            let de = new_proof.add_rule_step(
                AletheRule::DistinctElim,
                vec![equiv],
                Vec::new(),
                Vec::new(),
            );
            let ep = new_proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equiv, not_x, not_eq_dup],
                Vec::new(),
                Vec::new(),
            );
            let r1 = new_proof.add_resolution(vec![not_x, not_eq_dup], equiv, ep, de);
            let r2 = new_proof.add_resolution(vec![not_eq_dup], x, r1, assume_id);
            let er = new_proof.add_rule_step(
                AletheRule::EqReflexive,
                vec![eq_dup],
                Vec::new(),
                Vec::new(),
            );
            new_proof.add_resolution(Vec::new(), eq_dup, r2, er);
        } else {
            // (= (distinct x1..xn) (and (not (= xi xj)) ..)) in `i < j` order.
            let mut conjs: Vec<TermId> = Vec::with_capacity(n * (n - 1) / 2);
            let mut dup_pos = 0usize;
            let mut k = 0usize;
            for i in 0..n {
                for j in (i + 1)..n {
                    let eq = terms.mk_app(Symbol::named("="), [args[i], args[j]], Sort::Bool);
                    conjs.push(terms.mk_not_raw(eq));
                    if (i, j) == (di, dj) {
                        dup_pos = k;
                    }
                    k += 1;
                }
            }
            let and_term = terms.mk_app(Symbol::named("and"), conjs.clone(), Sort::Bool);
            if !matches!(
                terms.get(and_term),
                TermData::App(Symbol::Named(op), a) if op == "and" && a.len() == conjs.len()
            ) {
                return false;
            }
            let not_and = terms.mk_not_raw(and_term);
            let equiv = terms.mk_app(Symbol::named("="), [x, and_term], Sort::Bool);
            let not_equiv = terms.mk_not_raw(equiv);
            let de = new_proof.add_rule_step(
                AletheRule::DistinctElim,
                vec![equiv],
                Vec::new(),
                Vec::new(),
            );
            let ep = new_proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equiv, not_x, and_term],
                Vec::new(),
                Vec::new(),
            );
            let r1 = new_proof.add_resolution(vec![not_x, and_term], equiv, ep, de);
            let r2 = new_proof.add_resolution(vec![and_term], x, r1, assume_id);
            #[allow(clippy::cast_possible_truncation)]
            let ap = new_proof.add_rule_step(
                AletheRule::AndPos(dup_pos as u32),
                vec![not_and, conjs[dup_pos]],
                Vec::new(),
                Vec::new(),
            );
            let r3 = new_proof.add_resolution(vec![conjs[dup_pos]], and_term, ap, r2);
            let er = new_proof.add_rule_step(
                AletheRule::EqReflexive,
                vec![eq_dup],
                Vec::new(),
                Vec::new(),
            );
            new_proof.add_resolution(Vec::new(), eq_dup, r3, er);
        }
        *proof = new_proof;
        true
    }

    /// `(and .. p .. (not p) ..)` with a syntactically complementary conjunct
    /// pair: two `and_pos` extractions resolved to the empty clause.
    fn rebuild_complementary_and_collapse(
        &mut self,
        proof: &mut Proof,
        authored_root: TermId,
        surface_arity: usize,
    ) -> bool {
        // The assumption authority is the immutable, index-aligned problem
        // root. Never rebuild this premise by elaborating the parsed operands:
        // comparison normalization can turn an authored
        // `(and (not (> x 10)) (> x 10))` into the derived
        // `(and (not (< 10 x)) (< 10 x))`, which is equivalent but is not an
        // asserted formula. Parsed syntax is used only to verify the arity.
        let x = authored_root;
        if !matches!(
            self.ctx.terms.get(x),
            TermData::App(Symbol::Named(op), a) if op == "and" && a.len() == surface_arity
        ) {
            return false;
        }
        // Collect every Bool node reachable through the `and`-tree of `x`,
        // recording the path (child indices) from the root. The complementary
        // pair need NOT be two top-level conjuncts: a conjunct may itself be a
        // nested `(and ..)`, so a literal `p` can sit one or more levels deep
        // while its complement `(not p)` is a sibling conjunct (the class
        // `(and .. (and .. p) .. (not p) ..)`). Each node's unit is derived by
        // the strictly-validated `and_pos` + resolution chain down its path.
        let mut nodes: Vec<(TermId, Vec<u32>)> = Vec::new();
        {
            let mut stack: Vec<(TermId, Vec<u32>)> = vec![(x, Vec::new())];
            while let Some((t, path)) = stack.pop() {
                if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) {
                    if name == "and" && !args.is_empty() {
                        let args = args.clone();
                        // Reverse push keeps the pop order left-to-right.
                        for (i, &child) in args.iter().enumerate().rev() {
                            let Ok(pos) = u32::try_from(i) else { continue };
                            let mut cp = path.clone();
                            cp.push(pos);
                            stack.push((child, cp));
                        }
                        continue;
                    }
                }
                if matches!(self.ctx.terms.sort(t), Sort::Bool) {
                    nodes.push((t, path));
                }
            }
        }
        // First-occurrence path per node (shortest is fine; any valid
        // extraction closes the proof). A node reachable only as the root `x`
        // itself is never recorded (the root is an `and`, descended above).
        let mut node_path: HashMap<TermId, Vec<u32>> = HashMap::default();
        for (t, p) in &nodes {
            node_path.entry(*t).or_insert_with(|| p.clone());
        }
        // Find a complementary pair `p` / `(not p)` where both are reachable.
        let Some((pos_term, neg_term)) = nodes.iter().find_map(|(t, _)| {
            let TermData::Not(inner) = self.ctx.terms.get(*t) else {
                return None;
            };
            let inner = *inner;
            node_path.contains_key(&inner).then_some((inner, *t))
        }) else {
            return false;
        };
        let pos_path = node_path[&pos_term].clone();
        let neg_path = node_path[&neg_term].clone();

        let mut new_proof = Proof::new();
        let assume_id = new_proof.add_assume(x, None);
        let (Some(pos_unit), Some(neg_unit)) = (
            Self::emit_and_pos_chain(
                &mut self.ctx.terms,
                &mut new_proof,
                assume_id,
                x,
                &pos_path,
                pos_term,
            ),
            Self::emit_and_pos_chain(
                &mut self.ctx.terms,
                &mut new_proof,
                assume_id,
                x,
                &neg_path,
                neg_term,
            ),
        ) else {
            return false;
        };
        new_proof.add_resolution(Vec::new(), pos_term, neg_unit, pos_unit);
        if !matches!(
            ay_proof::check_proof_strict(&new_proof, &self.ctx.terms),
            Ok(quality) if quality.trust_count == 0
        ) || ay_proof::validate_reachable_assumes_in_problem_scope(&new_proof, &[authored_root])
            .is_err()
        {
            return false;
        }
        *proof = new_proof;
        true
    }

    /// `(and c1 .. cn)` of pure linear-arithmetic atoms whose conjunction is
    /// arithmetically infeasible (the CAV09 fold-to-false family): synthesize
    /// a Farkas certificate over the POSITIVE pure-linear conjuncts with the
    /// LRA solver, keep only the conjuncts carrying a NONZERO coefficient
    /// (the certificate identifies exactly the participating atoms, so large
    /// conjunctions do not degenerate into one `and_pos` per conjunct),
    /// independently re-verify the pruned certificate at external
    /// `la_generic` strength plus a printable equality-sign orientation, and
    /// derive `and_pos` extraction + one `la_generic` lemma + resolutions to
    /// the empty clause. Fail-closed: negated/impure/duplicated conjuncts
    /// never enter the candidate set, and any failed synthesis or
    /// re-verification keeps the proof byte-identical.
    fn rebuild_linear_and_collapse(
        &mut self,
        proof: &mut Proof,
        operands: &[FrontendTerm],
    ) -> bool {
        let mut conjs = Vec::with_capacity(operands.len());
        for op in operands {
            let Some(t) = self.raw_intern_surface(op) else {
                return false;
            };
            conjs.push(t);
        }
        // Re-intern the folded conjunction RAW (see the distinct emitter).
        let x = self
            .ctx
            .terms
            .mk_app(Symbol::named("and"), conjs.clone(), Sort::Bool);
        if !matches!(
            self.ctx.terms.get(x),
            TermData::App(Symbol::Named(op), a) if op == "and" && a.len() == conjs.len()
        ) {
            return false;
        }
        // Candidate conjuncts: POSITIVE pure linear-arithmetic atoms, first
        // occurrence only (a duplicated conjunct would double-count its
        // coefficient position; the first extraction suffices).
        let mut cand: Vec<usize> = Vec::new();
        for (i, &c) in conjs.iter().enumerate() {
            let pure = match self.ctx.terms.get(c) {
                TermData::App(Symbol::Named(op), args) if args.len() == 2 => match op.as_str() {
                    "<=" | "<" | ">=" | ">" => args
                        .iter()
                        .all(|&a| term_is_pure_linear_arith(&self.ctx.terms, a)),
                    "=" => equality_is_pure_linear_arith(&self.ctx.terms, c),
                    _ => false,
                },
                _ => false,
            };
            if pure && !conjs[..i].contains(&c) {
                cand.push(i);
            }
        }
        if cand.is_empty() {
            return false;
        }
        // Synthesize the certificate: assert ALL candidates into a fresh LRA
        // solver; the returned conflict names exactly the participating
        // atoms with their coefficients (so large conjunctions do not
        // degenerate into one `and_pos` per conjunct).
        let mut lra = ay_lra::LraSolver::new(&self.ctx.terms);
        lra.set_combined_theory_mode(true);
        for &i in &cand {
            ay_core::TheorySolver::register_atom(&mut lra, conjs[i]);
        }
        for &i in &cand {
            ay_core::TheorySolver::assert_literal(&mut lra, conjs[i], true);
        }
        let (lits, all) = match ay_core::TheorySolver::check(&mut lra) {
            ay_core::TheoryResult::UnsatWithFarkas(conflict) => {
                let lits = conflict.literals;
                match conflict.farkas {
                    Some(f) if f.coefficients.len() == lits.len() => (lits, f),
                    // No (or misaligned) certificate metadata: fall back to
                    // the all-ones candidate, judged solely by the
                    // independent re-verification below.
                    _ => {
                        let ones = FarkasAnnotation::from_ints(&vec![1i64; lits.len()]);
                        (lits, ones)
                    }
                }
            }
            // A conflict without Farkas metadata (e.g. a single conjunct
            // whose linear form cancels to `0 <= -1`): all-ones candidate,
            // fail-closed on the re-verification below.
            ay_core::TheoryResult::Unsat(lits) => {
                let ones = FarkasAnnotation::from_ints(&vec![1i64; lits.len()]);
                (lits, ones)
            }
            _ => return false,
        };
        if lits.is_empty() {
            return false;
        }
        // Map the conflict literals back to conjunct positions, dropping
        // zero-coefficient entries. Fail-closed on any literal that is not a
        // positively-asserted candidate conjunct (or appears twice).
        let mut sel: Vec<usize> = Vec::new();
        let mut coeffs = Vec::new();
        for (lit, coef) in lits.iter().zip(all.coefficients.iter()) {
            if num_traits::Zero::is_zero(coef) {
                continue;
            }
            if !lit.value {
                return false;
            }
            let Some(&i) = cand.iter().find(|&&i| conjs[i] == lit.term) else {
                return false;
            };
            if sel.contains(&i) {
                return false;
            }
            sel.push(i);
            coeffs.push(*coef);
        }
        // Deterministic conjunct order for stable printing.
        let mut order: Vec<usize> = (0..sel.len()).collect();
        order.sort_by_key(|&k| sel[k]);
        let sel: Vec<usize> = order.iter().map(|&k| sel[k]).collect();
        let coeffs: Vec<_> = order.iter().map(|&k| coeffs[k]).collect();
        if sel.is_empty() {
            return false;
        }
        let farkas = FarkasAnnotation::new(coeffs);
        let sel_conjs: Vec<TermId> = sel.iter().map(|&i| conjs[i]).collect();
        // Independent re-verification at external `la_generic` strength
        // (no congruence), plus the printable sign orientation (fail-closed).
        let conflict: Vec<TheoryLit> = sel_conjs.iter().map(|&c| TheoryLit::new(c, true)).collect();
        if ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_err()
        {
            return false;
        }
        if ay_core::proof_validation::resolve_equality_coefficient_signs(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_none()
        {
            return false;
        }
        let terms = &mut self.ctx.terms;
        let not_x = terms.mk_not_raw(x);
        let clause: Vec<TermId> = sel_conjs.iter().map(|&c| terms.mk_not_raw(c)).collect();
        let mut new_proof = Proof::new();
        let assume_id = new_proof.add_assume(x, None);
        let mut units: Vec<ProofId> = Vec::with_capacity(sel.len());
        for (&i, &c) in sel.iter().zip(sel_conjs.iter()) {
            #[allow(clippy::cast_possible_truncation)]
            let ap = new_proof.add_rule_step(
                AletheRule::AndPos(i as u32),
                vec![not_x, c],
                Vec::new(),
                Vec::new(),
            );
            units.push(new_proof.add_resolution(vec![c], x, ap, assume_id));
        }
        let lemma = new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: clause.clone(),
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        let mut current = lemma;
        for (k, (&c, &uid)) in sel_conjs.iter().zip(units.iter()).enumerate() {
            current = new_proof.add_resolution(clause[k + 1..].to_vec(), c, current, uid);
        }
        *proof = new_proof;
        // `x` is recursively raw-interned from the parsed conjunction above,
        // and the independently checked Farkas rebuild has now succeeded.
        // Record that exact source term so the final exporter accepts the
        // rebuilt Assume without granting authority to any generated leaf.
        self.record_rebuilt_authored_proof_premise(x);
        true
    }

    /// Consumed-assertions collapse whose contradiction is pure EUF
    /// CONGRUENCE (`(= a b)` together with `(not (= (f .. a ..) (f .. b ..)))`):
    /// the preprocessor rewrote one side into the other, folded the result,
    /// and the exported proof is the bare `(cl false) :rule trust`.
    ///
    /// Re-prove it from the ORIGINAL assertions with a single `cong` step —
    /// a first-class Alethe rule that AY's own strict checker validates
    /// (`validate_cong`) and that Carcara checks natively — closed by one
    /// resolution against the assumed disequality:
    ///
    /// ```text
    /// (assume h0 (= a b))
    /// (assume h1 (not (= (f .. a ..) (f .. b ..))))
    /// (step  c  (cl (= (f .. a ..) (f .. b ..))) :rule cong :premises (h0))
    /// (step  r  (cl) :rule resolution :premises (c h1))
    /// ```
    ///
    /// FAIL-CLOSED CONDITIONS (any one keeps the honest `trust` step):
    ///  - the assertion set is not exactly one disequality plus one or more
    ///    equalities (an unused original could be the one that mattered, and
    ///    the rebuilt proof must not claim a refutation it did not use);
    ///  - the two disequality sides are not applications of the SAME symbol
    ///    with the same arity;
    ///  - some differing argument position has no equality original for
    ///    exactly that unordered pair, or some equality original is left
    ///    over (`cong` requires every premise to be consumed);
    ///  - re-interning any reconstructed term does not reproduce it RAW (a
    ///    folding interner would make the derivation not match the premise).
    ///
    /// This is congruence over the ORIGINAL assertions only. It never appeals
    /// to array extensionality, so `(= a b)` between arrays is used exactly
    /// as the congruence premise for a shared argument position — the same
    /// obligation Carcara's `cong` checks.
    fn rebuild_congruence_collapse(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        if originals.len() < 2 {
            return false;
        }
        // Partition the originals: exactly one disequality conclusion, every
        // other one an equality that must end up used as a `cong` premise.
        let mut disequality: Option<(TermId, TermId)> = None;
        let mut equalities: Vec<(TermId, TermId)> = Vec::with_capacity(originals.len());
        for (_, parsed) in originals {
            let stripped = strip_frontend_annotations(parsed);
            let FrontendTerm::App(head, operands) = stripped else {
                return false;
            };
            let (is_disequality, sides) = match (head.as_str(), operands.len()) {
                ("=", 2) => (false, &operands[..]),
                ("distinct", 2) => (true, &operands[..]),
                ("not", 1) => match strip_frontend_annotations(&operands[0]) {
                    FrontendTerm::App(inner_head, inner_operands)
                        if inner_head == "=" && inner_operands.len() == 2 =>
                    {
                        (true, &inner_operands[..])
                    }
                    _ => return false,
                },
                _ => return false,
            };
            let (Some(lhs), Some(rhs)) = (
                self.ctx.elaborate_surface_subterm(&sides[0]),
                self.ctx.elaborate_surface_subterm(&sides[1]),
            ) else {
                return false;
            };
            if self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs) {
                return false;
            }
            if is_disequality {
                if disequality.is_some() {
                    return false;
                }
                disequality = Some((lhs, rhs));
            } else {
                equalities.push((lhs, rhs));
            }
        }
        let (Some((conc_lhs, conc_rhs)), false) = (disequality, equalities.is_empty()) else {
            return false;
        };

        // The two sides must be the same application, differing only at
        // positions an original equality covers — and every equality must be
        // consumed, which is exactly what `validate_cong` re-checks.
        let (TermData::App(lhs_sym, lhs_args), TermData::App(rhs_sym, rhs_args)) = (
            self.ctx.terms.get(conc_lhs).clone(),
            self.ctx.terms.get(conc_rhs).clone(),
        ) else {
            return false;
        };
        if lhs_sym != rhs_sym || lhs_args.len() != rhs_args.len() {
            return false;
        }
        let mut used = vec![false; equalities.len()];
        for (left, right) in lhs_args.iter().zip(rhs_args.iter()) {
            if left == right {
                continue;
            }
            let Some(position) = equalities.iter().enumerate().position(|(k, &(a, b))| {
                !used[k] && ((a == *left && b == *right) || (a == *right && b == *left))
            }) else {
                return false;
            };
            used[position] = true;
        }
        if used.iter().any(|consumed| !consumed) {
            return false;
        }

        // Re-intern every premise RAW; a folding interner would leave the
        // derivation referring to terms the printed premises do not carry.
        let mut premises: Vec<TermId> = Vec::with_capacity(equalities.len());
        for &(lhs, rhs) in &equalities {
            let eq = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
            if !matches!(
                self.ctx.terms.get(eq),
                TermData::App(Symbol::Named(op), a)
                    if op == "=" && a.len() == 2 && a[0] == lhs && a[1] == rhs
            ) {
                return false;
            }
            premises.push(eq);
        }
        let conclusion =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [conc_lhs, conc_rhs], Sort::Bool);
        if !matches!(
            self.ctx.terms.get(conclusion),
            TermData::App(Symbol::Named(op), a)
                if op == "=" && a.len() == 2 && a[0] == conc_lhs && a[1] == conc_rhs
        ) {
            return false;
        }
        let negated = self.ctx.terms.mk_not_raw(conclusion);
        if negated == conclusion {
            return false;
        }

        let mut new_proof = Proof::new();
        let mut premise_ids: Vec<ProofId> = Vec::with_capacity(premises.len());
        for &eq in &premises {
            premise_ids.push(new_proof.add_assume(eq, None));
        }
        let negated_id = new_proof.add_assume(negated, None);
        let cong =
            new_proof.add_rule_step(AletheRule::Cong, vec![conclusion], premise_ids, Vec::new());
        new_proof.add_resolution(Vec::new(), conclusion, cong, negated_id);
        *proof = new_proof;
        for &eq in &premises {
            self.record_rebuilt_authored_proof_premise(eq);
        }
        self.record_rebuilt_authored_proof_premise(negated);
        true
    }

    /// Consumed-assertions collapse (`x = 1 ∧ y = 2 ∧ x + y = 4`): the
    /// preprocessor substituted the assertions into each other, folded the
    /// contradiction, and the exported proof is the bare `(cl false) :rule
    /// trust` — no assume, no derivation. Re-prove from the ORIGINAL
    /// arithmetic-equality assertions: a single `la_generic` lemma over
    /// their negations, coefficients SYNTHESIZED by the LRA solver and
    /// independently re-verified (rational check + printable sign
    /// orientation, both fail-closed), closed by one resolution per assumed
    /// equality. Any non-equality original or failed certificate keeps the
    /// honest trust step.
    /// Last-resort Shape-C repair: BIND THE PREMISES even when the refutation
    /// itself cannot be certified (#dt-premise-binding).
    ///
    /// Shape C is "the preprocessor consumed the assertions entirely", leaving
    /// the bare `(cl false)` with NO assume and NO derivation. The two rebuilds
    /// above re-prove such a collapse for arithmetic and congruence. A DATATYPE
    /// collapse has no such rebuild and cannot get one: Alethe defines no
    /// datatype rules, carcara implements none (181 rules, zero datatype), and
    /// cvc5 itself refuses to emit Alethe for datatypes. So the refutation step
    /// stays an unproved `hole`.
    ///
    /// But an unproved step is not the worst property of the exported artefact.
    /// A bare `(cl false) :rule hole` mentions NOTHING from the problem, so it
    /// checks IDENTICALLY AGAINST ANY INPUT FILE — it is not a weak proof of
    /// this instance, it is not a proof of anything. This repair fixes exactly
    /// that, without inventing a rule:
    ///
    /// ```text
    /// (assume a0 A0) ... (assume aN AN)          <- must match problem premises
    /// (step  t0 (cl (not A0) ... (not AN)) :rule hole)
    /// (step  t1 (cl) :rule th_resolution ...)    <- CHECKED
    /// ```
    ///
    /// A checker now verifies (a) every assume is a premise OF THIS PROBLEM,
    /// and (b) the contradiction genuinely follows from the hole's clause plus
    /// those premises. The hole also states its own content — "this premise set
    /// is jointly unsatisfiable" — instead of "false, trust me", so the trusted
    /// surface is one explicit clause a human can audit and a future rule can
    /// discharge.
    ///
    /// SOUNDNESS: the emitted clause is the negation of the conjunction of the
    /// problem's own assertions, which is exactly the claim "these are jointly
    /// unsat" — the claim the solver already made by answering `unsat`. No new
    /// assertion is introduced and no gate is relaxed; `terminal_trust.rs`
    /// counts the `hole` exactly as it counted the `trust`, so nothing that
    /// rejected the old proof accepts this one. Fail-closed: any original that
    /// does not elaborate to a Bool-sorted term leaves the proof unchanged.
    fn rebuild_premise_binding_collapse(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        if originals.is_empty() {
            return false;
        }
        // Elaborate every original assertion. Totality is required: binding a
        // SUBSET would claim a smaller premise set refutes the instance, which
        // the solver has not established.
        let mut premises: Vec<TermId> = Vec::with_capacity(originals.len());
        for (_, parsed) in originals {
            let stripped = strip_frontend_annotations(parsed);
            let Some(t) = self.ctx.elaborate_surface_subterm(stripped) else {
                return false;
            };
            if !matches!(self.ctx.terms.sort(t), Sort::Bool) {
                return false;
            }
            premises.push(t);
        }
        // Full (not just adjacent) dedup. `Vec::dedup` drops only CONSECUTIVE
        // repeats, so a file that asserts the same formula twice non-adjacently
        // used to bind it twice — harmless for the claim (the conjunction is
        // unchanged, so totality still holds) but it makes the closing
        // resolution ambiguous: the second copy of `A` has no `(not A)` left to
        // resolve against. Keep the first occurrence, in assertion order.
        let mut seen: HashSet<TermId> = HashSet::default();
        premises.retain(|&p| seen.insert(p));
        if premises.is_empty() {
            return false;
        }

        let clause: Vec<TermId> = premises
            .iter()
            .map(|&p| self.ctx.terms.mk_not_raw(p))
            .collect();

        let mut new_proof = Proof::new();
        let assume_ids: Vec<ProofId> = premises
            .iter()
            .map(|&p| new_proof.add_assume(p, None))
            .collect();
        // Unproved by construction — prints as `hole`, the honest encoding for
        // a step no checker can discharge. NOT a certified lemma.
        let lemma = new_proof.add_step(ProofStep::TheoryLemma {
            theory: "DT".to_string(),
            clause: clause.clone(),
            farkas: None,
            kind: TheoryLemmaKind::Generic,
            lia: None,
        });
        // ONE n-ary resolution, not a binary chain (#dt-premise-binding).
        //
        // This closed as `for i in 0..n { resolve(clause[i+1..], premises[i]) }`
        // — n binary steps, step i printing the n-i literals it has left. That
        // is TRIANGULAR text. Measured on the file that motivated the rebuild,
        // QF_DT/20210312-Bouvier/vlsat3_b14.smt2 (n = 2,986): 105.6 MB of
        // `.alethe`, 105.5 MB of it resolution steps whose lines decayed
        // 75,252 → 61,678 → 36,896 → … → 83 chars. The by-default sibling
        // emission is budgeted at 64 MiB of work (`executor/proof.rs`), so that
        // document was not a big proof — it was NO PROOF: emission aborted with
        // "work budget exhausted after 3502 steps" and the file was never
        // written.
        //
        // Alethe `resolution`/`th_resolution` are n-ary, so the whole chain is
        // one step whose premises are the lemma followed by every assume. Same
        // claim, same premises, same `hole`: 193,103 bytes (547x smaller),
        // inside the default budget, carcara 1.1.0 verdict `holey` in 0.01 s —
        // `holey` being the best achievable here, as Alethe defines no
        // datatype rules.
        // The order (lemma first, then assumes in assertion order) is the order
        // the checker folds in: the accumulator starts as the hole's clause
        // `[(not A0) … (not An)]` and each assume `Ai` cancels its own literal,
        // ending empty.
        let mut chain: Vec<ProofId> = Vec::with_capacity(assume_ids.len() + 1);
        chain.push(lemma);
        chain.extend_from_slice(&assume_ids);
        // Alethe requires >= 2 premises on a resolution (carcara: "expected at
        // least 2 premises, got 1"). Lemma + >= 1 assume always satisfies it,
        // but check rather than assume: a one-premise step would be rejected
        // outright, i.e. no proof, which is worse than keeping the trust stub.
        if chain.len() < 2 {
            return false;
        }
        new_proof.add_rule_step(AletheRule::ThResolution, Vec::new(), chain, Vec::new());
        *proof = new_proof;
        true
    }

    fn rebuild_consumed_equalities_collapse(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        // Every original must be a re-internable arithmetic equality (the
        // lemma's premises must cover the WHOLE assertion set: a dropped
        // non-equality premise could be the one that mattered — though any
        // certified subset would still be sound, requiring totality keeps
        // the rebuilt proof honest about what refuted the instance).
        let mut eqs: Vec<TermId> = Vec::with_capacity(originals.len());
        for (_, parsed) in originals {
            let stripped = strip_frontend_annotations(parsed);
            let FrontendTerm::App(head, operands) = stripped else {
                return false;
            };
            if head != "=" || operands.len() != 2 {
                return false;
            }
            let (Some(lhs), Some(rhs)) = (
                self.ctx.elaborate_surface_subterm(&operands[0]),
                self.ctx.elaborate_surface_subterm(&operands[1]),
            ) else {
                return false;
            };
            if !matches!(self.ctx.terms.sort(lhs), Sort::Int | Sort::Real)
                || self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs)
            {
                return false;
            }
            let eq = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
            if !matches!(
                self.ctx.terms.get(eq),
                TermData::App(Symbol::Named(op), a) if op == "=" && a.len() == 2 && a[0] == lhs && a[1] == rhs
            ) {
                return false;
            }
            // External `la_generic` evaluates the combination syntactically:
            // impure atoms (UF/array applications) are out of scope.
            if !equality_is_pure_linear_arith(&self.ctx.terms, eq) {
                return false;
            }
            if !eqs.contains(&eq) {
                eqs.push(eq);
            }
        }
        if eqs.len() < 2 {
            return false;
        }
        let clause: Vec<TermId> = eqs.iter().map(|&e| self.ctx.terms.mk_not_raw(e)).collect();
        // Synthesize the certificate, then independently re-verify it and
        // require a printable equality-sign orientation (fail-closed).
        let mut farkas: Option<FarkasAnnotation> = None;
        let mut kind = TheoryLemmaKind::Generic;
        if !super::proof_farkas::try_lra_farkas_reconstruction(
            &self.ctx.terms,
            &clause,
            &mut farkas,
            &mut kind,
        ) {
            return false;
        }
        let Some(farkas) = farkas else {
            return false;
        };
        let conflict: Vec<TheoryLit> = eqs.iter().map(|&e| TheoryLit::new(e, true)).collect();
        if ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_err()
        {
            return false;
        }
        if ay_core::proof_validation::resolve_equality_coefficient_signs(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_none()
        {
            return false;
        }
        let mut new_proof = Proof::new();
        let assume_ids: Vec<ProofId> = eqs.iter().map(|&e| new_proof.add_assume(e, None)).collect();
        // Rationally certified: `la_generic`, fully checked externally.
        let lemma = new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: clause.clone(),
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        let mut current = lemma;
        for (i, (&eq, &aid)) in eqs.iter().zip(assume_ids.iter()).enumerate() {
            let remaining: Vec<TermId> = clause[i + 1..].to_vec();
            current = new_proof.add_resolution(remaining, eq, current, aid);
        }
        *proof = new_proof;
        true
    }

    /// Whether `(cl (not a1) .. (not an) concl)` is a valid all-ones
    /// `la_generic` lemma per the independent LINEAR Farkas checker (the
    /// antecedent literals asserted true, the conclusion asserted false).
    /// `_linear`, not `_full`: the lemma exports as `la_generic` and
    /// external checkers perform no congruence reasoning inside it.
    fn quant_lemma_valid(&self, antecedents: &[TermId], conclusion: TermId) -> bool {
        let mut lits: Vec<TheoryLit> = antecedents
            .iter()
            .map(|&l| match self.ctx.terms.get(l) {
                TermData::Not(inner) => TheoryLit::new(*inner, false),
                _ => TheoryLit::new(l, true),
            })
            .collect();
        lits.push(match self.ctx.terms.get(conclusion) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(conclusion, false),
        });
        #[allow(clippy::cast_possible_truncation)]
        let coeffs = vec![1i64; lits.len()];
        ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &lits,
            &FarkasAnnotation::from_ints(&coeffs),
        )
        .is_ok()
    }

    /// Whether the asserted arithmetic literals are jointly infeasible under
    /// an all-ones Farkas combination.  This is the no-conclusion sibling of
    /// [`Self::quant_lemma_valid`], used when an E-matching instance and an
    /// authored equality directly contradict one another.
    fn quant_conflict_valid(&self, antecedents: &[TermId]) -> bool {
        if antecedents.is_empty() {
            return false;
        }
        let lits: Vec<TheoryLit> = antecedents
            .iter()
            .map(|&literal| match self.ctx.terms.get(literal) {
                TermData::Not(inner) => TheoryLit::new(*inner, false),
                _ => TheoryLit::new(literal, true),
            })
            .collect();
        #[allow(clippy::cast_possible_truncation)]
        let coeffs = vec![1i64; lits.len()];
        ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &lits,
            &FarkasAnnotation::from_ints(&coeffs),
        )
        .is_ok()
    }

    /// Whether the unit clause `(cl atom)` is a ground arithmetic tautology
    /// per the independent Farkas checker (its negation is infeasible on its
    /// own — e.g. the instantiated guard bound `(<= 0 24)`).
    fn ground_arith_unit_valid(&self, atom: TermId) -> bool {
        let lit = match self.ctx.terms.get(atom) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(atom, false),
        };
        ay_core::proof_validation::verify_farkas_conflict_lits_full(
            &self.ctx.terms,
            &[lit],
            &FarkasAnnotation::from_ints(&[1]),
        )
        .is_ok()
    }

    /// Emit a `[1]` `la_generic` unit lemma `(cl atom)`. Only called for
    /// atoms already validated by [`Self::ground_arith_unit_valid`].
    fn add_unit_lemma(new_proof: &mut Proof, atom: TermId) -> ProofId {
        new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![atom],
            farkas: Some(FarkasAnnotation::from_ints(&[1])),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Build the certified derivation chain from the parsed `forall` premise
    /// to the unit `(cl target)` at binder values `values`
    /// (#quant-expansion-proof). Every ingredient is validated here, at plan
    /// time; emission ([`Self::emit_quant_instance_chain`]) is mechanical.
    /// Fail-closed `None` on: binder/value arity or sort mismatch, a body
    /// with any nested binding construct, a guard that is not a conjunction
    /// of distinct positive ground arithmetic truths, or a consequent that
    /// neither equals `target` nor bridges to it by a re-verified `[1, 1]`
    /// `la_generic` lemma.
    fn build_quant_instance_chain(
        &mut self,
        parsed_forall: &FrontendTerm,
        values: &[TermId],
        target: TermId,
    ) -> Option<QuantInstanceChain> {
        if !surface_source_is_bounded(parsed_forall) {
            return None;
        }
        let stripped = strip_frontend_annotations(parsed_forall);
        let FrontendTerm::Forall(binders, body) = stripped else {
            return None;
        };
        if binders.len() != values.len() {
            return None;
        }
        let mut subst: HashMap<String, FrontendTerm> = HashMap::default();
        for ((name, _), &value) in binders.iter().zip(values.iter()) {
            subst.insert(name.clone(), value_to_surface(&self.ctx.terms, value)?);
        }
        let substituted = surface_subst_ground(body.as_ref(), &subst)?;
        let phi = self.raw_intern_surface(&substituted)?;
        let (guard, body_lit) = match &substituted {
            FrontendTerm::App(op, operands) if op == "=>" && operands.len() == 2 => {
                let guard_term = self.raw_intern_surface(&operands[0])?;
                let body_lit = self.raw_intern_surface(&operands[1])?;
                let atoms: Vec<TermId> = match strip_frontend_annotations(&operands[0]) {
                    FrontendTerm::App(gop, gargs) if gop == "and" && !gargs.is_empty() => gargs
                        .iter()
                        .map(|g| self.raw_intern_surface(g))
                        .collect::<Option<Vec<_>>>()?,
                    _ => vec![guard_term],
                };
                // Distinct positive atoms keep the and_neg resolution chain
                // unambiguous (a duplicated pivot would remove the wrong
                // number of literals; a negated conjunct would double-negate
                // in the and_neg clause).
                let mut seen = atoms.clone();
                seen.sort_unstable();
                seen.dedup();
                if seen.len() != atoms.len()
                    || atoms
                        .iter()
                        .any(|&a| matches!(self.ctx.terms.get(a), TermData::Not(_)))
                {
                    return None;
                }
                for &atom in &atoms {
                    if !self.ground_arith_unit_valid(atom) {
                        return None;
                    }
                }
                (Some((guard_term, atoms)), body_lit)
            }
            _ => (None, phi),
        };
        if body_lit != target {
            let body_complement = complement_of(&mut self.ctx.terms, body_lit);
            if !self.pair_lemma_valid(target, body_complement) {
                return None;
            }
        }
        Some(QuantInstanceChain {
            values: values.to_vec(),
            phi,
            guard,
            body_lit,
            target,
        })
    }

    /// Build an exact, unguarded direct-forall instance chain from either a
    /// parsed SMT-LIB forall or the native API's surface-placeholder.  The API
    /// path independently recomputes simultaneous substitution on the
    /// canonical authored term; it accepts only byte-identical ground bodies.
    fn build_direct_ematching_instance_chain(
        &mut self,
        forall_term: TermId,
        parsed: &FrontendTerm,
        values: &[TermId],
        instance: TermId,
    ) -> Option<QuantInstanceChain> {
        if !surface_source_is_bounded(parsed) {
            return None;
        }
        if matches!(
            strip_frontend_annotations(parsed),
            FrontendTerm::Symbol(name) if name == super::NATIVE_API_ASSERTION_PLACEHOLDER
        ) {
            let (body, substitution) = {
                let TermData::Forall(bindings, body, _) = self.ctx.terms.get(forall_term) else {
                    return None;
                };
                if bindings.is_empty()
                    || bindings.len() != values.len()
                    || bindings.len() > MAX_PROVENANCE_REPAIR_TERMS
                {
                    return None;
                }
                let binder_bytes = bindings
                    .iter()
                    .try_fold(0usize, |bytes, (name, _)| bytes.checked_add(name.len()))?;
                if binder_bytes > 64 * 1024
                    || quant_canonical_term_work(&self.ctx.terms, *body).is_none()
                {
                    return None;
                }
                let mut substitution = HashMap::default();
                for ((name, sort), &value) in bindings.iter().zip(values) {
                    if self.ctx.terms.sort(value) != sort {
                        return None;
                    }
                    substitution.insert(name.clone(), value);
                }
                (*body, substitution)
            };
            let phi = crate::ematching::subst_vars(&mut self.ctx.terms, body, &substitution);
            if phi != instance {
                return None;
            }
            return Some(QuantInstanceChain {
                values: values.to_vec(),
                phi,
                guard: None,
                body_lit: phi,
                target: phi,
            });
        }

        let chain = self.build_quant_instance_chain(parsed, values, instance)?;
        // The negative-forall proof consumes the RAW surface instance
        // (`chain.phi`) directly in an arithmetic conflict. A comparison may
        // have a different canonical orientation than `instance`; the builder
        // above independently validated that bridge. Guard discharge, however,
        // would require the forall as a premise and would be circular here.
        chain.guard.is_none().then_some(chain)
    }

    /// Rebuild the exact authored surface forall around a raw ground instance.
    /// The returned quantifier is alpha-fresh but structurally faithful to the
    /// parsed source, so both AY's exact-substitution checker and an external
    /// Alethe checker see the same `forall_inst` body.
    fn build_raw_ematching_forall_source(
        &mut self,
        canonical_forall: TermId,
        parsed: &FrontendTerm,
        values: &[TermId],
        ground_instance: TermId,
    ) -> Option<TermId> {
        if !surface_source_is_bounded(parsed) {
            return None;
        }
        if matches!(
            strip_frontend_annotations(parsed),
            FrontendTerm::Symbol(name) if name == super::NATIVE_API_ASSERTION_PLACEHOLDER
        ) {
            return Some(canonical_forall);
        }

        let FrontendTerm::Forall(parsed_bindings, parsed_body) = strip_frontend_annotations(parsed)
        else {
            return None;
        };
        let TermData::Forall(canonical_bindings, _, _) =
            self.ctx.terms.get(canonical_forall).clone()
        else {
            return None;
        };
        if parsed_bindings.is_empty()
            || parsed_bindings.len() != canonical_bindings.len()
            || parsed_bindings.len() != values.len()
        {
            return None;
        }

        let mut ground_substitution: HashMap<String, FrontendTerm> = HashMap::default();
        let mut bound_vars: HashMap<String, TermId> = HashMap::default();
        let mut raw_bindings = Vec::with_capacity(parsed_bindings.len());
        for (((parsed_name, _), (_, canonical_sort)), &value) in parsed_bindings
            .iter()
            .zip(canonical_bindings.iter())
            .zip(values)
        {
            if bound_vars.contains_key(parsed_name) || self.ctx.terms.sort(value) != canonical_sort
            {
                return None;
            }
            ground_substitution.insert(
                parsed_name.clone(),
                value_to_surface(&self.ctx.terms, value)?,
            );
            let variable = self
                .ctx
                .terms
                .mk_var(parsed_name.clone(), canonical_sort.clone());
            bound_vars.insert(parsed_name.clone(), variable);
            raw_bindings.push((parsed_name.clone(), canonical_sort.clone()));
        }

        let substituted = surface_subst_ground(parsed_body.as_ref(), &ground_substitution)?;
        let rebuilt_ground = self.raw_intern_surface(&substituted)?;
        if rebuilt_ground != ground_instance {
            return None;
        }
        let raw_body = lift_surface_binders_from_ground(
            &mut self.ctx.terms,
            parsed_body.as_ref(),
            &substituted,
            ground_instance,
            &bound_vars,
        )?;
        if self.ctx.terms.sort(raw_body) != &Sort::Bool {
            return None;
        }
        let raw_forall = self.ctx.terms.mk_forall(raw_bindings, raw_body);

        let exact_substitution: HashMap<String, TermId> = parsed_bindings
            .iter()
            .map(|(name, _)| name.clone())
            .zip(values.iter().copied())
            .collect();
        if !raw_instance_matches_substitution(
            &self.ctx.terms,
            raw_body,
            ground_instance,
            &exact_substitution,
        ) {
            return None;
        }
        Some(raw_forall)
    }

    /// Emit a plan-time-validated negative-forall derivation.  The forall is
    /// used only by the premiseless `forall_inst` rule; support assumptions
    /// close the checked arithmetic conflict to `(not instance)`, which then
    /// resolves the instantiation clause to `(not forall)`.
    fn emit_ematching_quant_negation(
        &mut self,
        new_proof: &mut Proof,
        plan: &QuantNegationPlan,
        lift_assume: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let not_forall = self.ctx.terms.mk_not_raw(plan.forall_term);
        let inst_or = self.ctx.terms.mk_app(
            Symbol::named("or"),
            [not_forall, plan.chain.phi],
            Sort::Bool,
        );
        let forall_inst = new_proof.add_rule_step(
            AletheRule::ForallInst,
            vec![inst_or],
            Vec::new(),
            plan.chain.values.clone(),
        );
        let inst_clause = new_proof.add_rule_step(
            AletheRule::Or,
            vec![not_forall, plan.chain.phi],
            vec![forall_inst],
            Vec::new(),
        );

        #[allow(clippy::cast_possible_truncation)]
        let coeffs = vec![1i64; plan.lemma.len()];
        let mut conflict = new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: plan.lemma.clone(),
            farkas: Some(FarkasAnnotation::from_ints(&coeffs)),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        let mut remaining = plan.lemma.clone();
        for &support in &plan.supports {
            let support_id = *lift_assume.get(&support)?;
            let complement = complement_of(&mut self.ctx.terms, support);
            let position = remaining.iter().position(|&term| term == complement)?;
            let _ = remaining.remove(position);
            conflict = new_proof.add_resolution(
                remaining.clone(),
                atom_of(&self.ctx.terms, support),
                conflict,
                support_id,
            );
        }
        if remaining.len() != 1
            || remaining[0] != complement_of(&mut self.ctx.terms, plan.chain.phi)
        {
            return None;
        }
        Some(new_proof.add_resolution(
            vec![not_forall],
            atom_of(&self.ctx.terms, plan.chain.phi),
            inst_clause,
            conflict,
        ))
    }

    /// Emit the plan-time-validated instance derivation
    /// (#quant-expansion-proof): `forall_inst` (positional binder-value
    /// args) + `or` + resolution against the forall's assume yields the raw
    /// substituted body; `implies_pos` + per-atom `[1]` `la_generic` guard
    /// units + `and_neg` discharge the instantiated guard; the optional
    /// re-verified `[1, 1]` bridge lands on the canonical target unit.
    fn emit_quant_instance_chain(
        &mut self,
        new_proof: &mut Proof,
        forall_term: TermId,
        assume_id: ProofId,
        chain: &QuantInstanceChain,
    ) -> ProofId {
        let not_forall = self.ctx.terms.mk_not_raw(forall_term);
        let inst_or =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), [not_forall, chain.phi], Sort::Bool);
        let fi = new_proof.add_rule_step(
            AletheRule::ForallInst,
            vec![inst_or],
            Vec::new(),
            chain.values.clone(),
        );
        let or_step = new_proof.add_rule_step(
            AletheRule::Or,
            vec![not_forall, chain.phi],
            vec![fi],
            Vec::new(),
        );
        let phi_unit = new_proof.add_resolution(vec![chain.phi], forall_term, or_step, assume_id);
        let body_unit = match &chain.guard {
            None => phi_unit,
            Some((guard_term, atoms)) => {
                let (guard_term, atoms) = (*guard_term, atoms.clone());
                let not_phi = self.ctx.terms.mk_not_raw(chain.phi);
                let not_guard = self.ctx.terms.mk_not_raw(guard_term);
                let ip = new_proof.add_rule_step(
                    AletheRule::ImpliesPos,
                    vec![not_phi, not_guard, chain.body_lit],
                    Vec::new(),
                    Vec::new(),
                );
                let guard_unit = if atoms.len() == 1 && atoms[0] == guard_term {
                    Self::add_unit_lemma(new_proof, guard_term)
                } else {
                    let not_atoms: Vec<TermId> = atoms
                        .iter()
                        .map(|&a| self.ctx.terms.mk_not_raw(a))
                        .collect();
                    let mut working = vec![guard_term];
                    working.extend(not_atoms.iter().copied());
                    let mut cur = new_proof.add_rule_step(
                        AletheRule::AndNeg,
                        working.clone(),
                        Vec::new(),
                        Vec::new(),
                    );
                    for (&atom, &not_atom) in atoms.iter().zip(not_atoms.iter()) {
                        let unit = Self::add_unit_lemma(new_proof, atom);
                        if let Some(p) = working.iter().position(|&l| l == not_atom) {
                            let _ = working.remove(p);
                        }
                        cur = new_proof.add_resolution(working.clone(), atom, cur, unit);
                    }
                    cur
                };
                let r1 = new_proof.add_resolution(
                    vec![not_guard, chain.body_lit],
                    chain.phi,
                    ip,
                    phi_unit,
                );
                new_proof.add_resolution(vec![chain.body_lit], guard_term, r1, guard_unit)
            }
        };
        if chain.target == chain.body_lit {
            body_unit
        } else {
            let body_pivot = atom_of(&self.ctx.terms, chain.body_lit);
            let body_complement = complement_of(&mut self.ctx.terms, chain.body_lit);
            let lemma = Self::add_pair_lemma(new_proof, chain.target, body_complement);
            new_proof.add_resolution(vec![chain.target], body_pivot, lemma, body_unit)
        }
    }
}
