// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// #no-mbqi-rewrite-transfer: the "E-matching only" mark must survive body
/// normalization. `fold_linear_eqs` rebuilds a quantifier whose body it
/// normalized (`(not (<= i j))` -> `(< j i)`), and the rebuilt `TermId` used
/// to shed the mark — CEGQI then instantiated the deductive-checks Hilbert-choose
/// combined axiom `∀i j. (i<=j) => (c0<=c1)` at a fabricated witness and
/// published UNSAT, making the choose.rs `fails1` ports prove more than
/// Verus. The marked axiom must fail closed to Unknown instead.
#[test]
fn no_mbqi_survives_linear_body_normalization() {
    let mut executor = Executor::new();
    executor.ctx.set_logic("ALL".to_string());
    let int = Sort::Int;
    let c0 = executor.ctx.terms.mk_var("c0", int.clone());
    let c1 = executor.ctx.terms.mk_var("c1", int.clone());
    let i = executor.ctx.terms.mk_var("i", int.clone());
    let j = executor.ctx.terms.mk_var("j", int.clone());
    let ante = executor.ctx.terms.mk_le(i, j);
    let concl = executor.ctx.terms.mk_le(c0, c1);
    let not_ante = executor.ctx.terms.mk_not(ante);
    let body = executor.ctx.terms.mk_or(vec![not_ante, concl]);
    let forall = executor.ctx.terms.mk_forall(
        vec![
            ("i".to_string(), int.clone()),
            ("j".to_string(), int.clone()),
        ],
        body,
    );
    executor.ctx.terms.mark_no_mbqi(forall);
    executor.ctx.assertions.push(forall);
    let lt = executor.ctx.terms.mk_lt(c1, c0);
    executor.ctx.assertions.push(lt);

    let result = executor.check_sat();

    assert!(
        matches!(result, Ok(SolveResult::Unknown)),
        "a no_mbqi axiom must not be synthesis-instantiated after body \
         normalization rebuilds its TermId: {result:?}"
    );
}

/// The capability dual: the same query without the mark is legitimately
/// decided UNSAT, so copying quantifier metadata restricts only the marked
/// discipline and leaves the CEGQI-instantiable universal decidable.
#[test]
fn unmarked_linear_normalized_forall_still_decides() {
    let mut executor = Executor::new();
    executor.ctx.set_logic("ALL".to_string());
    let int = Sort::Int;
    let c0 = executor.ctx.terms.mk_var("c0", int.clone());
    let c1 = executor.ctx.terms.mk_var("c1", int.clone());
    let i = executor.ctx.terms.mk_var("i", int.clone());
    let j = executor.ctx.terms.mk_var("j", int.clone());
    let ante = executor.ctx.terms.mk_le(i, j);
    let concl = executor.ctx.terms.mk_le(c0, c1);
    let not_ante = executor.ctx.terms.mk_not(ante);
    let body = executor.ctx.terms.mk_or(vec![not_ante, concl]);
    let forall = executor.ctx.terms.mk_forall(
        vec![
            ("i".to_string(), int.clone()),
            ("j".to_string(), int.clone()),
        ],
        body,
    );
    executor.ctx.assertions.push(forall);
    let lt = executor.ctx.terms.mk_lt(c1, c0);
    executor.ctx.assertions.push(lt);

    let result = executor.check_sat();

    assert!(
        matches!(result, Ok(SolveResult::Unsat(_))),
        "the unmarked universal stays decidable: {result:?}"
    );
}

/// A rewrite can hash-cons onto an equivalent quantifier that came from a
/// separately marked origin. Copying metadata from the unmarked source must
/// not clear that target's conservative E-matching-only restriction; ordinary
/// quantifier metadata still mirrors the source exactly.
#[test]
fn metadata_copy_preserves_no_mbqi_on_an_interned_target() {
    let mut terms = ay_core::TermStore::new();
    let int = Sort::Int;
    let i = terms.mk_var("metadata_collision_i", int.clone());
    let j = terms.mk_var("metadata_collision_j", int.clone());
    let conclusion = terms.mk_var("metadata_collision_conclusion", Sort::Bool);

    let normalized_antecedent = terms.mk_lt(j, i);
    let normalized_body = terms.mk_or(vec![normalized_antecedent, conclusion]);
    let binders = vec![("i".to_string(), int.clone()), ("j".to_string(), int)];
    let marked_target = terms.mk_forall(binders.clone(), normalized_body);
    terms.mark_no_mbqi(marked_target);
    terms.set_quantifier_id(marked_target, "stale-target-qid".to_string());

    let source_antecedent = terms.mk_le(i, j);
    let negated_source_antecedent = terms.mk_not(source_antecedent);
    let source_body = terms.mk_or(vec![negated_source_antecedent, conclusion]);
    let unmarked_source = terms.mk_forall(binders.clone(), source_body);
    terms.set_quantifier_id(unmarked_source, "source-qid".to_string());
    terms.set_skolem_id(unmarked_source, "source-skid".to_string());
    terms.set_quantifier_weight(unmarked_source, 17);
    terms.set_quantifier_no_patterns(unmarked_source, vec![source_antecedent]);

    assert_ne!(unmarked_source, marked_target);
    assert!(!terms.is_no_mbqi(unmarked_source));
    let interned_rebuild = terms.mk_forall(binders, normalized_body);
    assert_eq!(interned_rebuild, marked_target);

    terms.copy_quantifier_metadata(unmarked_source, interned_rebuild);

    assert!(terms.is_no_mbqi(marked_target));
    assert_eq!(terms.quantifier_id(marked_target), Some("source-qid"));
    assert_eq!(terms.skolem_id(marked_target), Some("source-skid"));
    assert_eq!(terms.explicit_quantifier_weight(marked_target), Some(17));
    assert_eq!(
        terms.quantifier_no_patterns(marked_target),
        &[source_antecedent]
    );
}

/// #no-mbqi-authored-diagonal: shape is not provenance. The e-matching gate
/// for `no_mbqi` quantifiers used to refuse every DIAGONAL ground candidate
/// (`P(c,c)`) alongside the synthesis watermark, to keep
/// `add_diagonal_forall_instances`' manufactured terms from discharging a
/// Hilbert-`choose` axiom. But the watermark alone already excludes every
/// solver-invented app (it is set before all synthesis passes), while the
/// blanket shape test refused genuine AUTHORED diagonal witnesses — the
/// deductive-checks choose.rs `test_refine2_tuple` port asserts `cnatf2(10, 10)` and
/// then chooses over `cnatf2`, and its combined axiom could never fire. An
/// authored diagonal witness must discharge the marked axiom.
#[test]
fn no_mbqi_matches_authored_diagonal_witness() {
    let mut executor = Executor::new();
    executor.ctx.set_logic("ALL".to_string());
    let int = Sort::Int;
    let c0 = executor.ctx.terms.mk_var("c0", int.clone());
    let c1 = executor.ctx.terms.mk_var("c1", int.clone());
    let m = executor.ctx.terms.mk_var("m", int.clone());
    let n = executor.ctx.terms.mk_var("n", int.clone());
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let ten = executor.ctx.terms.mk_int(BigInt::from(10));
    let f_mn = executor
        .ctx
        .terms
        .mk_app(Symbol::named("cnatf2"), vec![m, n], Sort::Bool);
    let f_c = executor
        .ctx
        .terms
        .mk_app(Symbol::named("cnatf2"), vec![c0, c1], Sort::Bool);
    let f_1010 = executor
        .ctx
        .terms
        .mk_app(Symbol::named("cnatf2"), vec![ten, ten], Sort::Bool);
    let def = executor.ctx.terms.mk_forall(
        vec![
            ("m".to_string(), int.clone()),
            ("n".to_string(), int.clone()),
        ],
        f_mn,
    );
    let le10m = executor.ctx.terms.mk_le(ten, m);
    let le10n = executor.ctx.terms.mk_le(ten, n);
    let le0m = executor.ctx.terms.mk_le(zero, m);
    let le0n = executor.ctx.terms.mk_le(zero, n);
    let le10c0 = executor.ctx.terms.mk_le(ten, c0);
    let le10c1 = executor.ctx.terms.mk_le(ten, c1);
    let conj = executor.ctx.terms.mk_and(vec![f_c, le10c0, le10c1]);
    let nf = executor.ctx.terms.mk_not(f_mn);
    let n10m = executor.ctx.terms.mk_not(le10m);
    let n10n = executor.ctx.terms.mk_not(le10n);
    let n0m = executor.ctx.terms.mk_not(le0m);
    let n0n = executor.ctx.terms.mk_not(le0n);
    let body = executor
        .ctx
        .terms
        .mk_or(vec![nf, n10m, n10n, conj, n0m, n0n]);
    let axiom = executor.ctx.terms.mk_forall_with_triggers(
        vec![
            ("m".to_string(), int.clone()),
            ("n".to_string(), int.clone()),
        ],
        body,
        vec![vec![f_mn]],
    );
    executor.ctx.terms.mark_no_mbqi(axiom);
    let lt = executor.ctx.terms.mk_lt(c0, ten);
    executor.ctx.assertions.push(def);
    executor.ctx.assertions.push(axiom);
    executor.ctx.assertions.push(lt);
    executor.ctx.assertions.push(f_1010);

    let result = executor.check_sat();

    assert!(
        matches!(result, Ok(SolveResult::Unsat(_))),
        "an authored diagonal witness discharges the marked choose axiom: {result:?}"
    );
}
