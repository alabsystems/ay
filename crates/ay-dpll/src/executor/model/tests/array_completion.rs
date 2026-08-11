// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn run_completion(executor: &mut Executor, model: Model, extra_roots: &[TermId]) {
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);
    executor.final_lia_resolve_disabled = true;
    executor.complete_model_for_validation(extra_roots);
}

fn int_array_interp(
    default: Option<&str>,
    stores: &[(&str, &str)],
) -> ay_arrays::ArrayInterpretation {
    ay_arrays::ArrayInterpretation {
        default: default.map(str::to_string),
        stores: stores
            .iter()
            .map(|(index, value)| ((*index).to_string(), (*value).to_string()))
            .collect(),
        index_sort: Some(Sort::Int),
        element_sort: Some(Sort::Int),
    }
}

fn raw_int_select(executor: &mut Executor, array: TermId, index: TermId) -> TermId {
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![array, index], Sort::Int)
}

#[test]
fn missing_array_default_is_committed_used_and_idempotent() {
    let mut executor = Executor::new();
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let two = executor.ctx.terms.mk_int(BigInt::from(2));
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let nine = executor.ctx.terms.mk_int(BigInt::from(9));
    let at_one = raw_int_select(&mut executor, a, one);
    let at_two = raw_int_select(&mut executor, a, two);
    let at_three = raw_int_select(&mut executor, a, three);
    let assertion = executor.ctx.terms.mk_eq(at_one, nine);
    executor.ctx.assertions.push(assertion);

    let mut model = empty_model();
    let mut arrays = ArrayModel::default();
    arrays
        .array_values
        .insert(a, int_array_interp(None, &[("2", "8"), ("1", "9")]));
    model.array_model = Some(arrays);
    run_completion(&mut executor, model, &[]);

    let first = executor
        .last_model
        .as_ref()
        .and_then(|model| model.array_model.as_ref())
        .and_then(|arrays| arrays.array_values.get(&a))
        .expect("relevant non-conflicted array must be completed")
        .clone();
    assert_eq!(first.default.as_deref(), Some("0"));
    assert_eq!(
        first.stores,
        vec![
            ("2".to_string(), "8".to_string()),
            ("1".to_string(), "9".to_string()),
        ]
    );
    assert_eq!(
        executor.evaluate_term(executor.last_model.as_ref().unwrap(), at_one),
        EvalValue::Rational(BigRational::from(BigInt::from(9)))
    );
    assert_eq!(
        executor.evaluate_term(executor.last_model.as_ref().unwrap(), at_two),
        EvalValue::Rational(BigRational::from(BigInt::from(8)))
    );
    assert_eq!(
        executor.evaluate_term(executor.last_model.as_ref().unwrap(), at_three),
        EvalValue::Rational(BigRational::zero())
    );

    executor.complete_model_for_validation(&[]);
    let second = executor
        .last_model
        .as_ref()
        .and_then(|model| model.array_model.as_ref())
        .and_then(|arrays| arrays.array_values.get(&a))
        .expect("completion must remain installed");
    assert!(Executor::same_array_interpretation(&first, second));
}

#[test]
fn symbolic_default_is_authority_before_canonical_completion() {
    let mut executor = Executor::new();
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let default_a = executor.ctx.terms.mk_array_default(a);
    let mut values = HashMap::default();
    values.insert(default_a, BigInt::from(7));
    let mut model = empty_model();
    let mut arrays = ArrayModel::default();
    arrays
        .array_values
        .insert(a, int_array_interp(Some("0"), &[]));
    model.array_model = Some(arrays);
    model.lia_model = Some(LiaModel { values });

    run_completion(&mut executor, model, &[a]);
    let interp = executor
        .last_model
        .as_ref()
        .and_then(|model| model.array_model.as_ref())
        .and_then(|arrays| arrays.array_values.get(&a))
        .expect("symbolic default must materialize an interpretation");
    assert_eq!(interp.default.as_deref(), Some("7"));
}

#[test]
fn store_definition_chain_inherits_default_and_keeps_newest_write_first() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = executor.ctx.terms.mk_var("a", array_sort.clone());
    let b = executor.ctx.terms.mk_var("b", array_sort.clone());
    let c = executor.ctx.terms.mk_var("c", array_sort);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let two = executor.ctx.terms.mk_int(BigInt::from(2));
    let nine = executor.ctx.terms.mk_int(BigInt::from(9));
    let ten = executor.ctx.terms.mk_int(BigInt::from(10));
    let b_value = executor.ctx.terms.mk_store(a, one, nine);
    let c_value = executor.ctx.terms.mk_store(b, one, ten);
    let b_eq = executor.ctx.terms.mk_eq(b, b_value);
    let c_eq = executor.ctx.terms.mk_eq(c, c_value);
    // Reverse dependency order to exercise the bounded fixpoint rather than
    // relying on assertion insertion order.
    executor.ctx.assertions.push(c_eq);
    executor.ctx.assertions.push(b_eq);

    let mut model = empty_model();
    let mut arrays = ArrayModel::default();
    arrays
        .array_values
        .insert(a, int_array_interp(Some("7"), &[("0", "4")]));
    // This is the extractor's stale/fallback target default, not semantic
    // authority.  The hard definition must replace it with a's inherited 7.
    arrays
        .array_values
        .insert(b, int_array_interp(Some("0"), &[]));
    model.array_model = Some(arrays);
    run_completion(&mut executor, model, &[]);

    let arrays = executor
        .last_model
        .as_ref()
        .unwrap()
        .array_model
        .as_ref()
        .unwrap();
    let b_interp = arrays
        .array_values
        .get(&b)
        .expect("b must be derived")
        .clone();
    let c_interp = arrays
        .array_values
        .get(&c)
        .expect("c must be derived")
        .clone();
    assert_eq!(b_interp.default.as_deref(), Some("7"));
    assert_eq!(c_interp.default.as_deref(), Some("7"));
    assert_eq!(b_interp.stores.first(), Some(&("1".into(), "9".into())));
    assert_eq!(c_interp.stores.first(), Some(&("1".into(), "10".into())));

    let c_at_one = raw_int_select(&mut executor, c, one);
    let c_at_two = raw_int_select(&mut executor, c, two);
    assert_eq!(
        executor.evaluate_term(executor.last_model.as_ref().unwrap(), c_at_one),
        EvalValue::Rational(BigRational::from(BigInt::from(10)))
    );
    assert_eq!(
        executor.evaluate_term(executor.last_model.as_ref().unwrap(), c_at_two),
        EvalValue::Rational(BigRational::from(BigInt::from(7)))
    );

    let before = c_interp;
    executor.complete_model_for_validation(&[]);
    let after = executor
        .last_model
        .as_ref()
        .unwrap()
        .array_model
        .as_ref()
        .unwrap()
        .array_values
        .get(&c)
        .unwrap();
    assert!(Executor::same_array_interpretation(&before, after));

    // Keep the inherited base point observable and silence accidental future
    // removal of it as "redundant" when it differs from the default.
    assert!(after.stores.contains(&("0".into(), "4".into())));
}

#[test]
fn direct_alias_adopts_explicit_default_and_authoritative_store() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = executor.ctx.terms.mk_var("a", array_sort.clone());
    let b = executor.ctx.terms.mk_var("b", array_sort);
    let equality = executor.ctx.terms.mk_eq(a, b);
    executor.ctx.assertions.push(equality);

    let mut model = empty_model();
    let mut arrays = ArrayModel::default();
    arrays
        .array_values
        .insert(a, int_array_interp(Some("7"), &[("3", "2"), ("3", "1")]));
    model.array_model = Some(arrays);
    run_completion(&mut executor, model, &[]);

    let arrays = executor
        .last_model
        .as_ref()
        .unwrap()
        .array_model
        .as_ref()
        .unwrap();
    for term in [a, b] {
        let interp = arrays.array_values.get(&term).expect("alias must be total");
        assert_eq!(interp.default.as_deref(), Some("7"));
        assert_eq!(interp.stores.first(), Some(&("3".into(), "2".into())));
        assert_eq!(interp.stores.len(), 1, "shadowed older write stays hidden");
    }
}

#[test]
fn read_conflict_taints_store_and_alias_dependents_and_blocks_defaults() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = executor.ctx.terms.mk_var("a", array_sort.clone());
    let b = executor.ctx.terms.mk_var("b", array_sort.clone());
    let c = executor.ctx.terms.mk_var("c", array_sort);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let two = executor.ctx.terms.mk_int(BigInt::from(2));
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let ten = executor.ctx.terms.mk_int(BigInt::from(10));
    let b_value = executor.ctx.terms.mk_store(a, two, ten);
    let b_eq = executor.ctx.terms.mk_eq(b, b_value);
    let c_eq = executor.ctx.terms.mk_eq(c, b);
    executor.ctx.assertions.push(b_eq);
    executor.ctx.assertions.push(c_eq);

    let mut model = empty_model();
    let mut arrays = ArrayModel::default();
    // Even an already-present default is unusable after a read conflict.
    arrays
        .array_values
        .insert(a, int_array_interp(Some("7"), &[("1", "9")]));
    arrays.read_conflicted.insert(a);
    model.array_model = Some(arrays);
    run_completion(&mut executor, model, &[]);

    let arrays = executor
        .last_model
        .as_ref()
        .unwrap()
        .array_model
        .as_ref()
        .unwrap();
    assert!(arrays.read_conflicted.contains(&a));
    assert!(arrays.read_conflicted.contains(&b));
    assert!(arrays.read_conflicted.contains(&c));

    let a_at_one = raw_int_select(&mut executor, a, one);
    let a_at_three = raw_int_select(&mut executor, a, three);
    let b_at_two = raw_int_select(&mut executor, b, two);
    let b_at_three = raw_int_select(&mut executor, b, three);
    let model = executor.last_model.as_ref().unwrap();
    assert_eq!(
        executor.evaluate_term(model, a_at_one),
        EvalValue::Rational(BigRational::from(BigInt::from(9))),
        "an exact explicit store remains authoritative"
    );
    assert_eq!(
        executor.evaluate_term(model, a_at_three),
        EvalValue::Unknown
    );
    assert_eq!(
        executor.evaluate_term(model, b_at_two),
        EvalValue::Rational(BigRational::from(BigInt::from(10))),
        "the structural newest write remains authoritative"
    );
    assert_eq!(
        executor.evaluate_term(model, b_at_three),
        EvalValue::Unknown
    );
    assert_eq!(
        executor.compare_array_models_normalized(model, b, c),
        None,
        "conflicted aliases must not acquire an exact normalized form"
    );
}

#[test]
fn unsupported_hard_array_definition_is_not_canonicalized() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = executor.ctx.terms.mk_var("a", array_sort.clone());
    let unsupported =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("as-array"), Vec::<TermId>::new(), array_sort);
    let definition = executor.ctx.terms.mk_eq(a, unsupported);
    executor.ctx.assertions.push(definition);

    run_completion(&mut executor, empty_model(), &[]);

    assert!(executor
        .last_model
        .as_ref()
        .and_then(|model| model.array_model.as_ref())
        .and_then(|arrays| arrays.array_values.get(&a))
        .and_then(|interp| interp.default.as_ref())
        .is_none());
}

#[test]
fn active_unknown_direct_read_blocks_array_totalization() {
    let mut executor = Executor::new();
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::Bool));
    let zero = executor.ctx.terms.mk_int(BigInt::zero());
    let read = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![a, zero], Sort::Bool);
    executor.ctx.assertions.push(read);

    run_completion(&mut executor, empty_model(), &[]);

    assert!(executor
        .last_model
        .as_ref()
        .and_then(|model| model.array_model.as_ref())
        .and_then(|arrays| arrays.array_values.get(&a))
        .and_then(|interp| interp.default.as_ref())
        .is_none());
}

/// #guarded-vacuous-array-read: a select read that occurs only under a
/// disjunct the model already satisfies (guard true without the read) leaves
/// the read Unknown. The gate-verified second completion pass must commit a
/// canonical default for the array — the completed model satisfies every
/// assertion, so re-validation accepts it and `(get-model)` can print a full
/// witness instead of the whole-model error.
#[test]
fn vacuous_guarded_unknown_read_completes_gate_verified() {
    let mut executor = Executor::new();
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::zero());
    let one = executor.ctx.terms.mk_int(BigInt::one());
    let nine = executor.ctx.terms.mk_int(BigInt::from(9));
    let read = raw_int_select(&mut executor, a, zero);
    let guard = executor.ctx.terms.mk_eq(x, one);
    let read_pin = executor.ctx.terms.mk_eq(read, nine);
    let assertion =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("or"), vec![guard, read_pin], Sort::Bool);
    executor.ctx.assertions.push(assertion);

    let mut model = empty_model();
    let mut values = HashMap::default();
    values.insert(x, BigInt::one());
    model.lia_model = Some(LiaModel { values });
    run_completion(&mut executor, model, &[]);

    let interp = executor
        .last_model
        .as_ref()
        .and_then(|model| model.array_model.as_ref())
        .and_then(|arrays| arrays.array_values.get(&a))
        .expect("vacuously-read array must be completed by the gate-verified pass");
    assert_eq!(interp.default.as_deref(), Some("0"));
    assert_eq!(
        executor.evaluate_term(executor.last_model.as_ref().unwrap(), read),
        EvalValue::Rational(BigRational::zero())
    );
}

/// #guarded-vacuous-array-read, RETRACTION path: an Unknown active read that
/// genuinely constrains the cell in a way the completion cannot discharge —
/// `(not (= a[0] 0))` pins the cell away from the canonical default, and the
/// negative shape is invisible to `extract_value_from_asserted_equalities`
/// (positive top-level equalities only) — so the gate must refute the
/// canonical-default candidate and the pass must retract to the fail-closed
/// partial model (no fabricated default ships).
///
/// (Pre-merge this test used a positive pin `a[0] = 9`; the upstream
/// asserted-equality extraction now legitimately completes that shape to a
/// genuine gate-verified witness — see
/// `equality_pinned_unknown_read_completes_to_genuine_witness` — so the
/// retraction path is exercised with a pin that stays undischargeable.)
#[test]
fn constrained_unknown_read_candidate_is_refuted_and_retracted() {
    let mut executor = Executor::new();
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let zero = executor.ctx.terms.mk_int(BigInt::zero());
    let read = raw_int_select(&mut executor, a, zero);
    let read_eq_zero = executor.ctx.terms.mk_eq(read, zero);
    let assertion = executor.ctx.terms.mk_not(read_eq_zero);
    executor.ctx.assertions.push(assertion);

    run_completion(&mut executor, empty_model(), &[]);

    assert!(
        executor
            .last_model
            .as_ref()
            .and_then(|model| model.array_model.as_ref())
            .and_then(|arrays| arrays.array_values.get(&a))
            .and_then(|interp| interp.default.as_ref())
            .is_none(),
        "a refuted completion candidate must be retracted, not committed"
    );
    assert_eq!(
        executor.evaluate_term(executor.last_model.as_ref().unwrap(), read),
        EvalValue::Unknown
    );
}

/// Twin of the retraction test for the POSITIVE-pin shape: `a[0] = 9` is a
/// top-level asserted equality, so the upstream asserted-equality extraction
/// resolves the read to `9` and the completion commits a genuine witness
/// (`a = store(const .., 0, 9)`) instead of retracting — the completed model
/// must actually satisfy the pin (the read evaluates to `9`, never to a
/// fabricated canonical default).
#[test]
fn equality_pinned_unknown_read_completes_to_genuine_witness() {
    let mut executor = Executor::new();
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let zero = executor.ctx.terms.mk_int(BigInt::zero());
    let nine = executor.ctx.terms.mk_int(BigInt::from(9));
    let read = raw_int_select(&mut executor, a, zero);
    let assertion = executor.ctx.terms.mk_eq(read, nine);
    executor.ctx.assertions.push(assertion);

    run_completion(&mut executor, empty_model(), &[]);

    assert_eq!(
        executor.evaluate_term(executor.last_model.as_ref().unwrap(), read),
        EvalValue::Rational(BigRational::from(BigInt::from(9))),
        "the completed model must satisfy the asserted pin a[0] = 9"
    );
}

// ---------------------------------------------------------------------------
// #opaque-array-app-def: OPAQUE array-valued UF applications as definition
// targets, and the congruence filter that decides admission.
//
// These are WHITE-BOX tests of `collect_array_completion_graph`. The
// end-to-end verdicts live in `model::tests::seq_array_uf_def`, but those
// cannot distinguish "the filter refused" from "the solver refuted first" —
// every congruence-conflicting input is UNSAT and never reaches the model
// gate. Reading the admitted definition set directly is what makes the filter
// itself testable.
// ---------------------------------------------------------------------------

/// Parse + execute a declaration/assertion prelude (no `check-sat`), then read
/// the array-completion definition edges the graph builder admits.
fn admitted_array_definitions(input: &str) -> (Executor, Vec<(TermId, TermId)>) {
    let commands = ay_frontend::parse(input).expect("valid SMT-LIB input");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("declarations and assertions execute");
    let (_relevant, _edges, _aliases, definitions, _required_reads) =
        executor.collect_array_completion_graph(&empty_model(), &[]);
    (executor, definitions)
}

/// Whether any admitted definition TARGETS an application of `symbol`.
fn defines_application_of(
    executor: &Executor,
    definitions: &[(TermId, TermId)],
    symbol: &str,
) -> bool {
    definitions.iter().any(|&(target, _)| {
        matches!(executor.ctx.terms.get(target), TermData::App(sym, _) if sym.name() == symbol)
    })
}

const OPAQUE_APP_PRELUDE: &str = "(set-logic ALL)\
     (declare-sort Elem 0)\
     (declare-fun v () Elem)\
     (declare-fun w () Elem)\
     (declare-fun g (Elem) (Array (_ BitVec 4) Int))";

/// The admitting case: a single application of `g`, defined once by a
/// const-array. Congruence relates it to nothing, so the definition is safe to
/// publish — and this is the edge that turns
/// `array_valued_uf_select_over_bitvec_index_resolves_through_its_definition`
/// from `unknown` into `sat`.
#[test]
fn lone_opaque_array_app_definition_is_admitted() {
    let (executor, definitions) = admitted_array_definitions(&format!(
        "{OPAQUE_APP_PRELUDE}\
         (assert (= ((as const (Array (_ BitVec 4) Int)) 7) (g v)))\
         (assert (= (select (g v) #x3) 7))"
    ));
    assert!(
        defines_application_of(&executor, &definitions, "g"),
        "a lone array-valued application with one const-array definition is a \
         definition target"
    );
}

/// CONGRUENCE FILTER, clause (ii): a SECOND application of the same symbol
/// exists, so `v = w` could force the two to denote one array. Publishing a
/// value for `(g v)` alone could then contradict what the same model says
/// about `(g w)` — nothing downstream re-derives UF congruence over whole-array
/// values — so the definition must be REFUSED and the application falls back to
/// its reads-derived candidate.
#[test]
fn opaque_array_app_definition_is_refused_with_a_congruent_sibling() {
    let (executor, definitions) = admitted_array_definitions(&format!(
        "{OPAQUE_APP_PRELUDE}\
         (assert (= ((as const (Array (_ BitVec 4) Int)) 7) (g v)))\
         (assert (= (select (g w) #x3) 5))"
    ));
    assert!(
        !defines_application_of(&executor, &definitions, "g"),
        "a sibling application of the same symbol must fail the definition \
         closed (congruence could relate them)"
    );
}

/// CONGRUENCE FILTER, clause (i): the SAME application carries two different
/// definitions. There is no principled winner, so both are refused rather than
/// one being chosen — the same discipline
/// `unique_array_constructor_definition_excluding` applies to array variables.
#[test]
fn ambiguous_opaque_array_app_definitions_are_refused() {
    let (executor, definitions) = admitted_array_definitions(&format!(
        "{OPAQUE_APP_PRELUDE}\
         (assert (= ((as const (Array (_ BitVec 4) Int)) 0) (g v)))\
         (assert (= ((as const (Array (_ BitVec 4) Int)) 1) (g v)))"
    ));
    assert!(
        !defines_application_of(&executor, &definitions, "g"),
        "competing definitions of one application must both be refused"
    );
}

/// An ordinary array VARIABLE definition is untouched by the new arm: the
/// filter is additive, never a restriction on the pre-existing `TermData::Var`
/// classification.
#[test]
fn array_variable_definitions_are_unaffected_by_the_opaque_app_arm() {
    let (executor, definitions) = admitted_array_definitions(
        "(set-logic ALL)\
         (declare-fun a () (Array (_ BitVec 4) Int))\
         (assert (= ((as const (Array (_ BitVec 4) Int)) 7) a))",
    );
    assert!(
        definitions.iter().any(|&(target, _)| {
            matches!(executor.ctx.terms.get(target), TermData::Var(name, _) if name == "a")
        }),
        "the array-variable definition edge must still be recorded"
    );
}
