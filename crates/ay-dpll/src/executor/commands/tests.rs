// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use super::Executor;
use crate::executor::model::Model;
use crate::executor_types::{SolveResult, StatValue, Statistics, UnknownReason};
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::Symbol;
use ay_core::Sort;
use ay_frontend::sexp::SExpr;
use ay_frontend::{parse, Command};
use num_bigint::BigInt;
use num_rational::BigRational;

#[test]
fn test_get_info_name_trims_colon_prefix() {
    let exec = Executor::new();
    assert_eq!(exec.get_info(":name"), "(:name \"ay\")");
}

#[test]
fn test_get_info_version_reports_structured_build_provenance() {
    let exec = Executor::new();
    let out = exec.get_info(":version");

    assert!(
        out.starts_with("(:version \""),
        "unexpected version output: {out}"
    );
    assert!(out.ends_with("\")"), "unexpected version output: {out}");
    assert!(
        !out.contains('\n'),
        "SMT-LIB version output should stay on one line: {out}"
    );

    for field in [
        "build.version=",
        "build.increment=",
        "build.commit=",
        "build.datetime_utc=",
        "build.stamp=",
        env!("CARGO_PKG_VERSION"),
        env!("AY_BUILD_INCREMENT"),
        env!("AY_BUILD_COMMIT"),
        env!("AY_BUILD_DATETIME_UTC"),
        env!("AY_BUILD_STAMP"),
    ] {
        assert!(
            out.contains(field),
            "expected {field} in structured version output: {out}"
        );
    }
}

#[test]
fn test_get_info_reason_unknown_requires_unknown_result() {
    let exec = Executor::new();
    assert_eq!(
        exec.get_info(":reason-unknown"),
        "(error \"no unknown result to explain\")"
    );
}

#[test]
fn test_get_info_reason_unknown_formats_reason() {
    let mut exec = Executor::new();
    exec.last_result = Some(SolveResult::Unknown);
    exec.last_unknown_reason = Some(UnknownReason::MemoryLimit);
    assert_eq!(exec.get_info("reason-unknown"), "(:reason-unknown memout)");
}

#[test]
fn test_get_info_assertion_stack_levels_counts_assertions() {
    let mut exec = Executor::new();
    let a = exec.ctx.terms.mk_var("a", Sort::Bool);
    exec.ctx.assertions.push(a);
    exec.ctx.assertions.push(exec.ctx.terms.mk_not(a));
    assert_eq!(
        exec.get_info(":assertion-stack-levels"),
        "(:assertion-stack-levels 2)"
    );
}

#[test]
fn test_format_statistics_smt2_formats_extra_fields() {
    let mut exec = Executor::new();
    let mut stats = Statistics {
        conflicts: 1,
        decisions: 2,
        time_seconds: 0.25,
        memory_mb: 10.5,
        max_memory_mb: 11.5,
        rlimit_count: 17,
        ..Default::default()
    };
    stats.extra.insert("foo_bar".to_string(), StatValue::Int(7));
    stats
        .extra
        .insert("time_sec".to_string(), StatValue::Float(1.5));
    stats
        .extra
        .insert("note".to_string(), StatValue::String("hello".to_string()));
    exec.last_statistics = stats;

    let out = exec.get_info(":all-statistics");
    assert!(out.starts_with('('));
    assert!(out.ends_with(')'));
    assert!(out.contains(":conflicts"));
    assert!(out.contains(":decisions"));
    assert!(out.contains(":time"));
    assert!(out.contains("0.25"));
    assert!(out.contains(":memory"));
    assert!(out.contains("10.50"));
    assert!(out.contains(":max-memory"));
    assert!(out.contains("11.50"));
    assert!(out.contains(":rlimit-count"));
    assert!(out.contains("17"));
    assert!(out.contains(":foo-bar"));
    assert!(out.contains(":time-sec"));
    assert!(out.contains("1.50"));
    assert!(out.contains("\"hello\""));
}

#[test]
fn test_get_option_value_reports_known_and_unknown_options() {
    let mut exec = Executor::new();
    exec.execute(&Command::SetOption(
        ":produce-unsat-cores".to_string(),
        SExpr::True,
    ))
    .unwrap();

    assert_eq!(
        exec.get_option_value(":produce-unsat-cores"),
        "(:produce-unsat-cores true)"
    );
    assert_eq!(
        exec.get_option_value(":does-not-exist"),
        "(error \"unknown option: :does-not-exist\")"
    );
}

#[test]
fn test_get_assertions_empty_and_nonempty() {
    let mut exec = Executor::new();
    assert_eq!(exec.assertions(), "()");

    let a = exec.ctx.terms.mk_var("a", Sort::Bool);
    exec.ctx.assertions.push(a);
    exec.ctx.assertions.push(exec.ctx.terms.mk_not(a));
    assert_eq!(exec.assertions(), "(a\n (not a))");
}

#[test]
fn test_labels_follow_z3_result_availability() {
    let mut exec = Executor::new();
    assert_eq!(exec.labels(), "(error \"labels are not available\")");

    exec.last_result = Some(SolveResult::Sat);
    assert_eq!(exec.labels(), "(labels)");

    exec.last_result = Some(SolveResult::Unknown);
    assert_eq!(exec.labels(), "(labels)");

    exec.last_result = Some(SolveResult::unsat());
    assert_eq!(exec.labels(), "(error \"labels are not available\")");
}

#[test]
fn test_format_term_handles_core_term_forms() {
    let mut exec = Executor::new();

    let a = exec.ctx.terms.mk_var("a", Sort::Bool);
    assert_eq!(exec.format_term(a), "a");

    let let_var = exec.ctx.terms.mk_var("let", Sort::Bool);
    assert_eq!(exec.format_term(let_var), "|let|");

    let int_term = exec.ctx.terms.mk_int(BigInt::from(-7));
    assert_eq!(exec.format_term(int_term), "(- 7)");

    let rat_term = exec
        .ctx
        .terms
        .mk_rational(BigRational::new(BigInt::from(3), BigInt::from(2)));
    assert_eq!(exec.format_term(rat_term), "(/ 3 2)");

    let str_term = exec.ctx.terms.mk_string("hi".to_string());
    assert_eq!(exec.format_term(str_term), "\"hi\"");

    let bv_term = exec.ctx.terms.mk_bitvec(BigInt::from(1), 8);
    assert_eq!(exec.format_term(bv_term), "#x01");

    let not_a = exec.ctx.terms.mk_not(a);
    assert_eq!(exec.format_term(not_a), "(not a)");

    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let two = exec.ctx.terms.mk_int(BigInt::from(2));
    let ite_term = exec.ctx.terms.mk_ite(a, one, two);
    assert_eq!(exec.format_term(ite_term), "(ite a 1 2)");

    let c = exec.ctx.terms.mk_app(Symbol::named("c"), vec![], Sort::Int);
    assert_eq!(exec.format_term(c), "c");

    let arg1 = exec.ctx.terms.mk_int(BigInt::from(1));
    let arg2 = exec.ctx.terms.mk_int(BigInt::from(2));
    let f_app = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![arg1, arg2], Sort::Int);
    assert_eq!(exec.format_term(f_app), "(f 1 2)");

    let x = exec.ctx.terms.mk_var("x", Sort::Int);
    let let_term = exec.ctx.terms.mk_let(vec![("x".to_string(), int_term)], x);
    assert_eq!(exec.format_term(let_term), "(let ((x (- 7))) x)");

    let forall_term = exec.ctx.terms.mk_forall(
        vec![("x".to_string(), Sort::Int)],
        exec.ctx.terms.true_term(),
    );
    assert_eq!(exec.format_term(forall_term), "(forall ((x Int)) true)");

    let exists_term = exec.ctx.terms.mk_exists(
        vec![("y".to_string(), Sort::Bool)],
        exec.ctx.terms.false_term(),
    );
    assert_eq!(exec.format_term(exists_term), "(exists ((y Bool)) false)");
}

#[test]
fn test_get_assignment_requires_produce_assignments() {
    let exec = Executor::new();
    assert_eq!(
        exec.get_assignment(),
        "(error \"assignment generation is not enabled, set :produce-assignments to true\")"
    );
}

#[test]
fn test_get_assignment_sat_model_named_term() {
    let mut exec = Executor::new();
    exec.execute(&Command::SetOption(
        ":produce-assignments".to_string(),
        SExpr::True,
    ))
    .unwrap();

    let cmds = parse(
        r#"
            (set-logic QF_UF)
            (declare-const a Bool)
            (assert (! a :named n1))
        "#,
    )
    .unwrap();
    exec.execute_all(&cmds).unwrap();

    let a = exec.ctx.terms.lookup("a").unwrap();
    let mut term_to_var = HashMap::default();
    term_to_var.insert(a, 0);

    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(Model {
        sat_model: vec![true],
        term_to_var,
        bool_overrides: HashMap::default(),
        euf_model: None,
        array_model: None,
        lra_model: None,
        lia_model: None,
        bv_model: None,
        fp_model: None,
        string_model: None,
        seq_model: None,
        completed_values: HashMap::default(),
        dt_ground: HashMap::default(),
        dt_pins: HashMap::default(),
    });

    assert_eq!(exec.get_assignment(), "((n1 true))");
}

#[test]
fn test_get_unsat_core_requires_produce_unsat_cores() {
    let exec = Executor::new();
    assert_eq!(
        exec.unsat_core(),
        "(error \"unsat core generation is not enabled, set :produce-unsat-cores to true\")"
    );
}

#[test]
fn test_get_unsat_core_single_named_assertion() {
    let mut exec = Executor::new();
    exec.execute(&Command::SetOption(
        ":produce-unsat-cores".to_string(),
        SExpr::True,
    ))
    .unwrap();

    let cmds = parse(
        r#"
            (set-logic QF_UF)
            (declare-const a Bool)
            (assert (! a :named n1))
        "#,
    )
    .unwrap();
    exec.execute_all(&cmds).unwrap();

    exec.last_result = Some(SolveResult::unsat());
    assert_eq!(exec.unsat_core(), "(n1)");
}

#[test]
fn test_get_unsat_assumptions_prefers_minimal_core_if_present() {
    let mut exec = Executor::new();
    let a = exec.ctx.terms.mk_var("a", Sort::Bool);
    let b = exec.ctx.terms.mk_var("b", Sort::Bool);

    exec.last_result = Some(SolveResult::unsat());
    exec.last_assumptions = Some(vec![a, b]);
    exec.last_assumption_core = Some(vec![b]);

    assert_eq!(exec.unsat_assumptions(), "(b)");
}

#[test]
fn test_get_unsat_assumptions_errors_without_check_sat_assuming() {
    let mut exec = Executor::new();
    exec.last_result = Some(SolveResult::unsat());
    exec.last_assumptions = None;
    assert_eq!(
        exec.unsat_assumptions(),
        "(error \"no check-sat-assuming has been performed\")"
    );
}

/// Run an SMT-LIB script and collect every command output line.
fn run_script_collect(script: &str) -> Vec<String> {
    let mut exec = Executor::new();
    let cmds = parse(script).unwrap();
    let mut out = Vec::new();
    for cmd in &cmds {
        if let Some(s) = exec.execute(cmd).unwrap() {
            out.push(s);
        }
    }
    out
}

#[test]
fn ordinary_result_sort_overloads_remain_independent_for_sat_and_unsat() {
    let sat = run_script_collect(
        r#"
            (set-logic ALL)
            (declare-fun f (Int) Int)
            (declare-fun f (Int) Bool)
            (assert (= ((as f Int) 0) 0))
            (assert (not ((as f Bool) 0)))
            (check-sat)
        "#,
    );
    assert_eq!(sat.last().map(String::as_str), Some("sat"), "{sat:?}");

    let unsat = run_script_collect(
        r#"
            (set-logic ALL)
            (declare-fun f (Int) Int)
            (declare-fun f (Int) Bool)
            (assert (= ((as f Int) 0) 0))
            (assert (= ((as f Int) 0) 1))
            (check-sat)
        "#,
    );
    assert_eq!(unsat.last().map(String::as_str), Some("unsat"), "{unsat:?}");
}

#[test]
fn overloaded_declarations_serialize_completely_with_surface_names() {
    let mut exec = Executor::new();
    let commands = parse(
        r#"
            (declare-fun f (Int) Int)
            (declare-fun f (Int) Bool)
            (assert (= ((as f Int) 0) 0))
            (assert ((as f Bool) 0))
        "#,
    )
    .unwrap();
    exec.execute_all(&commands).unwrap();

    let serialized = exec.to_smtlib2();
    assert_eq!(serialized.matches("(declare-fun f (Int)").count(), 2);
    assert!(!serialized.contains("__ay_overload_"), "{serialized}");
    assert!(serialized.contains("(declare-fun f (Int) Int)"));
    assert!(serialized.contains("(declare-fun f (Int) Bool)"));

    let replay = run_script_collect(&serialized);
    assert_eq!(
        replay.last().map(String::as_str),
        Some("sat"),
        "{serialized}"
    );
}

#[test]
fn unsupported_sort_preflight_scans_every_overload() {
    let mut exec = Executor::new();
    let commands = parse("(declare-fun f (Int) Int)").unwrap();
    exec.execute_all(&commands).unwrap();

    // Textual declarations correctly reject this width during elaboration.
    // Native adapters can supply an already-built core Sort, so add that
    // overload through the corresponding context hook to exercise the later
    // solve preflight's defense-in-depth scan.
    exec.ctx
        .register_native_function_alias(
            "f".to_string(),
            "__ay_test_wide_f".to_string(),
            vec![Sort::bitvec(1_048_577)],
            Sort::Int,
        )
        .unwrap();
    assert_eq!(exec.unsupported_bitvector_width(&[]), Some(1_048_577));
}

#[test]
fn overloaded_model_output_uses_surface_names_for_distinct_tables() {
    let output = run_script_collect(
        r#"
            (set-option :produce-models true)
            (set-logic ALL)
            (declare-fun f (Int) Int)
            (declare-fun f (Int) Bool)
            (check-sat)
            (get-model)
        "#,
    );
    assert_eq!(
        output.first().map(String::as_str),
        Some("sat"),
        "{output:?}"
    );
    let model = output.last().expect("get-model output");
    assert_eq!(model.matches("(define-fun f ").count(), 2, "{model}");
    assert!(!model.contains("__ay_overload_"), "{model}");
}

#[test]
fn model_hides_custom_datatype_recognizer_alias_but_keeps_overloads() {
    let mut exec = Executor::new();
    let commands = parse(
        r#"
            (set-option :produce-models true)
            (set-logic ALL)
            (declare-datatype Color ((red) (blue)))
            (declare-fun f (Int) Int)
            (declare-fun f (Int) Bool)
        "#,
    )
    .unwrap();
    exec.execute_all(&commands).unwrap();

    exec.ctx
        .register_native_function_alias(
            "r-red".to_string(),
            "is-red".to_string(),
            vec![Sort::Uninterpreted("Color".to_string())],
            Sort::Bool,
        )
        .unwrap();
    exec.ctx
        .register_native_function_alias(
            "r-red".to_string(),
            "is-red".to_string(),
            vec![Sort::Uninterpreted("Color".to_string())],
            Sort::Bool,
        )
        .expect("exact datatype-member alias re-registration is idempotent");
    assert!(exec.is_dt_internal_symbol("is-red"));
    assert!(exec.is_dt_internal_symbol("r-red"));
    for (name, info) in exec
        .ctx
        .symbol_iter()
        .filter(|(name, _)| name.as_str() == "f")
    {
        assert!(!exec.is_dt_internal_symbol(name));
        assert!(!exec.is_dt_internal_symbol(exec.ctx.symbol_identity_name(name, info)));
    }

    exec.last_result = Some(SolveResult::Sat);
    let model = exec.model();
    assert!(!model.contains("r-red"), "{model}");
    assert!(!model.contains("is-red"), "{model}");
    assert_eq!(model.matches("(define-fun f ").count(), 2, "{model}");
}

#[test]
fn test_unsat_core_survives_get_consequences_state_clobber() {
    // #unsat-core-staleness (skeptic reproducer x1): a get-consequences (or
    // get-abduct) between an UNSAT check-sat-assuming and get-unsat-core runs
    // internal probes that harvest their OWN assumption cores. Restoring
    // last_result/last_assumptions without the core provenance fields let the
    // second get-unsat-core print the PROBE's harvest — a SATISFIABLE set
    // ((< x 5) without the load-bearing named h1). Both core prints must be
    // identical and contain h1.
    let outputs = run_script_collect(
        r#"
            (set-option :produce-unsat-cores true)
            (set-logic QF_LIA)
            (declare-const x Int)
            (declare-const y Int)
            (declare-const p Bool)
            (assert (! (>= x 5) :named h1))
            (check-sat-assuming ((< x 5) (> y 10)))
            (get-unsat-core)
            (get-consequences ((< x 5)) (p))
            (get-unsat-core)
        "#,
    );
    assert_eq!(outputs[0], "unsat", "verdict: {outputs:?}");
    let first_core = &outputs[1];
    let second_core = outputs.last().unwrap();
    assert!(
        first_core.contains("h1"),
        "first core must contain the load-bearing named assertion: {outputs:?}"
    );
    assert!(
        second_core.contains("h1"),
        "core after get-consequences must still contain h1 (stale-probe \
         harvest must not survive the wrapper restore): {outputs:?}"
    );
    assert_eq!(
        first_core, second_core,
        "get-consequences must not change the printable core: {outputs:?}"
    );
}

#[test]
fn test_unsat_proof_survives_get_consequences_probe_solves() {
    let outputs = run_script_collect(
        r#"
            (set-option :produce-proofs true)
            (set-logic QF_BOOL)
            (declare-const p Bool)
            (declare-const q Bool)
            (assert p)
            (assert q)
            (check-sat-assuming ((not q)))
            (get-proof)
            (get-consequences () (p))
            (get-proof)
        "#,
    );
    assert_eq!(outputs[0], "unsat", "verdict: {outputs:?}");
    assert!(
        outputs[1].contains("(cl)"),
        "first proof must derive the empty clause: {outputs:?}"
    );
    assert_eq!(
        outputs[1], outputs[3],
        "internal consequence probes must restore the complete proof/scope snapshot: {outputs:?}"
    );
}

#[test]
fn combined_theory_consequence_probe_restores_proof_assertion_provenance() {
    let mut exec = Executor::new();
    let setup = parse(
        r#"
            (set-option :produce-proofs true)
            (set-logic ALL)
            (declare-const q Bool)
            (declare-const r Bool)
            (declare-const x Int)
            (declare-fun f (Int) Int)
            (assert q)
            (assert r)
            (assert (= x 0))
            (check-sat-assuming ((not q)))
        "#,
    )
    .unwrap();
    let setup_outputs = exec.execute_all(&setup).unwrap();
    assert_eq!(setup_outputs, ["unsat"], "{setup_outputs:?}");
    assert!(exec.last_proof.is_some(), "initial proof was not retained");

    // Model a legitimate narrower preprocessing window: `r` is an immutable
    // authored root but is irrelevant to the retained q / not-q refutation, so
    // this proof window does not export it as a current premise. A later
    // combined-theory probe will rediscover `r` in its own preprocessing
    // window; restoring the old proof must restore this narrower map as well.
    let r = exec.ctx.terms.lookup("r").expect("declared r");
    let provenance = exec
        .proof_problem_assertion_provenance
        .as_mut()
        .expect("public solve should freeze proof assertion provenance");
    assert!(
        provenance.original_problem_assertions.contains(&r),
        "r must remain an immutable authored root"
    );
    provenance
        .problem_assertions
        .retain(|assertion| *assertion != r);
    provenance.assertion_sources.remove(&r);

    let before = exec
        .proof_problem_assertion_provenance
        .clone()
        .expect("narrowed proof assertion provenance");
    let probe = parse(
        r#"
            (get-consequences ()
                ((= (+ (f x) 1) (+ (f 0) 1))))
        "#,
    )
    .unwrap();
    let probe_outputs = exec.execute_all(&probe).unwrap();
    assert!(
        probe_outputs
            .first()
            .is_some_and(|output| output.starts_with("(sat (")),
        "combined-theory consequence probe did not complete: {probe_outputs:?}"
    );

    let after = exec
        .proof_problem_assertion_provenance
        .as_ref()
        .expect("probe must restore proof assertion provenance");
    assert_eq!(
        after.original_problem_assertions, before.original_problem_assertions,
        "probe changed the authored assertion roots"
    );
    assert_eq!(
        after.problem_assertions, before.problem_assertions,
        "probe changed the exportable assertion roots"
    );
    assert_eq!(
        after.assertion_sources, before.assertion_sources,
        "probe changed the proof assertion source map"
    );
}

#[test]
fn test_unsat_core_complementary_named_and_assumption_literal() {
    // #unsat-core-polarity (skeptic reproducer s_f): a named assertion whose
    // literal is COMPLEMENTARY to a user assumption literal on the same
    // variable, with base assertions that unit-propagate. The SAT-level BFS
    // used to attribute the conflict to the LAST-registered polarity for the
    // variable, dropping the load-bearing named (not r) and printing the
    // SATISFIABLE set (r (not s)). Any sound core here must contain nm0:
    // every nm0-free subset of {r, (not s)} is SAT with the base.
    // Both assumption orders must be sound (the defect was order-sensitive).
    for assumptions in ["((not s) r)", "(r (not s))"] {
        let outputs = run_script_collect(&format!(
            r#"
                (set-option :produce-unsat-cores true)
                (set-logic QF_UF)
                (declare-const p Bool)
                (declare-const r Bool)
                (declare-const s Bool)
                (assert (or s (not p)))
                (assert (= (not p) r))
                (assert (! (not r) :named nm0))
                (check-sat-assuming {assumptions})
                (get-unsat-core)
            "#
        ));
        assert_eq!(
            outputs[0], "unsat",
            "verdict for {assumptions}: {outputs:?}"
        );
        let core = &outputs[1];
        assert!(
            core.contains("nm0"),
            "core for assumption order {assumptions} must contain the \
             load-bearing named assertion nm0: {core}"
        );
    }
}

/// #dump-self-contained: a serialized script must declare every uninterpreted
/// sort it references (declaration sorts, term sorts, quantifier binder
/// sorts), or the dump is unusable as a standalone repro. The sort names are
/// verification-consumer-shaped on purpose (`__verification_consumer_mutref::int` needs pipe-quoting).
#[test]
fn serialized_script_declares_referenced_uninterpreted_sorts() {
    let mut exec = Executor::new();
    let commands = parse(
        r#"
            (set-logic ALL)
            (declare-sort |__verification_consumer_mutref::int| 0)
            (declare-sort Unit 0)
            (declare-const u Unit)
            (declare-const m |__verification_consumer_mutref::int|)
            (declare-const n |__verification_consumer_mutref::int|)
            (declare-fun cur (|__verification_consumer_mutref::int|) Int)
            (assert (= (cur m) 5))
            (assert (distinct m n))
            (assert (= u u))
        "#,
    )
    .unwrap();
    exec.execute_all(&commands).unwrap();

    let script = exec.to_smtlib2();
    assert!(
        script.contains("(declare-sort |__verification_consumer_mutref::int| 0)"),
        "{script}"
    );
    assert!(script.contains("(declare-sort Unit 0)"), "{script}");
    // Sort declarations must precede the first symbol declaration that uses
    // them.
    let sort_pos = script.find("(declare-sort |__verification_consumer_mutref::int| 0)");
    let use_pos = script.find("(declare-const m");
    assert!(sort_pos < use_pos, "{script}");
    // The built-in FP RoundingMode sort must never be re-declared.
    assert!(!script.contains("(declare-sort RoundingMode"), "{script}");

    // Round-trip: the serialized script must parse and solve in a fresh
    // executor through ay's own front end.
    let replay = run_script_collect(&script);
    assert_eq!(replay.last().map(String::as_str), Some("sat"), "{script}");
}

/// #dump-self-contained: an uninterpreted sort reachable only through a
/// compound sort (array index/element, seq element) or a quantifier binder is
/// still declared.
#[test]
fn serialized_script_declares_sorts_nested_in_compound_sorts() {
    let mut exec = Executor::new();
    let commands = parse(
        r#"
            (set-logic ALL)
            (declare-sort Elem 0)
            (declare-sort Idx 0)
            (declare-sort SeqElem 0)
            (declare-sort BinderOnly 0)
            (declare-const a (Array Idx Elem))
            (declare-const i Idx)
            (declare-const s (Seq SeqElem))
            (assert (= (select a i) (select a i)))
            (assert (= s s))
            (assert (forall ((q BinderOnly)) (= q q)))
        "#,
    )
    .unwrap();
    exec.execute_all(&commands).unwrap();

    let script = exec.to_smtlib2();
    assert!(script.contains("(declare-sort Elem 0)"), "{script}");
    assert!(script.contains("(declare-sort Idx 0)"), "{script}");
    assert!(script.contains("(declare-sort SeqElem 0)"), "{script}");
    assert!(script.contains("(declare-sort BinderOnly 0)"), "{script}");

    let replay = run_script_collect(&script);
    assert_eq!(replay.last().map(String::as_str), Some("sat"), "{script}");
}

/// #dump-self-contained: a script whose terms touch a declared DATATYPE sort
/// is serialized fail-visible — the carrier is declared as an uninterpreted
/// sort and the script carries a warning header marking it as a UF
/// over-abstraction (not oracle-equivalent for external solvers).
#[test]
fn serialized_script_marks_datatype_sorts_fail_visible() {
    let mut exec = Executor::new();
    let commands = parse(
        r#"
            (set-logic ALL)
            (declare-datatypes ((Pair 0))
                (((mk-pair (first Int) (second Int)))))
            (declare-const p Pair)
            (assert (= p (mk-pair 1 2)))
            (assert (= (first p) 1))
            (assert ((_ is mk-pair) p))
        "#,
    )
    .unwrap();
    exec.execute_all(&commands).unwrap();

    let script = exec.to_smtlib2();
    assert!(
        script.contains("; WARNING: NOT oracle-equivalent"),
        "{script}"
    );
    assert!(script.contains(";   datatype sort: Pair"), "{script}");
    assert!(script.contains("(declare-sort Pair 0)"), "{script}");
    // Constructor, selector, and tester applications must all survive the UF
    // weakening as ordinary declared symbols. The weakened script is expected
    // to be SAT (not oracle-equivalent), but it must be a real standalone
    // script accepted by AY's own parser/executor.
    let replay = run_script_collect(&script);
    assert_eq!(replay.last().map(String::as_str), Some("sat"), "{script}");
}
