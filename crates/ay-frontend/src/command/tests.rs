// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::sexp::parse_sexp;

#[test]
fn test_parse_set_logic() {
    let sexp = parse_sexp("(set-logic QF_LIA)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::SetLogic("QF_LIA".to_string()));
}

#[test]
fn test_parse_declare_fun() {
    let sexp = parse_sexp("(declare-fun x () Int)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(
        cmd,
        Command::DeclareFun("x".to_string(), vec![], Sort::Simple("Int".to_string()))
    );
}

#[test]
fn test_parse_maximize() {
    let sexp = parse_sexp("(maximize x)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::Maximize(Term::Symbol("x".to_string())));
}

#[test]
fn indexed_identifier_stays_distinct_from_same_spelled_quoted_symbol() {
    let sexp = parse_sexp("(assert (distinct |(_ bv0 8)| (_ bv0 8)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(
        cmd,
        Command::Assert(Term::App(
            "distinct".to_string(),
            vec![
                Term::Symbol("(_ bv0 8)".to_string()),
                Term::IndexedApp(
                    "bv0".to_string(),
                    vec![Index::Numeral("8".to_string())],
                    vec![],
                ),
            ],
        ))
    );
}

#[test]
fn indexed_identifier_preserves_index_token_kinds() {
    let sexp = parse_sexp("(assert (= (_ f 8 #x41) (_ f |8| |#x41|)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    let Command::Assert(Term::App(_, sides)) = &cmd else {
        panic!("expected equality assertion");
    };
    assert!(matches!(
        &sides[0],
        Term::IndexedApp(_, indices, _) if indices == &[
            Index::Numeral("8".to_string()),
            Index::Hexadecimal("#x41".to_string()),
        ]
    ));
    assert!(matches!(
        &sides[1],
        Term::IndexedApp(_, indices, _) if indices == &[
            Index::Symbol("8".to_string()),
            Index::Symbol("#x41".to_string()),
        ]
    ));
}

#[test]
fn qualified_identifier_preserves_symbol_vs_indexed_structure() {
    let sexp =
        parse_sexp("(assert (distinct (as |(_ mystery 1)| Int) (as (_ mystery 1) Int)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    let Command::Assert(Term::App(_, sides)) = &cmd else {
        panic!("expected distinct assertion");
    };
    assert!(matches!(
        &sides[0],
        Term::QualifiedApp(QualifiedIdentifier::Symbol(name), _, _)
            if name == "(_ mystery 1)"
    ));
    assert!(matches!(
        &sides[1],
        Term::QualifiedApp(QualifiedIdentifier::Indexed(name, indices), _, _)
            if name == "mystery"
                && indices == &[Index::Numeral("1".to_string())]
    ));
}

#[test]
fn test_parse_get_objectives() {
    let sexp = parse_sexp("(get-objectives)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::GetObjectives);
}

#[test]
fn test_parse_declare_fun_with_args() {
    let sexp = parse_sexp("(declare-fun f (Int Int) Bool)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(
        cmd,
        Command::DeclareFun(
            "f".to_string(),
            vec![
                Sort::Simple("Int".to_string()),
                Sort::Simple("Int".to_string())
            ],
            Sort::Simple("Bool".to_string())
        )
    );
}

#[test]
fn test_parse_declare_const() {
    let sexp = parse_sexp("(declare-const y Real)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(
        cmd,
        Command::DeclareConst("y".to_string(), Sort::Simple("Real".to_string()))
    );
}

#[test]
fn test_parse_assert() {
    let sexp = parse_sexp("(assert (> x 0))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Assert(Term::App(name, args)) => {
            assert_eq!(name, ">");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("Expected Assert command"),
    }
}

#[test]
fn test_parse_check_sat() {
    let sexp = parse_sexp("(check-sat)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::CheckSat);
}

#[test]
fn test_parse_check_sat_using_simple_tactic() {
    // `(check-sat-using <tactic>)` is the Z3 tactic surface. AY has no tactic
    // engine, so the tactic is a sound-to-ignore search hint: the command maps
    // to a plain `(check-sat)` discharged by the default solver. The verdict is
    // therefore identical to `(check-sat)` and never changed by the hint.
    let sexp = parse_sexp("(check-sat-using qflia)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::CheckSat);
}

#[test]
fn test_parse_check_sat_using_tactic_combinator() {
    // Opaque tactic combinators (then / or-else / par-then / and-then ...) must
    // parse without crashing the script and still route to the default engine.
    let sexp = parse_sexp("(check-sat-using (then simplify smt))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::CheckSat);

    let sexp = parse_sexp("(check-sat-using (or-else (then simplify smt) qfnia))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::CheckSat);
}

#[test]
fn test_check_sat_using_rejects_a_garbage_tactic_name_like_z3() {
    // The honesty fix: `(check-sat-using zzz-not-a-tactic)` must ERROR with
    // z3's byte text (z3 4.15.4: `invalid tactic, unknown tactic
    // zzz-not-a-tactic`, rc=1, script continues) instead of silently deciding.
    let sexp = parse_sexp("(check-sat-using zzz-not-a-tactic)").unwrap();
    let err = Command::from_sexp(&sexp).unwrap_err().to_string();
    assert!(
        err.contains("invalid tactic, unknown tactic zzz-not-a-tactic"),
        "garbage csu tactic must produce z3's unknown-tactic error, got: {err}"
    );
    // Garbage INSIDE a combinator errors identically (shared parser).
    let sexp = parse_sexp("(check-sat-using (then simplify zzz))").unwrap();
    let err = Command::from_sexp(&sexp).unwrap_err().to_string();
    assert!(err.contains("unknown tactic zzz"), "got: {err}");
}

#[test]
fn test_check_sat_using_with_no_argument_errors_like_z3() {
    // z3 4.15.4 byte text (measured): "check-sat-using needs a tactic
    // argument", rc=1, script continues.
    let sexp = parse_sexp("(check-sat-using)").unwrap();
    let err = Command::from_sexp(&sexp).unwrap_err().to_string();
    assert!(
        err.contains("check-sat-using needs a tactic argument"),
        "got: {err}"
    );
}

#[test]
fn test_check_sat_using_rejects_trailing_arguments_like_z3() {
    // z3 rejects trailing args — even keywords (params go INSIDE the tactic,
    // e.g. `(! smt :random-seed 7)`). Both byte texts measured on z3 4.15.4.
    let sexp = parse_sexp("(check-sat-using smt :random-seed 7)").unwrap();
    let err = Command::from_sexp(&sexp).unwrap_err().to_string();
    assert!(err.contains("invalid keyword argument"), "got: {err}");

    let sexp = parse_sexp("(check-sat-using smt extra)").unwrap();
    let err = Command::from_sexp(&sexp).unwrap_err().to_string();
    assert!(
        err.contains("invalid command argument, keyword expected"),
        "got: {err}"
    );
}

#[test]
fn test_check_sat_using_accepts_every_registered_name_and_the_bang_form() {
    // TWIN of the garbage-rejection tests: the strictness fix must reject ONLY
    // unknown names. Every registered z3 name (incl. the batch's qflia/qfbv/
    // diff-neq/fail-if-undecided) stays a valid csu hint discharged by the
    // sound default engine.
    for name in SUPPORTED_TACTIC_NAMES {
        let sexp = parse_sexp(&format!("(check-sat-using {name})")).unwrap();
        assert_eq!(
            Command::from_sexp(&sexp).unwrap_or_else(|e| panic!("{name}: {e}")),
            Command::CheckSat,
            "registered tactic {name:?} must remain a valid csu hint"
        );
    }
    // `(! t :k v)` is valid in csu (z3 c4 probe: unsat twin decides).
    let sexp = parse_sexp("(check-sat-using (! smt :random-seed 7))").unwrap();
    assert_eq!(Command::from_sexp(&sexp).unwrap(), Command::CheckSat);
    // if/cond combinators with a full-registry probe parse in csu position.
    let sexp = parse_sexp("(check-sat-using (if is-unbounded smt qflia))").unwrap();
    assert_eq!(Command::from_sexp(&sexp).unwrap(), Command::CheckSat);
    let sexp = parse_sexp("(check-sat-using (when is-unbounded smt))").unwrap();
    assert_eq!(Command::from_sexp(&sexp).unwrap(), Command::CheckSat);
}

#[test]
fn test_parse_apply_tactic_parses_a_structured_tactic() {
    use crate::command::ApplyTactic;
    // `(apply <tactic>)` now parses into a structured, validated tactic that the
    // executor runs over the current goal — NOT the old constant `Echo` of an
    // empty goal (which was unsound: an empty goal is `true`, trivially SAT). A
    // bare tactic name parses to its primitive.
    let sexp = parse_sexp("(apply simplify)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::Apply(ApplyTactic::Simplify));

    // A `then`/`and-then` combinator parses to a sequence of its children.
    let sexp = parse_sexp("(apply (then simplify propagate-values))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(
        cmd,
        Command::Apply(ApplyTactic::Then(vec![
            ApplyTactic::Simplify,
            ApplyTactic::PropagateValues,
        ]))
    );

    // An unknown tactic is a parse error, like z3 — never a silent empty goal.
    let sexp = parse_sexp("(apply no-such-tactic)").unwrap();
    assert!(Command::from_sexp(&sexp).is_err());
}

#[test]
fn test_parse_assert_soft_default_weight() {
    let sexp = parse_sexp("(assert-soft (not a))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match cmd {
        Command::AssertSoft { term, weight, id } => {
            assert_eq!(
                term,
                Term::App("not".to_string(), vec![Term::Symbol("a".to_string())])
            );
            assert_eq!(weight, 1, "default weight must be 1");
            assert_eq!(id, None);
        }
        other => panic!("Expected AssertSoft, got {other:?}"),
    }
}

#[test]
fn test_parse_assert_soft_weight_and_id() {
    let sexp = parse_sexp("(assert-soft p :weight 7 :id grp)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match cmd {
        Command::AssertSoft { term, weight, id } => {
            assert_eq!(term, Term::Symbol("p".to_string()));
            assert_eq!(weight, 7);
            assert_eq!(id, Some("grp".to_string()));
        }
        other => panic!("Expected AssertSoft, got {other:?}"),
    }
}

#[test]
fn test_parse_assert_soft_attributes_any_order() {
    let sexp = parse_sexp("(assert-soft p :id grp :weight 3)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match cmd {
        Command::AssertSoft { weight, id, .. } => {
            assert_eq!(weight, 3);
            assert_eq!(id, Some("grp".to_string()));
        }
        other => panic!("Expected AssertSoft, got {other:?}"),
    }
}

#[test]
fn test_parse_assert_soft_missing_term_errors() {
    let sexp = parse_sexp("(assert-soft)").unwrap();
    assert!(Command::from_sexp(&sexp).is_err());
}

#[test]
fn test_parse_assert_soft_nonnumeral_weight_errors() {
    let sexp = parse_sexp("(assert-soft p :weight foo)").unwrap();
    assert!(Command::from_sexp(&sexp).is_err());
}

#[test]
fn test_parse_declare_rel() {
    let sexp = parse_sexp("(declare-rel p (Int Bool))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(
        cmd,
        Command::DeclareRel(
            "p".to_string(),
            vec![
                Sort::Simple("Int".to_string()),
                Sort::Simple("Bool".to_string()),
            ],
        )
    );
}

#[test]
fn test_parse_declare_rel_nullary() {
    let sexp = parse_sexp("(declare-rel q ())").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::DeclareRel("q".to_string(), vec![]));
}

#[test]
fn test_parse_rule() {
    let sexp = parse_sexp("(rule (=> (= x 0) (p x)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Rule(Term::App(name, args)) => {
            assert_eq!(name, "=>");
            assert_eq!(args.len(), 2);
        }
        other => panic!("Expected Rule(=> ...), got {other:?}"),
    }
}

#[test]
fn test_parse_query_application() {
    let sexp = parse_sexp("(query (p 5))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Query(Term::App(name, args)) => {
            assert_eq!(name, "p");
            assert_eq!(args.len(), 1);
        }
        other => panic!("Expected Query(p 5), got {other:?}"),
    }
}

#[test]
fn test_parse_query_nullary_symbol() {
    let sexp = parse_sexp("(query goal)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::Query(Term::Symbol("goal".to_string())));
}

#[test]
fn test_parse_declare_rel_rejects_missing_sort_list() {
    // A bare symbol where the argument-sort list is required must be rejected
    // (sound: never silently accept a malformed fixedpoint declaration).
    let sexp = parse_sexp("(declare-rel p Int)").unwrap();
    assert!(Command::from_sexp(&sexp).is_err());
}

#[test]
fn test_parse_rule_rejects_extra_args() {
    let sexp = parse_sexp("(rule (p x) (p y))").unwrap();
    assert!(Command::from_sexp(&sexp).is_err());
}

#[test]
fn test_parse_push_pop() {
    let push = parse_sexp("(push 2)").unwrap();
    assert_eq!(Command::from_sexp(&push).unwrap(), Command::Push(2));

    let pop = parse_sexp("(pop 1)").unwrap();
    assert_eq!(Command::from_sexp(&pop).unwrap(), Command::Pop(1));
}

#[test]
fn test_parse_bitvector_sort() {
    let sexp = parse_sexp("(declare-const bv (_ BitVec 32))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareConst(name, Sort::Indexed(sort_name, indices)) => {
            assert_eq!(name, "bv");
            assert_eq!(sort_name, "BitVec");
            assert_eq!(indices, &vec![Index::Numeral("32".to_string())]);
        }
        _ => panic!("Expected DeclareConst with indexed sort"),
    }
}

#[test]
fn indexed_sort_requires_at_least_one_index() {
    for malformed in ["(_)", "(_ BitVec)", "(_ BitVec 8.0)"] {
        let sexp = parse_sexp(malformed).unwrap();
        assert!(Sort::from_sexp(&sexp).is_err(), "accepted {malformed}");
    }

    let command = parse_sexp("(declare-const bv (_ BitVec))").unwrap();
    assert!(Command::from_sexp(&command).is_err());

    let quoted_index = parse_sexp("(_ BitVec |8|)").unwrap();
    assert_eq!(
        Sort::from_sexp(&quoted_index).unwrap(),
        Sort::Indexed("BitVec".to_string(), vec![Index::Symbol("8".to_string())])
    );
}

#[test]
fn test_parse_array_sort() {
    let sexp = parse_sexp("(declare-const arr (Array Int Int))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareConst(name, Sort::Parameterized(sort_name, params)) => {
            assert_eq!(name, "arr");
            assert_eq!(sort_name, "Array");
            assert_eq!(params.len(), 2);
        }
        _ => panic!("Expected DeclareConst with parameterized sort"),
    }
}

#[test]
fn test_parse_let_term() {
    let sexp = parse_sexp("(assert (let ((x 1)) (+ x 2)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Assert(Term::Let(bindings, _body)) => {
            assert_eq!(bindings.len(), 1);
            assert_eq!(bindings[0].0, "x");
        }
        _ => panic!("Expected Assert with Let term"),
    }
}

#[test]
fn test_parse_forall() {
    let sexp = parse_sexp("(assert (forall ((x Int)) (> x 0)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Assert(Term::Forall(bindings, _body)) => {
            assert_eq!(bindings.len(), 1);
            assert_eq!(bindings[0].0, "x");
        }
        _ => panic!("Expected Assert with Forall term"),
    }
}

#[test]
fn test_parse_exists() {
    let sexp = parse_sexp("(assert (exists ((x Int)) (> x 0)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Assert(Term::Exists(bindings, _body)) => {
            assert_eq!(bindings.len(), 1);
            assert_eq!(bindings[0].0, "x");
        }
        _ => panic!("Expected Assert with Exists term"),
    }
}

#[test]
fn test_parse_nested_quantifiers() {
    let sexp = parse_sexp("(assert (forall ((x Int)) (exists ((y Int)) (= (+ x y) 0))))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Assert(Term::Forall(bindings, body)) => {
            assert_eq!(bindings.len(), 1);
            assert_eq!(bindings[0].0, "x");
            assert!(matches!(body.as_ref(), Term::Exists(_, _)));
        }
        _ => panic!("Expected nested Forall/Exists"),
    }
}

#[test]
fn test_parse_forall_multiple_bindings() {
    let sexp = parse_sexp("(assert (forall ((x Int) (y Int)) (>= (+ x y) 0)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Assert(Term::Forall(bindings, _body)) => {
            assert_eq!(bindings.len(), 2);
            assert_eq!(bindings[0].0, "x");
            assert_eq!(bindings[1].0, "y");
        }
        _ => panic!("Expected Forall with multiple bindings"),
    }
}

#[test]
fn test_parse_define_const_desugars_to_nullary_define_fun() {
    // z3's `(define-const c Int 5)` convenience form == `(define-fun c () Int 5)`.
    let sexp = parse_sexp("(define-const c Int 5)");
    let cmd = Command::from_sexp(&sexp.unwrap()).unwrap();
    match &cmd {
        Command::DefineFun(name, params, ret_sort, _body) => {
            assert_eq!(name, "c");
            assert!(params.is_empty(), "define-const is nullary");
            assert_eq!(ret_sort, &Sort::Simple("Int".to_string()));
        }
        _ => panic!("Expected define-const to desugar to DefineFun, got {cmd:?}"),
    }
}

#[test]
fn test_parse_define_fun_rec() {
    // Factorial function
    let sexp =
        parse_sexp("(define-fun-rec fact ((n Int)) Int (ite (= n 0) 1 (* n (fact (- n 1)))))");
    let cmd = Command::from_sexp(&sexp.unwrap()).unwrap();
    match &cmd {
        Command::DefineFunRec(name, params, ret_sort, _body) => {
            assert_eq!(name, "fact");
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].0, "n");
            assert_eq!(ret_sort, &Sort::Simple("Int".to_string()));
        }
        _ => panic!("Expected DefineFunRec command"),
    }
}

#[test]
fn test_parse_define_fun_rec_multiple_params() {
    let sexp =
        parse_sexp("(define-fun-rec gcd ((a Int) (b Int)) Int (ite (= b 0) a (gcd b (mod a b))))");
    let cmd = Command::from_sexp(&sexp.unwrap()).unwrap();
    match &cmd {
        Command::DefineFunRec(name, params, ret_sort, _body) => {
            assert_eq!(name, "gcd");
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].0, "a");
            assert_eq!(params[1].0, "b");
            assert_eq!(ret_sort, &Sort::Simple("Int".to_string()));
        }
        _ => panic!("Expected DefineFunRec command"),
    }
}

#[test]
fn test_parse_define_funs_rec() {
    // Mutually recursive even/odd functions
    let sexp = parse_sexp(
        "(define-funs-rec ((even ((n Int)) Bool) (odd ((n Int)) Bool)) \
         ((ite (= n 0) true (odd (- n 1))) (ite (= n 0) false (even (- n 1)))))",
    );
    let cmd = Command::from_sexp(&sexp.unwrap()).unwrap();
    match &cmd {
        Command::DefineFunsRec(declarations, bodies) => {
            assert_eq!(declarations.len(), 2);
            assert_eq!(bodies.len(), 2);

            // Check first declaration (even)
            assert_eq!(declarations[0].0, "even");
            assert_eq!(declarations[0].1.len(), 1);
            assert_eq!(declarations[0].1[0].0, "n");
            assert_eq!(declarations[0].2, Sort::Simple("Bool".to_string()));

            // Check second declaration (odd)
            assert_eq!(declarations[1].0, "odd");
            assert_eq!(declarations[1].1.len(), 1);
            assert_eq!(declarations[1].1[0].0, "n");
            assert_eq!(declarations[1].2, Sort::Simple("Bool".to_string()));
        }
        _ => panic!("Expected DefineFunsRec command"),
    }
}

#[test]
fn test_parse_define_funs_rec_mismatch_error() {
    // Mismatched number of declarations and bodies
    let sexp = parse_sexp("(define-funs-rec ((f ((x Int)) Int)) (body1 body2))");
    let result = Command::from_sexp(&sexp.unwrap());
    assert!(result.is_err());
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("number of declarations must match"));
}

#[test]
fn test_parse_sygus_synth_fun_with_grammar() {
    let sexp = parse_sexp(
        "(synth-fun max2 ((x Int) (y Int)) Int \
         ((Start Int (x y 0 1 (+ Start Start) (ite StartBool Start Start))) \
          (StartBool Bool ((<= Start Start)))))",
    )
    .unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::SynthFun(name, params, ret_sort, grammar) => {
            assert_eq!(name, "max2");
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].0, "x");
            assert_eq!(params[1].0, "y");
            assert_eq!(ret_sort, &Sort::Simple("Int".to_string()));

            let grammar = grammar.as_ref().expect("grammar should parse");
            assert_eq!(grammar.nonterminals.len(), 2);
            assert_eq!(grammar.nonterminals[0].name, "Start");
            assert_eq!(
                grammar.nonterminals[0].sort,
                Sort::Simple("Int".to_string())
            );
            assert_eq!(grammar.nonterminals[0].expansions.len(), 6);
            assert_eq!(grammar.nonterminals[1].name, "StartBool");
            assert_eq!(
                grammar.nonterminals[1].sort,
                Sort::Simple("Bool".to_string())
            );
        }
        _ => panic!("Expected SynthFun command"),
    }
}

#[test]
fn test_parse_sygus_commands_without_grammar() {
    let declare_var = parse_sexp("(declare-var x Int)").unwrap();
    assert_eq!(
        Command::from_sexp(&declare_var).unwrap(),
        Command::DeclareVar("x".to_string(), Sort::Simple("Int".to_string()))
    );

    let synth_inv = parse_sexp("(synth-inv inv ((x Int) (y Int)))").unwrap();
    match Command::from_sexp(&synth_inv).unwrap() {
        Command::SynthInv(name, params, grammar) => {
            assert_eq!(name, "inv");
            assert_eq!(params.len(), 2);
            assert!(grammar.is_none());
        }
        _ => panic!("Expected SynthInv command"),
    }

    let constraint = parse_sexp("(constraint (= (f x) (+ x 1)))").unwrap();
    let cmd = Command::from_sexp(&constraint).unwrap();
    match &cmd {
        Command::SygusConstraint(Term::App(name, args)) => {
            assert_eq!(name, "=");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("Expected SyGuS constraint command"),
    }

    let inv_constraint = parse_sexp("(inv-constraint inv pre trans post)").unwrap();
    assert_eq!(
        Command::from_sexp(&inv_constraint).unwrap(),
        Command::InvConstraint(
            "inv".to_string(),
            "pre".to_string(),
            "trans".to_string(),
            "post".to_string()
        )
    );

    let check_synth = parse_sexp("(check-synth)").unwrap();
    assert_eq!(
        Command::from_sexp(&check_synth).unwrap(),
        Command::CheckSynth
    );
}

#[test]
fn test_parse_sygus_empty_grammar_error() {
    let sexp = parse_sexp("(synth-fun f ((x Int)) Int ())").unwrap();
    let result = Command::from_sexp(&sexp);
    assert!(result.is_err());
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("grammar requires nonterminals"));
}

#[test]
fn test_parse_declare_datatype_simple() {
    // Simple enumeration type
    let sexp = parse_sexp("(declare-datatype Color ((Red) (Green) (Blue)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareDatatype(name, datatype_dec) => {
            assert_eq!(name, "Color");
            assert_eq!(datatype_dec.constructors.len(), 3);
            assert_eq!(datatype_dec.constructors[0].name, "Red");
            assert_eq!(datatype_dec.constructors[0].selectors.len(), 0);
            assert_eq!(datatype_dec.constructors[1].name, "Green");
            assert_eq!(datatype_dec.constructors[2].name, "Blue");
        }
        _ => panic!("Expected DeclareDatatype command"),
    }
}

#[test]
fn test_parse_declare_datatype_with_selectors() {
    // Record type with selectors
    let sexp = parse_sexp("(declare-datatype Point ((mk-point (x Int) (y Int))))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareDatatype(name, datatype_dec) => {
            assert_eq!(name, "Point");
            assert_eq!(datatype_dec.constructors.len(), 1);
            assert_eq!(datatype_dec.constructors[0].name, "mk-point");
            assert_eq!(datatype_dec.constructors[0].selectors.len(), 2);
            assert_eq!(datatype_dec.constructors[0].selectors[0].name, "x");
            assert_eq!(
                datatype_dec.constructors[0].selectors[0].sort,
                Sort::Simple("Int".to_string())
            );
            assert_eq!(datatype_dec.constructors[0].selectors[1].name, "y");
        }
        _ => panic!("Expected DeclareDatatype command"),
    }
}

#[test]
fn test_parse_parametric_datatype_par() {
    // Parametric datatype: (par (T U) (<ctor>+)) must parse with the type
    // parameters captured and the selector sorts mentioning them verbatim.
    let sexp =
        parse_sexp("(declare-datatypes ((Pair 2)) ((par (T U) ((mk (fst T) (snd U))))))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareDatatypes(sort_decs, datatype_decs) => {
            assert_eq!(sort_decs.len(), 1);
            assert_eq!(sort_decs[0].name, "Pair");
            assert_eq!(sort_decs[0].arity, 2);
            assert_eq!(datatype_decs.len(), 1);
            assert_eq!(datatype_decs[0].type_params, vec!["T", "U"]);
            assert_eq!(datatype_decs[0].constructors.len(), 1);
            assert_eq!(datatype_decs[0].constructors[0].name, "mk");
            assert_eq!(
                datatype_decs[0].constructors[0].selectors[0].sort,
                Sort::Simple("T".to_string())
            );
            assert_eq!(
                datatype_decs[0].constructors[0].selectors[1].sort,
                Sort::Simple("U".to_string())
            );
        }
        _ => panic!("Expected DeclareDatatypes command"),
    }
}

#[test]
fn test_parse_parametric_datatype_singular_par() {
    // Singular `declare-datatype` form with a `par` body.
    let sexp = parse_sexp("(declare-datatype Box (par (T) ((box (unbox T)))))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareDatatype(name, datatype_dec) => {
            assert_eq!(name, "Box");
            assert_eq!(datatype_dec.type_params, vec!["T"]);
            assert_eq!(datatype_dec.constructors.len(), 1);
            assert_eq!(datatype_dec.constructors[0].name, "box");
            assert_eq!(datatype_dec.constructors[0].selectors[0].name, "unbox");
        }
        _ => panic!("Expected DeclareDatatype command"),
    }
}

#[test]
fn test_parse_declare_datatype_multiple_constructors() {
    // Option-like type
    let sexp = parse_sexp("(declare-datatype Option ((None) (Some (value Int))))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareDatatype(name, datatype_dec) => {
            assert_eq!(name, "Option");
            assert_eq!(datatype_dec.constructors.len(), 2);
            assert_eq!(datatype_dec.constructors[0].name, "None");
            assert_eq!(datatype_dec.constructors[0].selectors.len(), 0);
            assert_eq!(datatype_dec.constructors[1].name, "Some");
            assert_eq!(datatype_dec.constructors[1].selectors.len(), 1);
            assert_eq!(datatype_dec.constructors[1].selectors[0].name, "value");
        }
        _ => panic!("Expected DeclareDatatype command"),
    }
}

#[test]
fn test_parse_declare_datatypes() {
    // Multiple datatypes (potentially mutually recursive)
    let sexp = parse_sexp(
        "(declare-datatypes ((Tree 0) (Forest 0)) \
         (((leaf (val Int)) (node (children Forest))) ((nil) (cons (head Tree) (tail Forest)))))",
    )
    .unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareDatatypes(sort_decs, datatype_decs) => {
            assert_eq!(sort_decs.len(), 2);
            assert_eq!(datatype_decs.len(), 2);

            // Check sort declarations
            assert_eq!(sort_decs[0].name, "Tree");
            assert_eq!(sort_decs[0].arity, 0);
            assert_eq!(sort_decs[1].name, "Forest");
            assert_eq!(sort_decs[1].arity, 0);

            // Check Tree constructors
            assert_eq!(datatype_decs[0].constructors.len(), 2);
            assert_eq!(datatype_decs[0].constructors[0].name, "leaf");
            assert_eq!(datatype_decs[0].constructors[1].name, "node");

            // Check Forest constructors
            assert_eq!(datatype_decs[1].constructors.len(), 2);
            assert_eq!(datatype_decs[1].constructors[0].name, "nil");
            assert_eq!(datatype_decs[1].constructors[1].name, "cons");
        }
        _ => panic!("Expected DeclareDatatypes command"),
    }
}

#[test]
fn test_parse_declare_datatypes_mismatch_error() {
    // Mismatched number of sort declarations and datatype declarations
    let sexp = parse_sexp("(declare-datatypes ((T 0)) (((a)) ((b))))");
    let result = Command::from_sexp(&sexp.unwrap());
    assert!(result.is_err());
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("number of sort declarations must match"));
}

#[test]
fn test_parse_declare_datatype_bare_symbol_constructors() {
    // z3 accepts a bare symbol as a nullary constructor (`red` == `(red)`), and
    // mixed with list constructors carrying selectors.
    let sexp = parse_sexp("(declare-datatype Maybe (nothing (just (val Int))))").unwrap();
    match Command::from_sexp(&sexp).unwrap() {
        Command::DeclareDatatype(name, dec) => {
            assert_eq!(name, "Maybe");
            assert_eq!(dec.constructors.len(), 2);
            assert_eq!(dec.constructors[0].name, "nothing");
            assert!(dec.constructors[0].selectors.is_empty());
            assert_eq!(dec.constructors[1].name, "just");
            assert_eq!(dec.constructors[1].selectors.len(), 1);
            assert_eq!(dec.constructors[1].selectors[0].name, "val");
        }
        other => panic!("expected DeclareDatatype, got {other:?}"),
    }
}

#[test]
fn test_parse_declare_datatypes_legacy_pre26_syntax() {
    // Legacy pre-2.6 form: empty parameter list, each datatype entry carries its
    // own name `(Name <ctor>+)`. Must rewrite to the modern arity-0 shape (z3
    // still accepts this). Two datatypes, one an enum and one recursive.
    let sexp = parse_sexp(
        "(declare-datatypes () ((Color (red) (green)) \
         (Lst (nil) (cons (hd Int) (tl Lst)))))",
    )
    .unwrap();
    match Command::from_sexp(&sexp).unwrap() {
        Command::DeclareDatatypes(sort_decs, datatype_decs) => {
            assert_eq!(sort_decs.len(), 2);
            assert_eq!(datatype_decs.len(), 2);
            assert_eq!(sort_decs[0].name, "Color");
            assert_eq!(sort_decs[0].arity, 0);
            assert_eq!(sort_decs[1].name, "Lst");
            assert_eq!(sort_decs[1].arity, 0);
            assert_eq!(datatype_decs[0].constructors.len(), 2);
            assert_eq!(datatype_decs[0].constructors[0].name, "red");
            assert_eq!(datatype_decs[0].constructors[1].name, "green");
            assert_eq!(datatype_decs[1].constructors.len(), 2);
            assert_eq!(datatype_decs[1].constructors[1].name, "cons");
            assert_eq!(datatype_decs[1].constructors[1].selectors[0].name, "hd");
        }
        other => panic!("expected DeclareDatatypes, got {other:?}"),
    }
}

#[test]
fn test_parse_simplify_basic() {
    let sexp = parse_sexp("(simplify (and true x))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Simplify(Term::App(name, args)) => {
            assert_eq!(name, "and");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("Expected Simplify command"),
    }
}

#[test]
fn test_parse_simplify_constant() {
    let sexp = parse_sexp("(simplify true)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Simplify(Term::Const(Constant::True)) => {}
        _ => panic!("Expected Simplify command with true constant"),
    }
}

#[test]
fn test_parse_simplify_arithmetic() {
    let sexp = parse_sexp("(simplify (+ 1 2))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Simplify(Term::App(name, args)) => {
            assert_eq!(name, "+");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("Expected Simplify command"),
    }
}

#[test]
fn test_parse_get_interpolant() {
    let sexp = parse_sexp("(get-interpolant (and (<= x 0)) (and (>= x 1)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::GetInterpolant(Term::App(a, _), Term::App(b, _)) => {
            assert_eq!(a, "and");
            assert_eq!(b, "and");
        }
        _ => panic!("Expected GetInterpolant command, got {cmd:?}"),
    }
}

#[test]
fn test_parse_compute_interpolant() {
    let sexp = parse_sexp("(compute-interpolant (<= x 0) (>= x 1))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::ComputeInterpolant(Term::App(a, _), Term::App(b, _)) => {
            assert_eq!(a, "<=");
            assert_eq!(b, ">=");
        }
        _ => panic!("Expected ComputeInterpolant command, got {cmd:?}"),
    }
}

#[test]
fn test_parse_get_interpolant_wrong_arity_errors() {
    // Missing second argument.
    let sexp = parse_sexp("(get-interpolant (<= x 0))").unwrap();
    assert!(Command::from_sexp(&sexp).is_err());
    // Extra argument.
    let sexp = parse_sexp("(get-interpolant a b c)").unwrap();
    assert!(Command::from_sexp(&sexp).is_err());
}

#[test]
fn test_parse_get_abduct() {
    let sexp = parse_sexp("(get-abduct a (> x 5))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::GetAbduct(name, Term::App(op, _)) => {
            assert_eq!(name, "a");
            assert_eq!(op, ">");
        }
        _ => panic!("Expected GetAbduct command, got {cmd:?}"),
    }
}

#[test]
fn test_parse_get_abduct_with_grammar_is_ignored() {
    // The optional grammar argument is accepted for surface compatibility but
    // does not change the parsed command shape.
    let sexp = parse_sexp("(get-abduct a (> x 5) ((Start Bool ((> x 5)))))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::GetAbduct(name, _) => assert_eq!(name, "a"),
        _ => panic!("Expected GetAbduct command, got {cmd:?}"),
    }
}

#[test]
fn test_parse_get_abduct_wrong_arity_errors() {
    // Missing goal.
    let sexp = parse_sexp("(get-abduct a)").unwrap();
    assert!(Command::from_sexp(&sexp).is_err());
    // Missing both name and goal.
    let sexp = parse_sexp("(get-abduct)").unwrap();
    assert!(Command::from_sexp(&sexp).is_err());
}

// === Deep-nesting stress tests for Term::Drop (#3697) ===
//
// Term::Drop uses iterative drain to avoid stack overflow.
// These tests construct deeply nested Term trees and drop them,
// verifying that the iterative Drop doesn't crash or overflow.

/// Build a deeply nested App chain: (not (not (not ... (not true) ...)))
fn build_deep_app_chain(depth: usize) -> Term {
    let mut term = Term::Const(Constant::True);
    for _ in 0..depth {
        term = Term::App("not".to_string(), vec![term]);
    }
    term
}

#[test]
fn test_term_deep_app_drop_10000() {
    // 10,000-deep App nesting — would overflow with recursive Drop
    let term = build_deep_app_chain(10_000);
    drop(term); // must not stack overflow
}

#[test]
fn test_term_deep_app_drop_100000() {
    // 100,000-deep App nesting — stress test for iterative Drop
    let term = build_deep_app_chain(100_000);
    drop(term);
}

#[test]
fn test_term_deep_let_drop_10000() {
    // 10,000-deep Let nesting: (let ((x true)) (let ((x true)) ...))
    let mut term = Term::Const(Constant::True);
    for i in 0..10_000 {
        let binding = (format!("x{i}"), Term::Const(Constant::False));
        term = Term::Let(vec![binding], Box::new(term));
    }
    drop(term);
}

#[test]
fn test_term_deep_forall_exists_drop_10000() {
    // 5,000 alternating Forall/Exists nesting
    let mut term = Term::Const(Constant::True);
    for i in 0..5_000 {
        let var = (format!("x{i}"), Sort::Simple("Int".to_string()));
        if i % 2 == 0 {
            term = Term::Forall(vec![var], Box::new(term));
        } else {
            term = Term::Exists(vec![var], Box::new(term));
        }
    }
    drop(term);
}

#[test]
fn test_term_deep_annotated_drop_10000() {
    // 10,000-deep Annotated nesting: (! (! (! ... true :named a) :named b) ...)
    let mut term = Term::Const(Constant::True);
    for i in 0..10_000 {
        let attr = (format!("named{i}"), SExpr::Symbol("a".to_string()));
        term = Term::Annotated(Box::new(term), vec![attr]);
    }
    drop(term);
}

#[test]
fn test_term_deep_mixed_nesting_drop() {
    // Mixed nesting: App → Let → Forall → Annotated → App → ...
    let mut term = Term::Const(Constant::True);
    for i in 0..2_500 {
        match i % 4 {
            0 => {
                term = Term::App("f".to_string(), vec![term]);
            }
            1 => {
                let binding = (format!("v{i}"), Term::Const(Constant::False));
                term = Term::Let(vec![binding], Box::new(term));
            }
            2 => {
                let var = (format!("x{i}"), Sort::Simple("Bool".to_string()));
                term = Term::Forall(vec![var], Box::new(term));
            }
            _ => {
                let attr = ("named".to_string(), SExpr::Symbol("a".to_string()));
                term = Term::Annotated(Box::new(term), vec![attr]);
            }
        }
    }
    drop(term); // 10,000 total nesting depth
}

#[test]
fn test_term_deep_app_small_stack() {
    // Run on a restricted 128KB stack to verify iterative Drop works
    // even when the default thread stack is unavailable.
    let result = std::thread::Builder::new()
        .stack_size(128 * 1024) // 128KB — far too small for 10K recursive drops
        .spawn(|| {
            let term = build_deep_app_chain(10_000);
            drop(term);
        })
        .unwrap()
        .join();
    assert!(
        result.is_ok(),
        "iterative Drop must not overflow on 128KB stack"
    );
}
