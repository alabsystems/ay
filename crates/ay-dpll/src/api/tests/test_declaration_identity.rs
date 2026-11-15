// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Declaration-identity and datatype-reincarnation API regressions.

use crate::api::*;
use ay_core::TermData;

/// #reserved-ops (Remediate2): the programmatic API ADOPTS an
/// identical-signature redeclaration of a datatype constructor/selector/
/// tester as a handle to the registered member — the documented embedder
/// contract deductive-checks's encoder relies on (`declare_variant_encoding`
/// re-declares the exact native member names after `try_declare_datatype`).
/// A mismatched signature is rejected by the frontend
/// `DatatypeMemberCollision` gate, which also rejects EVERY textual
/// `declare-fun` of a member name (the rc_forge_tester/rc_forge_selector
/// wrong-UNSAT forgery class).
#[test]
fn test_datatype_member_redeclaration_adopted_or_rejected() {
    let mut solver = Solver::new(Logic::Uf);

    let pt_dt = DatatypeSort {
        name: "PtA".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mk-pta".to_string(),
            fields: vec![DatatypeField {
                name: "pta-x".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    solver.declare_datatype(&pt_dt);
    let carrier = Sort::Datatype(pt_dt.clone());

    // Identical-signature redeclarations: adopted (Ok), exactly the deductive-checks
    // handle pattern. `Sort::Datatype` exercises the as_term_sort mapping to
    // the registered `Sort::Uninterpreted` carrier.
    let ctor = solver
        .try_declare_fun("mk-pta", &[Sort::Int], carrier.clone())
        .expect("identical-signature constructor redeclaration must be adopted");
    let sel = solver
        .try_declare_fun("pta-x", std::slice::from_ref(&carrier), Sort::Int)
        .expect("identical-signature selector redeclaration must be adopted");
    let _tester = solver
        .try_declare_fun("is-mk-pta", std::slice::from_ref(&carrier), Sort::Bool)
        .expect("identical-signature tester redeclaration must be adopted");

    // Mismatched signatures: rejected by the DatatypeMemberCollision gate.
    assert!(
        solver
            .try_declare_fun("pta-x", &[Sort::Int], Sort::Int)
            .is_err(),
        "wrong-signature selector redeclaration must be rejected"
    );
    assert!(
        solver
            .try_declare_fun("is-mk-pta", &[Sort::Int], Sort::Bool)
            .is_err(),
        "wrong-signature tester redeclaration must be rejected"
    );
    assert!(
        solver
            .try_declare_fun("mk-pta", &[Sort::Bool], carrier.clone())
            .is_err(),
        "wrong-signature constructor redeclaration must be rejected"
    );

    // The adopted handles denote the REAL member operations: selector over
    // constructor discharges definitionally (UNSAT on the negation).
    let one = solver.int_const(1);
    let p = solver.apply(&ctor, &[one]);
    let px = solver.apply(&sel, &[p]);
    let eq = solver.eq(px, one);
    let neq = solver.not(eq);
    solver.assert_term(neq);
    assert!(
        solver.check_sat().is_unsat(),
        "adopted selector/constructor handles must carry builtin member semantics"
    );
}

#[test]
fn datatype_member_handles_require_the_exact_live_declaration() {
    let mut solver = Solver::new(Logic::Uf);
    let datatype = DatatypeSort {
        name: "EpochDt".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mk-epoch-dt".to_string(),
            fields: vec![DatatypeField {
                name: "epoch-dt-value".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    let carrier = Sort::Datatype(datatype.clone());
    solver.declare_datatype(&datatype);
    let stale = solver
        .try_declare_fun("mk-epoch-dt", &[Sort::Int], carrier.clone())
        .expect("registered datatype constructor handle");
    let _unrelated = solver.declare_const("unrelated", Sort::Bool);
    let same_declaration = solver
        .try_declare_fun("mk-epoch-dt", &[Sort::Int], carrier.clone())
        .expect("the same datatype declaration remains live after an unrelated revision");
    assert_eq!(stale, same_declaration);

    solver.try_reset().unwrap();
    solver.declare_datatype(&datatype);
    let current = solver
        .try_declare_fun("mk-epoch-dt", &[Sort::Int], carrier.clone())
        .expect("reincarnated datatype constructor handle");
    let forged = FuncDecl::new("mk-epoch-dt".to_string(), vec![Sort::Int], carrier);
    let one = solver.int_const(1);

    assert!(matches!(
        solver.try_apply(&stale, &[one]),
        Err(SolverError::InvalidArgument {
            operation: "apply",
            ..
        })
    ));
    assert!(matches!(
        solver.try_apply(&forged, &[one]),
        Err(SolverError::InvalidArgument {
            operation: "apply",
            ..
        })
    ));
    assert!(solver.try_apply(&current, &[one]).is_ok());
}

#[test]
fn scoped_same_signature_function_reincarnations_do_not_hash_cons() {
    let mut solver = Solver::new(Logic::All);
    solver
        .parse_smtlib2("(declare-const scoped-core-x Int)")
        .expect("declare outer argument");
    solver.push();
    let old_assertions = solver
        .parse_smtlib2(
            "(declare-fun scoped-core-f (Int) Bool) \
             (assert (scoped-core-f scoped-core-x))",
        )
        .expect("declare and retain the old application");
    let old_application = old_assertions[0];
    solver.pop();

    let new_assertions = solver
        .parse_smtlib2(
            "(declare-fun scoped-core-f (Int) Bool) \
             (assert (not (scoped-core-f scoped-core-x)))",
        )
        .expect("declare the new application");
    let TermData::Not(new_application) = solver.terms().get(new_assertions[0].id()) else {
        panic!("new assertion must remain a negated application");
    };
    assert_ne!(
        old_application.id(),
        *new_application,
        "distinct declarations must not hash-cons to one application"
    );

    solver.assert_term(old_application);
    assert!(
        !solver.check_sat().is_unsat(),
        "the retained old application and negated new application are independent"
    );
}

#[test]
fn native_datatype_builders_use_reincarnated_member_core_identities() {
    let datatype = DatatypeSort {
        name: "ScopedNativeDt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "ScopedNativeC".to_string(),
                fields: vec![DatatypeField {
                    name: "scoped-native-field".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "ScopedNativeOther".to_string(),
                fields: Vec::new(),
            },
        ],
    };
    let declaration = "(declare-datatype ScopedNativeDt \
        ((ScopedNativeC (scoped-native-field Int)) (ScopedNativeOther)))";
    let mut solver = Solver::new(Logic::All);
    let one = solver.int_const(1);

    // A selector or tester over a LITERAL constructor application folds away
    // (to the stored field / a Boolean constant) exactly as its surface
    // spelling elaborates, so the member's core identity is only observable on
    // an OPAQUE scrutinee. Each incarnation therefore gets its own constant.
    let true_term = solver.bool_const(true);

    solver.push();
    solver
        .parse_smtlib2(declaration)
        .expect("declare first scoped datatype");
    let old_opaque = solver.declare_const("scoped-native-opaque", Sort::Datatype(datatype.clone()));
    let old_ctor = solver.datatype_constructor(&datatype, "ScopedNativeC", &[one]);
    assert_eq!(
        solver.datatype_selector("scoped-native-field", old_ctor, Sort::Int),
        one,
        "selector over its own constructor folds to the stored field"
    );
    assert_eq!(
        solver.datatype_tester("ScopedNativeC", old_ctor),
        true_term,
        "tester over its own constructor folds to `true`"
    );
    let old_selector = solver.datatype_selector("scoped-native-field", old_opaque, Sort::Int);
    let old_tester = solver.datatype_tester("ScopedNativeC", old_opaque);
    solver.pop();

    solver
        .parse_smtlib2(declaration)
        .expect("declare reincarnated datatype");
    let new_opaque =
        solver.declare_const("scoped-native-opaque-2", Sort::Datatype(datatype.clone()));
    let new_ctor = solver.datatype_constructor(&datatype, "ScopedNativeC", &[one]);
    let new_selector = solver.datatype_selector("scoped-native-field", new_opaque, Sort::Int);
    let new_tester = solver.datatype_tester("ScopedNativeC", new_opaque);

    // The applied symbol is the member's CORE name, so comparing it isolates
    // member identity from the (necessarily distinct) scrutinee constants.
    let applied_core = |solver: &Solver, term: Term, what: &str| match solver.terms().get(term.id())
    {
        TermData::App(symbol, _) => symbol.to_string(),
        other => panic!("{what} must stay an application over an opaque scrutinee, got {other:?}"),
    };

    assert_ne!(old_ctor, new_ctor, "constructor core identity was reused");
    assert_ne!(
        applied_core(&solver, old_selector, "selector"),
        applied_core(&solver, new_selector, "selector"),
        "selector core identity was reused"
    );
    assert_ne!(
        applied_core(&solver, old_tester, "tester"),
        applied_core(&solver, new_tester, "tester"),
        "tester core identity was reused"
    );
    assert!(matches!(
        solver.try_datatype_selector("scoped-native-field", old_ctor, Sort::Int),
        Err(SolverError::SortMismatch { .. })
    ));
    assert!(matches!(
        solver.try_datatype_tester("ScopedNativeC", old_ctor),
        Err(SolverError::SortMismatch { .. })
    ));
}

#[test]
fn retained_datatype_terms_keep_exact_axioms_across_redeclaration() {
    const DECLARATION: &str = "(declare-datatype StickyDt \
        ((StickyC (sticky-field Int)) (StickyOther)))";

    // An assertion retained from the popped declaration still receives that
    // exact declaration's injectivity axiom after a same-surface reincarnation.
    let mut old_unsat = Solver::new(Logic::All);
    old_unsat.push();
    let old_contradiction = old_unsat
        .parse_smtlib2(&format!(
            "{DECLARATION} (assert (= (StickyC 1) (StickyC 2)))"
        ))
        .expect("retain old datatype contradiction")[0];
    old_unsat.pop();
    old_unsat
        .parse_smtlib2(DECLARATION)
        .expect("redeclare same datatype surface");
    old_unsat.assert_term(old_contradiction);
    assert!(old_unsat.check_sat().is_unsat());

    // The current declaration independently keeps its own exact axioms while
    // the popped declaration remains in the sticky semantic registry.
    let mut new_unsat = Solver::new(Logic::All);
    new_unsat.push();
    new_unsat
        .parse_smtlib2(DECLARATION)
        .expect("seed popped declaration epoch");
    new_unsat.pop();
    let new_contradiction = new_unsat
        .parse_smtlib2(&format!(
            "{DECLARATION} (assert (= (StickyC 3) (StickyC 4)))"
        ))
        .expect("build current datatype contradiction")[0];
    new_unsat.assert_term(new_contradiction);
    assert!(new_unsat.check_sat().is_unsat());

    // Control: satisfiable facts about both declaration epochs must remain
    // satisfiable; sticky metadata must not conflate their private carriers or
    // constructor heads.
    let mut sat_control = Solver::new(Logic::All);
    sat_control.push();
    let old_fact = sat_control
        .parse_smtlib2(&format!(
            "{DECLARATION} (assert (distinct (StickyC 1) StickyOther))"
        ))
        .expect("retain satisfiable old datatype fact")[0];
    sat_control.pop();
    let new_fact = sat_control
        .parse_smtlib2(&format!(
            "{DECLARATION} (assert (distinct (StickyC 2) StickyOther))"
        ))
        .expect("build satisfiable current datatype fact")[0];
    sat_control.assert_term(old_fact);
    sat_control.assert_term(new_fact);
    assert_eq!(sat_control.check_sat(), SolveResult::Sat);
}

/// `Solver::declare_const`'s `# Panics` section lists reserved names beside
/// declaration collisions, because the panicking wrapper takes exactly the
/// refusals `try_declare_const` returns. Pin one name from each reserved class
/// the doc names: a builtin theory operator, a declaration-activated collection
/// operator and the internal `__ay_` namespace.
#[test]
fn test_declare_const_refuses_each_documented_reserved_class() {
    for name in ["fp", "int2bv", "set.subset", "__ay_documented"] {
        let mut solver = Solver::new(Logic::QfLia);
        let error = solver
            .try_declare_const(name, Sort::Int)
            .expect_err("a reserved name must be refused");
        assert!(
            error.to_string().contains("reserved"),
            "try_declare_const({name}) must name the reservation, got: {error}"
        );
        let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut solver = Solver::new(Logic::QfLia);
            let _ = solver.declare_const(name, Sort::Int);
        }));
        assert!(
            panicked.is_err(),
            "declare_const({name}) must panic, as its # Panics section documents"
        );
    }
}
