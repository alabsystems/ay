// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_declare_datatype_simple() {
    let mut ctx = Context::new();

    let script = "(declare-datatype Color ((Red) (Green) (Blue)))";
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    assert!(ctx.sort_defs.contains_key("Color"));

    let red = ctx.symbols.get("Red").expect("Red constructor not found");
    assert!(red.arg_sorts.is_empty());
    assert!(red.term.is_some());

    let green = ctx
        .symbols
        .get("Green")
        .expect("Green constructor not found");
    assert!(green.arg_sorts.is_empty());

    let blue = ctx.symbols.get("Blue").expect("Blue constructor not found");
    assert!(blue.arg_sorts.is_empty());

    let is_red = ctx.symbols.get("is-Red").expect("is-Red tester not found");
    assert_eq!(is_red.arg_sorts.len(), 1);
    assert_eq!(is_red.sort, Sort::Bool);

    let is_green = ctx
        .symbols
        .get("is-Green")
        .expect("is-Green tester not found");
    assert_eq!(is_green.arg_sorts.len(), 1);
    assert_eq!(is_green.sort, Sort::Bool);
}

#[test]
fn test_declare_datatype_with_selectors() {
    let mut ctx = Context::new();

    let script = "(declare-datatype Point ((mk-point (x Int) (y Int))))";
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    assert!(ctx.sort_defs.contains_key("Point"));

    let mk_point = ctx
        .symbols
        .get("mk-point")
        .expect("mk-point constructor not found");
    assert_eq!(mk_point.arg_sorts.len(), 2);
    assert_eq!(mk_point.arg_sorts[0], Sort::Int);
    assert_eq!(mk_point.arg_sorts[1], Sort::Int);
    assert!(mk_point.term.is_none());

    let sel_x = ctx.symbols.get("x").expect("x selector not found");
    assert_eq!(sel_x.arg_sorts.len(), 1);
    assert_eq!(sel_x.sort, Sort::Int);

    let sel_y = ctx.symbols.get("y").expect("y selector not found");
    assert_eq!(sel_y.arg_sorts.len(), 1);
    assert_eq!(sel_y.sort, Sort::Int);

    let is_mk_point = ctx
        .symbols
        .get("is-mk-point")
        .expect("is-mk-point tester not found");
    assert_eq!(is_mk_point.arg_sorts.len(), 1);
    assert_eq!(is_mk_point.sort, Sort::Bool);
}

#[test]
fn test_declare_datatypes_mutually_recursive() {
    let mut ctx = Context::new();

    let script = r#"(declare-datatypes ((Tree 0) (Forest 0))
                        (((leaf (val Int)) (node (children Forest)))
                         ((nil) (cons (head Tree) (tail Forest)))))"#;
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    assert!(ctx.sort_defs.contains_key("Tree"));
    assert!(ctx.sort_defs.contains_key("Forest"));

    let leaf = ctx.symbols.get("leaf").expect("leaf constructor not found");
    assert_eq!(leaf.arg_sorts.len(), 1);
    assert_eq!(leaf.arg_sorts[0], Sort::Int);

    let node = ctx.symbols.get("node").expect("node constructor not found");
    assert_eq!(node.arg_sorts.len(), 1);
    assert_eq!(node.arg_sorts[0], Sort::Uninterpreted("Forest".to_string()));

    let nil = ctx.symbols.get("nil").expect("nil constructor not found");
    assert!(nil.arg_sorts.is_empty());
    assert!(nil.term.is_some());

    let cons = ctx.symbols.get("cons").expect("cons constructor not found");
    assert_eq!(cons.arg_sorts.len(), 2);
    assert_eq!(cons.arg_sorts[0], Sort::Uninterpreted("Tree".to_string()));
    assert_eq!(cons.arg_sorts[1], Sort::Uninterpreted("Forest".to_string()));

    let head = ctx.symbols.get("head").expect("head selector not found");
    assert_eq!(head.sort, Sort::Uninterpreted("Tree".to_string()));

    let tail = ctx.symbols.get("tail").expect("tail selector not found");
    assert_eq!(tail.sort, Sort::Uninterpreted("Forest".to_string()));
}

#[test]
fn test_declare_datatype_can_use_in_terms() {
    let mut ctx = Context::new();

    let script = r#"
            (declare-datatype Option ((None) (Some (value Int))))
            (declare-const x Option)
            (assert (is-Some x))
        "#;
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

/// Test for #1190: SMT-LIB standard datatype tester syntax ((_ is Ctor) x)
/// This is the standard form; ay registers testers as "is-Ctor" internally.
#[test]
fn test_datatype_tester_standard_syntax_1190() {
    let mut ctx = Context::new();

    let script = r#"
            (declare-datatype Option ((None) (Some (value Int))))
            (declare-const x Option)
            (assert ((_ is Some) x))
        "#;
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_datatype_overloaded_selectors_resolve_by_argument_sort() {
    let mut ctx = Context::new();

    let script = r#"
            (declare-datatype Inner ((Inner_mk (fld_0 (_ BitVec 8)) (fld_1 Bool))))
            (declare-datatype Outer ((Outer_mk (fld_0 Inner) (fld_1 (_ BitVec 8)))))
            (assert (= (concat (fld_0 (fld_0 (Outer_mk (Inner_mk #x2a true) #x07))) #x07) #x2a07))
        "#;
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    assert_eq!(*ctx.terms.sort(ctx.assertions[0]), Sort::Bool);
}

/// Test for #1729: datatype_iter() and is_constructor() accessor methods
#[test]
fn test_datatype_iter_and_is_constructor() {
    let mut ctx = Context::new();

    // Declare Color enum and Option type
    let script = r#"
            (declare-datatype Color ((Red) (Green) (Blue)))
            (declare-datatype Option ((None) (Some (value Int))))
        "#;
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    // Test datatype_iter: should yield both datatypes
    let datatypes: Vec<_> = ctx.datatype_iter().collect();
    assert_eq!(datatypes.len(), 2);

    // Check Color constructors
    let color_entry = datatypes.iter().find(|(name, _)| *name == "Color");
    assert!(color_entry.is_some());
    let (_, color_ctors) = color_entry.unwrap();
    assert_eq!(color_ctors.len(), 3);
    assert!(color_ctors.contains(&"Red".to_string()));
    assert!(color_ctors.contains(&"Green".to_string()));
    assert!(color_ctors.contains(&"Blue".to_string()));

    // Check Option constructors
    let option_entry = datatypes.iter().find(|(name, _)| *name == "Option");
    assert!(option_entry.is_some());
    let (_, option_ctors) = option_entry.unwrap();
    assert_eq!(option_ctors.len(), 2);
    assert!(option_ctors.contains(&"None".to_string()));
    assert!(option_ctors.contains(&"Some".to_string()));

    // Test is_constructor: constructors return Some((dt_name, ctor_name))
    assert_eq!(
        ctx.is_constructor("Red"),
        Some(("Color".to_string(), "Red".to_string()))
    );
    assert_eq!(
        ctx.is_constructor("Some"),
        Some(("Option".to_string(), "Some".to_string()))
    );

    // Non-constructors return None
    assert_eq!(ctx.is_constructor("NotAConstructor"), None);
    assert_eq!(ctx.is_constructor("value"), None); // selector, not constructor
}

/// Test push/pop correctly scopes datatypes and constructors
#[test]
fn test_datatype_push_pop_scoping() {
    let mut ctx = Context::new();

    // Declare Color at top level
    let script1 = "(declare-datatype Color ((Red) (Green) (Blue)))";
    for cmd in parse(script1).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    // Verify Color is visible
    assert_eq!(ctx.datatype_iter().count(), 1);
    assert!(ctx.is_constructor("Red").is_some());

    // Push a scope and declare Option inside it
    ctx.push();
    let script2 = "(declare-datatype Option ((None) (Some (value Int))))";
    for cmd in parse(script2).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    // Both datatypes should be visible
    assert_eq!(ctx.datatype_iter().count(), 2);
    assert!(ctx.is_constructor("Red").is_some());
    assert!(ctx.is_constructor("None").is_some());
    assert!(ctx.is_constructor("Some").is_some());

    // Pop the scope
    assert!(ctx.pop(), "pop should succeed after push");

    // Only Color should remain, Option and its constructors should be gone
    assert_eq!(ctx.datatype_iter().count(), 1);
    assert!(ctx.is_constructor("Red").is_some());
    assert!(ctx.is_constructor("None").is_none());
    assert!(ctx.is_constructor("Some").is_none());

    // Verify symbols are also scoped (constructors, selectors, testers)
    assert!(ctx.symbols.contains_key("Red")); // Color constructor still exists
    assert!(ctx.symbols.contains_key("is-Red")); // Color tester still exists
    assert!(!ctx.symbols.contains_key("None")); // Option constructor gone
    assert!(!ctx.symbols.contains_key("Some")); // Option constructor gone
    assert!(!ctx.symbols.contains_key("value")); // Option selector gone
    assert!(!ctx.symbols.contains_key("is-None")); // Option tester gone
    assert!(!ctx.symbols.contains_key("is-Some")); // Option tester gone

    // Verify sort_defs are also scoped
    assert!(ctx.sort_defs.contains_key("Color")); // Color sort still exists
    assert!(!ctx.sort_defs.contains_key("Option")); // Option sort gone
}

/// Test datatype_iter and is_constructor work with declare-datatypes (mutually recursive)
#[test]
fn test_datatype_iter_with_declare_datatypes() {
    let mut ctx = Context::new();

    // Declare mutually recursive Tree/Forest types
    let script = r#"(declare-datatypes ((Tree 0) (Forest 0))
                        (((leaf (val Int)) (node (children Forest)))
                         ((nil) (cons (head Tree) (tail Forest)))))"#;
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    // Test datatype_iter: should yield both datatypes
    let datatypes: Vec<_> = ctx.datatype_iter().collect();
    assert_eq!(datatypes.len(), 2);

    // Check Tree exists with correct constructors
    let tree_entry = datatypes.iter().find(|(name, _)| *name == "Tree");
    assert!(tree_entry.is_some());
    let (_, tree_ctors) = tree_entry.unwrap();
    assert_eq!(tree_ctors.len(), 2);
    assert!(tree_ctors.contains(&"leaf".to_string()));
    assert!(tree_ctors.contains(&"node".to_string()));

    // Check Forest exists with correct constructors
    let forest_entry = datatypes.iter().find(|(name, _)| *name == "Forest");
    assert!(forest_entry.is_some());
    let (_, forest_ctors) = forest_entry.unwrap();
    assert_eq!(forest_ctors.len(), 2);
    assert!(forest_ctors.contains(&"nil".to_string()));
    assert!(forest_ctors.contains(&"cons".to_string()));

    // Test is_constructor works for mutually recursive constructors
    assert_eq!(
        ctx.is_constructor("leaf"),
        Some(("Tree".to_string(), "leaf".to_string()))
    );
    assert_eq!(
        ctx.is_constructor("cons"),
        Some(("Forest".to_string(), "cons".to_string()))
    );
}

#[test]
fn test_parametric_datatype_parses_without_error() {
    // The `(par ...)` surface form must elaborate (no hard parse/elaborate
    // error). The template itself is not a concrete sort yet.
    let mut ctx = Context::new();
    let script = "(declare-datatypes ((Pair 2)) ((par (T U) ((mk (fst T) (snd U))))))";
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd)
            .expect("par template should elaborate");
    }
    assert!(ctx.is_parametric_datatype("Pair"));
    // Not registered as a concrete sort/datatype until instantiated.
    assert!(!ctx.sort_defs.contains_key("Pair"));
    assert!(!ctx.datatypes.contains_key("Pair"));
}

#[test]
fn test_parametric_datatype_monomorphizes_on_use() {
    // Using `(Pair Int Bool)` must instantiate a concrete datatype whose
    // selector sorts are the substituted concrete sorts.
    let mut ctx = Context::new();
    let script = "(declare-datatypes ((Pair 2)) ((par (T U) ((mk (fst T) (snd U))))))\
                  (declare-const p (Pair Int Bool))";
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd)
            .expect("monomorphic use should elaborate");
    }

    // The instance constructor is overload-registered; resolved by arg sort.
    let mk = ctx
        .symbols
        .get("mk")
        .expect("mk constructor not registered");
    assert_eq!(mk.arg_sorts.len(), 2);
    assert_eq!(mk.arg_sorts[0], Sort::Int);
    assert_eq!(mk.arg_sorts[1], Sort::Bool);

    // Selector return sorts follow the substitution: fst : Int, snd : Bool.
    let fst = ctx.symbols.get("fst").expect("fst selector not registered");
    assert_eq!(fst.sort, Sort::Int);
    let snd = ctx.symbols.get("snd").expect("snd selector not registered");
    assert_eq!(snd.sort, Sort::Bool);

    // `mk` maps to the concrete instance datatype under its INSTANCE-MANGLED
    // internal name (per-instance constructor mangling, b30b7353d9); the bare
    // surface name is resolved by argument/result sort at application sites,
    // not through the name-keyed constructor map.
    let (dt, ctor) = ctx
        .is_constructor("mk@Pair!{Int}!{Bool}")
        .expect("mangled mk -> datatype mapping");
    assert_eq!(ctor, "mk@Pair!{Int}!{Bool}");
    assert_eq!(dt, "Pair!{Int}!{Bool}");
    assert!(ctx.datatypes.contains_key(&dt));
}

#[test]
fn test_parametric_datatype_distinct_instances_coexist() {
    // Two instantiations of one template at different type arguments used to
    // collide on the shared surface constructor name `mk` (the pre-mangling
    // design had to fail closed here). Per-instance internal-name mangling
    // (b30b7353d9) root-fixed the collision: both instances must elaborate,
    // each as its own concrete datatype with correctly substituted selector
    // sorts.
    let mut ctx = Context::new();
    let script = "(declare-datatypes ((Pair 2)) ((par (T U) ((mk (fst T) (snd U))))))\
                  (declare-const a (Pair Int Int))\
                  (declare-const b (Pair Bool Bool))";
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd)
            .expect("distinct parametric instances must both elaborate");
    }
    for (inst, field_sort) in [
        ("Pair!{Int}!{Int}", Sort::Int),
        ("Pair!{Bool}!{Bool}", Sort::Bool),
    ] {
        assert!(ctx.datatypes.contains_key(inst), "{inst} not registered");
        let mangled_ctor = format!("mk@{inst}");
        let (dt, _) = ctx
            .is_constructor(&mangled_ctor)
            .expect("instance constructor registered under its mangled name");
        assert_eq!(dt, inst);
        let info = ctx
            .constructor_selector_info(&mangled_ctor)
            .expect("instance selector info registered");
        assert_eq!(info.len(), 2);
        assert!(
            info.iter().all(|(_, s)| *s == field_sort),
            "selector sorts must be the substituted {field_sort:?}, got {info:?}"
        );
    }
}

// ============================================================================
// #reserved-ops dynamic datatype-member gates (Remediate2)
//
// The DT theory matches constructor/selector/tester operations structurally
// by name, so declaring a same-named user symbol conflates it with the
// builtin operation. Both directions were confirmed wrong-UNSATs on clean
// HEAD 477f3d06d9:
//   forward: (declare-datatype Lst ((Cons (hd Int)) (Nil))) then
//            (declare-fun is-Cons (Lst) Bool) / (declare-fun hd (Lst) Int) —
//            the forged "fresh" symbol got the builtin tester/selector
//            semantics (rc_forge_tester.smt2 / rc_forge_selector.smt2);
//   reverse: (declare-sort Lst 0) + (declare-fun hd (Lst) Int) + use, then
//            (declare-datatype Lst ((Cons (hd Int)) (Nil))) — the
//            pre-declared symbol's applications were captured as selector
//            operations (rev_pre_use.smt2 / rev_pre_use_tester.smt2).
// ============================================================================

/// Forward gate: declaring a fn/const/define-fun whose name is a registered
/// datatype constructor, selector, or tester is rejected with
/// `DatatypeMemberCollision`.
#[test]
fn test_datatype_member_forgery_rejected() {
    let dt = "(declare-datatype Lst ((Cons (hd Int)) (Nil)))";
    for (decl, what) in [
        (
            "(declare-fun is-Cons (Lst) Bool)",
            "tester via declare-fun (exact sig)",
        ),
        (
            "(declare-fun is-Cons (Int) Bool)",
            "tester via declare-fun (wrong sig)",
        ),
        (
            "(declare-fun hd (Lst) Int)",
            "selector via declare-fun (exact sig)",
        ),
        (
            "(declare-fun hd (Int) Bool)",
            "selector via declare-fun (wrong sig)",
        ),
        (
            "(declare-fun Cons (Int) Lst)",
            "constructor via declare-fun",
        ),
        (
            "(declare-fun Nil () Lst)",
            "nullary constructor via declare-fun",
        ),
        ("(declare-const hd Int)", "selector name via declare-const"),
        (
            "(declare-const Nil Lst)",
            "nullary constructor via declare-const",
        ),
        (
            "(define-fun is-Cons ((l Lst)) Bool false)",
            "tester via define-fun",
        ),
        (
            "(define-fun-rec hd ((l Lst)) Int (hd l))",
            "selector via define-fun-rec",
        ),
    ] {
        let script = format!("{dt}\n{decl}");
        let commands = parse(&script).unwrap();
        let mut ctx = Context::new();
        let mut rejected = false;
        for cmd in &commands {
            if let Err(e) = ctx.process_command(cmd) {
                assert!(
                    matches!(e, ElaborateError::DatatypeMemberCollision(_)),
                    "expected DatatypeMemberCollision for {what} via `{decl}`, got: {e:?}"
                );
                rejected = true;
                break;
            }
        }
        assert!(
            rejected,
            "forged member declaration must be rejected: {what} via `{decl}`"
        );
    }
}

/// Forward gate covers parametric datatypes too: template members (both
/// before and after instantiation) are not declarable.
#[test]
fn test_parametric_datatype_member_forgery_rejected() {
    // Before instantiation: the template members are gated.
    let script_template_only = r#"
            (declare-datatype Opt (par (T) ((onone) (osome (oval T)))))
            (declare-fun oval (Int) Int)
        "#;
    // After instantiation: the surface names of instance members are gated.
    let script_instantiated = r#"
            (declare-datatype Opt (par (T) ((onone) (osome (oval T)))))
            (declare-const x (Opt Bool))
            (declare-fun osome (Bool) Bool)
        "#;
    for (script, what) in [
        (
            script_template_only,
            "template selector before instantiation",
        ),
        (
            script_instantiated,
            "instance constructor after instantiation",
        ),
    ] {
        let commands = parse(script).unwrap();
        let mut ctx = Context::new();
        let mut rejected = false;
        for cmd in &commands {
            if let Err(e) = ctx.process_command(cmd) {
                assert!(
                    matches!(e, ElaborateError::DatatypeMemberCollision(_)),
                    "expected DatatypeMemberCollision for {what}, got: {e:?}"
                );
                rejected = true;
                break;
            }
        }
        assert!(
            rejected,
            "forged parametric member declaration must be rejected: {what}"
        );
    }
}

/// Reverse gate: re-declaring an existing sort name as a datatype is rejected
/// with `SortRedeclaration` — this is the only way a pre-existing user symbol
/// can mention the new datatype's carrier sort and be captured by its member
/// operations (the rev_pre_use wrong-UNSAT).
#[test]
fn test_datatype_sort_redeclaration_rejected() {
    for (script, what) in [
        (
            "(declare-sort Lst 0)\n(declare-datatype Lst ((Cons (hd Int)) (Nil)))",
            "declare-sort then declare-datatype",
        ),
        (
            "(declare-datatype D ((mk (f Int))))\n(declare-datatype D ((mk2 (g Int))))",
            "declare-datatype twice",
        ),
        (
            "(define-sort S () Int)\n(declare-datatype S ((mkS)))",
            "define-sort alias then declare-datatype",
        ),
        (
            "(declare-sort G 0)\n(declare-datatypes ((G 0)) (((mkG (gf Int)))))",
            "declare-sort then declare-datatypes group",
        ),
        (
            "(declare-datatype P (par (T) ((mkP (pf T)))))\n(declare-datatype P ((mkQ)))",
            "parametric template then monomorphic redeclaration",
        ),
    ] {
        let commands = parse(script).unwrap();
        let mut ctx = Context::new();
        let mut rejected = false;
        for cmd in &commands {
            if let Err(e) = ctx.process_command(cmd) {
                assert!(
                    matches!(e, ElaborateError::SortRedeclaration(_)),
                    "expected SortRedeclaration for {what}, got: {e:?}"
                );
                rejected = true;
                break;
            }
        }
        assert!(rejected, "sort redeclaration must be rejected: {what}");
    }
}

/// The gates must NOT break supported overloading: two datatypes sharing a
/// selector name (resolved by argument sort), and a plain user fn declared
/// BEFORE a datatype whose selector shares its name but cannot mention the
/// new carrier sort (different signature — stays a correct independent
/// symbol; verified `sat` end-to-end on the CLI as rev_difsig.smt2).
#[test]
fn test_datatype_member_overloading_still_works() {
    // Selector name shared across two datatypes.
    let script_dt_dt = r#"
            (declare-datatype A ((mkA (val Int))))
            (declare-datatype B ((mkB (val Bool))))
            (declare-const a A)
            (declare-const b B)
            (assert (= (val a) 1))
            (assert (val b))
        "#;
    // User fn declared before a datatype introducing a same-named selector.
    let script_fn_then_dt = r#"
            (declare-fun hd (Int) Int)
            (declare-datatype Lst ((Cons (hd Int)) (Nil)))
            (declare-const l Lst)
            (assert (= l (Cons 5)))
            (assert (= (hd 3) 7))
        "#;
    for (script, what) in [
        (script_dt_dt, "selector overloaded across datatypes"),
        (script_fn_then_dt, "user fn before same-named selector"),
    ] {
        let commands = parse(script).unwrap();
        let mut ctx = Context::new();
        for cmd in &commands {
            ctx.process_command(cmd)
                .unwrap_or_else(|e| panic!("{what} must stay accepted, got: {e:?}"));
        }
    }
}

/// Scoped datatypes: after `pop`, the member names and the sort name are free
/// again — the dynamic gates must consult only LIVE registrations.
#[test]
fn test_datatype_member_gate_respects_pop() {
    let script = r#"
            (push 1)
            (declare-datatype Tmp ((mkTmp (tf Int))))
            (pop 1)
            (declare-fun tf (Int) Int)
            (declare-fun mkTmp (Int) Int)
            (declare-fun is-mkTmp (Int) Bool)
            (declare-datatype Tmp ((other)))
        "#;
    let commands = parse(script).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .unwrap_or_else(|e| panic!("post-pop redeclaration must be accepted, got: {e:?}"));
    }
}

#[test]
fn test_bare_symbol_nullary_constructors_elaborate() {
    // `(declare-datatype Color (red green blue))` — bare symbols are nullary
    // constructors (z3 shorthand). Must register them like `((red)(green)...)`.
    let mut ctx = Context::new();
    for cmd in parse("(declare-datatype Color (red green blue))").unwrap() {
        ctx.process_command(&cmd)
            .unwrap_or_else(|e| panic!("bare-symbol constructors must elaborate, got: {e:?}"));
    }
    assert!(ctx.sort_defs.contains_key("Color"));
    for ctor in ["red", "green", "blue"] {
        let c = ctx
            .symbols
            .get(ctor)
            .unwrap_or_else(|| panic!("{ctor} constructor not registered"));
        assert!(c.arg_sorts.is_empty(), "{ctor} must be nullary");
    }
}

#[test]
fn test_legacy_declare_datatypes_elaborates() {
    // Pre-2.6 legacy syntax `(declare-datatypes () ((Name <ctor>+) ...))` must
    // register the datatype + constructors exactly like the modern form (z3
    // still accepts it). Enum + recursive datatype in one command.
    let mut ctx = Context::new();
    let script = "(declare-datatypes () ((Color (red) (green)) \
                  (Lst (nil) (cons (hd Int) (tl Lst)))))";
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd)
            .unwrap_or_else(|e| panic!("legacy declare-datatypes must elaborate, got: {e:?}"));
    }
    assert!(ctx.sort_defs.contains_key("Color"));
    assert!(ctx.sort_defs.contains_key("Lst"));
    assert!(ctx.symbols.contains_key("red"));
    assert!(ctx.symbols.contains_key("green"));
    // The recursive constructor and its selector are registered.
    let cons = ctx.symbols.get("cons").expect("cons constructor not found");
    assert_eq!(cons.arg_sorts.len(), 2);
    assert!(ctx.symbols.contains_key("hd"));
    assert!(ctx.symbols.contains_key("tl"));
}
