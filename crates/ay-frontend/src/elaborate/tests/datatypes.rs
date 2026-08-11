// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::command::{self, Command};

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
fn failed_single_datatype_declaration_is_atomic() {
    let mut ctx = Context::new();
    let declaration = Command::DeclareDatatype(
        "Broken".to_string(),
        command::DatatypeDec {
            constructors: vec![command::ConstructorDec {
                name: "mk-broken".to_string(),
                selectors: vec![command::SelectorDec {
                    name: "broken-field".to_string(),
                    sort: command::Sort::Indexed("BitVec".to_string(), Vec::new()),
                }],
            }],
            type_params: Vec::new(),
        },
    );

    assert!(ctx.process_command(&declaration).is_err());
    assert!(!ctx.sort_defs.contains_key("Broken"));
    assert!(!ctx.datatypes.contains_key("Broken"));
    assert!(!ctx.constructors.contains_key("mk-broken"));
    assert!(!ctx.symbols.contains_key("mk-broken"));
    assert!(!ctx.symbols.contains_key("broken-field"));
    assert!(!ctx.symbols.contains_key("is-mk-broken"));
}

#[test]
fn failed_datatype_group_leaves_no_partial_declarations() {
    let mut ctx = Context::new();
    let commands = parse(
        "(declare-datatypes ((Good 0) (Broken 0)) \
         (((mk-good (value Int))) ((mk-broken (bad (Unknown Int))))))",
    )
    .expect("parse datatype group");

    assert!(ctx.process_command(&commands[0]).is_err());
    for name in ["Good", "Broken"] {
        assert!(!ctx.sort_defs.contains_key(name));
        assert!(!ctx.datatypes.contains_key(name));
    }
    for name in [
        "mk-good",
        "value",
        "is-mk-good",
        "mk-broken",
        "bad",
        "is-mk-broken",
    ] {
        assert!(!ctx.symbols.contains_key(name), "surviving symbol: {name}");
    }
}

#[test]
fn datatype_group_validates_cardinality_arity_and_duplicate_sorts_first() {
    let datatype = command::DatatypeDec {
        constructors: vec![command::ConstructorDec {
            name: "unit".to_string(),
            selectors: Vec::new(),
        }],
        type_params: Vec::new(),
    };

    let mut mismatched = Context::new();
    let mismatch = Command::DeclareDatatypes(
        vec![command::SortDec {
            name: "OnlySort".to_string(),
            arity: 0,
        }],
        Vec::new(),
    );
    assert!(mismatched.process_command(&mismatch).is_err());
    assert!(!mismatched.sort_defs.contains_key("OnlySort"));

    let mut duplicate = Context::new();
    let duplicate_group = Command::DeclareDatatypes(
        vec![
            command::SortDec {
                name: "Duplicate".to_string(),
                arity: 0,
            },
            command::SortDec {
                name: "Duplicate".to_string(),
                arity: 0,
            },
        ],
        vec![datatype.clone(), datatype.clone()],
    );
    assert!(duplicate.process_command(&duplicate_group).is_err());
    assert!(!duplicate.sort_defs.contains_key("Duplicate"));

    let mut bad_arity = Context::new();
    let arity_group = Command::DeclareDatatypes(
        vec![
            command::SortDec {
                name: "First".to_string(),
                arity: 0,
            },
            command::SortDec {
                name: "Second".to_string(),
                arity: 1,
            },
        ],
        vec![datatype.clone(), datatype],
    );
    assert!(bad_arity.process_command(&arity_group).is_err());
    assert!(!bad_arity.sort_defs.contains_key("First"));
    assert!(!bad_arity.parametric_datatypes.contains_key("Second"));
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
    assert_eq!(ctx.live_datatype_iter().count(), 1);
    assert!(ctx.is_constructor("Red").is_some());

    // Push a scope and declare Option inside it
    ctx.push();
    let script2 = "(declare-datatype Option ((None) (Some (value Int))))";
    for cmd in parse(script2).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    // Both datatypes should be visible
    assert_eq!(ctx.live_datatype_iter().count(), 2);
    assert!(ctx.is_constructor("Red").is_some());
    assert!(ctx.is_constructor("None").is_some());
    assert!(ctx.is_constructor("Some").is_some());

    // Pop the scope
    assert!(ctx.pop(), "pop should succeed after push");

    // Only Color remains source-visible. Exact Option semantics stay sticky so
    // a retained old TermId can still be solved soundly after this pop.
    assert_eq!(ctx.live_datatype_iter().count(), 1);
    assert_eq!(ctx.datatype_iter().count(), 2);
    assert!(ctx.is_constructor("Red").is_some());
    assert!(ctx.is_constructor("None").is_some());
    assert!(ctx.is_constructor("Some").is_some());
    assert!(!ctx.is_datatype_member_name("None"));
    assert!(!ctx.is_datatype_member_name("Some"));

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

#[test]
fn popped_datatype_member_core_identities_are_never_reused() {
    fn identity(ctx: &Context, surface: &str, args: &[Sort], result: &Sort) -> String {
        let info = ctx
            .symbol_info_with_signature(surface, args, result)
            .unwrap_or_else(|| panic!("missing exact datatype member {surface}"));
        ctx.symbol_identity_name(surface, info).to_string()
    }

    let declaration = "(declare-datatype ScopedDt ((ScopedC (scoped-field Int)) (ScopedOther)))";
    let mut ctx = Context::new();
    ctx.push();
    for command in parse(declaration).expect("parse first datatype") {
        ctx.process_command(&command)
            .expect("declare first scoped datatype");
    }
    let old_carrier = ctx
        .sort_definition("ScopedDt")
        .expect("first datatype carrier")
        .clone();
    let old_ctor = identity(&ctx, "ScopedC", &[Sort::Int], &old_carrier);
    let old_selector = identity(
        &ctx,
        "scoped-field",
        std::slice::from_ref(&old_carrier),
        &Sort::Int,
    );
    let old_tester = identity(
        &ctx,
        "is-ScopedC",
        std::slice::from_ref(&old_carrier),
        &Sort::Bool,
    );
    assert_eq!(old_ctor, "ScopedC");
    assert_eq!(old_selector, "scoped-field");
    assert_eq!(old_tester, "is-ScopedC");

    assert!(ctx.pop(), "pop first datatype declaration");
    assert_eq!(
        ctx.surface_sort(&old_carrier),
        Some(command::Sort::Simple("ScopedDt".to_string())),
        "popped carrier keeps sticky source rendering while its terms survive"
    );
    for command in parse(declaration).expect("parse reincarnated datatype") {
        ctx.process_command(&command)
            .expect("declare reincarnated datatype");
    }
    let new_carrier = ctx
        .sort_definition("ScopedDt")
        .expect("reincarnated datatype carrier")
        .clone();
    let new_ctor = identity(&ctx, "ScopedC", &[Sort::Int], &new_carrier);
    let new_selector = identity(
        &ctx,
        "scoped-field",
        std::slice::from_ref(&new_carrier),
        &Sort::Int,
    );
    let new_tester = identity(
        &ctx,
        "is-ScopedC",
        std::slice::from_ref(&new_carrier),
        &Sort::Bool,
    );

    assert_ne!(new_carrier, old_carrier);
    assert_ne!(new_ctor, old_ctor);
    assert_ne!(new_selector, old_selector);
    assert_ne!(new_tester, old_tester);
    assert_eq!(ctx.dt_surface_name(&new_ctor), Some("ScopedC"));
    assert_eq!(ctx.dt_surface_name(&new_selector), Some("scoped-field"));
    assert_eq!(ctx.dt_surface_name(&new_tester), Some("is-ScopedC"));
    assert_eq!(ctx.output_symbol_name(&old_ctor), old_ctor);
    assert_eq!(ctx.output_symbol_name(&new_ctor), new_ctor);
    assert_eq!(
        ctx.format_sort_surface(&old_carrier),
        Some(ay_core::quote_symbol(match &old_carrier {
            Sort::Uninterpreted(identity) => identity,
            _ => unreachable!("datatype carrier must be nominal"),
        }))
    );
    assert_eq!(
        ctx.format_sort_surface(&new_carrier),
        Some(ay_core::quote_symbol(match &new_carrier {
            Sort::Uninterpreted(identity) => identity,
            _ => unreachable!("datatype carrier must be nominal"),
        }))
    );
    let Sort::Uninterpreted(new_carrier_name) = &new_carrier else {
        panic!("datatype carrier must be nominal")
    };
    assert_eq!(
        ctx.datatypes
            .get(new_carrier_name)
            .and_then(|constructors| constructors.first()),
        Some(&new_ctor),
        "datatype metadata must carry the fresh constructor identity"
    );
    assert_eq!(
        ctx.constructor_selector_info(&new_ctor)
            .and_then(|fields| fields.first())
            .map(|(name, _)| name),
        Some(&new_selector),
        "selector metadata must carry the fresh selector identity"
    );
}

#[test]
fn popped_parametric_instance_member_core_identities_are_never_reused() {
    let template = "(declare-datatypes ((ScopedBox 1)) \
        ((par (T) ((scoped-box (scoped-unbox T))))))";
    let preferred_instance = "ScopedBox!{Int}";
    let mut ctx = Context::new();
    ctx.push();
    for command in parse(&format!(
        "{template} (declare-const first-scoped-box (ScopedBox Int))"
    ))
    .expect("parse first parametric instance")
    {
        ctx.process_command(&command)
            .expect("instantiate first parametric datatype");
    }
    let old_instance = ctx
        .parametric_instance_sorts
        .get(&(
            ctx.parametric_datatype_ids["ScopedBox"].clone(),
            vec![Sort::Int],
        ))
        .expect("first instance carrier")
        .clone();
    let old_ctor = ctx.datatypes[&old_instance][0].clone();
    let old_selector = ctx.constructor_selector_info(&old_ctor).unwrap()[0]
        .0
        .clone();

    assert!(ctx.pop(), "pop first parametric datatype");
    for command in parse(&format!(
        "{template} (declare-const second-scoped-box (ScopedBox Int))"
    ))
    .expect("parse reincarnated parametric instance")
    {
        ctx.process_command(&command)
            .expect("instantiate reincarnated parametric datatype");
    }
    let new_instance = ctx
        .parametric_instance_sorts
        .get(&(
            ctx.parametric_datatype_ids["ScopedBox"].clone(),
            vec![Sort::Int],
        ))
        .expect("reincarnated instance carrier")
        .clone();
    let new_ctor = ctx.datatypes[&new_instance][0].clone();
    let new_selector = ctx.constructor_selector_info(&new_ctor).unwrap()[0]
        .0
        .clone();

    assert_ne!(new_instance, old_instance);
    assert_ne!(new_ctor, old_ctor);
    assert_ne!(new_selector, old_selector);
    assert_eq!(ctx.dt_surface_name(&new_ctor), Some("scoped-box"));
    assert_eq!(ctx.dt_surface_name(&new_selector), Some("scoped-unbox"));
    assert_eq!(ctx.sort_surface_name(&new_instance), preferred_instance);
    assert!(ctx.is_parametric_datatype_instance(&new_instance));
    assert_eq!(
        ctx.surface_sort(&Sort::Uninterpreted(new_instance.clone())),
        Some(command::Sort::Parameterized(
            "ScopedBox".to_string(),
            vec![command::Sort::Simple("Int".to_string())]
        ))
    );
    assert_eq!(
        ctx.format_sort_surface(&Sort::Uninterpreted(old_instance.clone())),
        Some(ay_core::quote_symbol(&old_instance))
    );
    assert_eq!(
        ctx.format_sort_surface(&Sort::Uninterpreted(new_instance.clone())),
        Some(ay_core::quote_symbol(&new_instance))
    );
}

#[test]
fn parametric_instance_lifetime_follows_its_template_not_first_use_scope() {
    let mut ctx = Context::new();
    for command in parse(
        "(declare-datatypes ((StableBox 1)) \
         ((par (T) ((stable-box (stable-unbox T))))))",
    )
    .expect("parse outer template")
    {
        ctx.process_command(&command)
            .expect("declare outer template");
    }
    let template_id = ctx.parametric_datatype_ids["StableBox"].clone();

    ctx.push();
    for command in
        parse("(declare-const inner-box (StableBox Int))").expect("parse first ground use")
    {
        ctx.process_command(&command)
            .expect("instantiate inside nested scope");
    }
    let instance_key = (template_id, vec![Sort::Int]);
    let first_carrier = ctx.parametric_instance_sorts[&instance_key].clone();
    let first_constructor = ctx.datatypes[&first_carrier][0].clone();
    let first_declaration = ctx
        .exact_datatype_member_info(&first_constructor)
        .expect("sticky constructor signature")
        .declaration_id()
        .clone();

    assert!(ctx.pop(), "pop incidental first-use scope");
    assert!(ctx.is_live_datatype_carrier(&first_carrier));
    assert!(!ctx.symbols.contains_key("stable-box"));

    for command in
        parse("(declare-const outer-box (StableBox Int))").expect("parse repeated ground use")
    {
        ctx.process_command(&command)
            .expect("reactivate exact cached instance");
    }
    let second_carrier = ctx.parametric_instance_sorts[&instance_key].clone();
    assert_eq!(second_carrier, first_carrier);
    let info = ctx
        .symbol_info_with_signature(
            "stable-box",
            &[Sort::Int],
            &Sort::Uninterpreted(second_carrier),
        )
        .expect("reactivated constructor binding");
    assert_eq!(
        ctx.symbol_identity_name("stable-box", info),
        first_constructor
    );
    assert_eq!(info.declaration_id(), &first_declaration);
}

#[test]
fn scoped_parametric_template_pop_removes_members_activated_as_global() {
    let template = "(declare-datatypes ((OptionFlipBox 1)) \
        ((par (T) ((option-flip-box (option-flip-unbox T))))))";
    let mut ctx = Context::new();
    for command in
        parse("(declare-fun option-flip-box (Bool) Bool)").expect("parse unrelated overload")
    {
        ctx.process_command(&command)
            .expect("declare unrelated overload before the template");
    }
    ctx.push();
    for command in parse(template).expect("parse scoped template") {
        ctx.process_command(&command)
            .expect("declare scoped template while declarations are local");
    }
    for command in parse(
        "(set-option :global-declarations true) \
         (declare-const old-option-flip-box (OptionFlipBox Int)) \
         (assert (= (option-flip-box 1) (option-flip-box 2)))",
    )
    .expect("parse option flip and lazy instance")
    {
        ctx.process_command(&command)
            .expect("instantiate after enabling global declarations");
    }
    let old_template_id = ctx.parametric_datatype_ids["OptionFlipBox"].clone();
    let old_carrier = ctx.parametric_instance_sorts[&(old_template_id, vec![Sort::Int])].clone();
    let old_constructor = ctx.datatypes[&old_carrier][0].clone();
    let old_assertion = ctx.assertions[0];

    assert!(ctx.pop(), "pop scoped template");
    assert!(!ctx.is_live_datatype_carrier(&old_carrier));
    assert!(ctx
        .symbol_info_with_signature("option-flip-box", &[Sort::Bool], &Sort::Bool)
        .is_some());
    assert!(ctx
        .symbol_info_with_signature(
            "option-flip-box",
            &[Sort::Int],
            &Sort::Uninterpreted(old_carrier.clone())
        )
        .is_none());
    assert!(!ctx.symbols.contains_key("option-flip-unbox"));
    assert!(!ctx.symbols.contains_key("is-option-flip-box"));
    assert!(!ctx.is_datatype_member_name("option-flip-box"));
    assert!(ctx.datatypes.contains_key(&old_carrier));
    assert!(ctx.exact_datatype_member_info(&old_constructor).is_some());
    assert_eq!(ctx.terms.sort(old_assertion), &Sort::Bool);

    for command in parse(&format!(
        "{template} (declare-const new-option-flip-box (OptionFlipBox Int))"
    ))
    .expect("parse reincarnated template")
    {
        ctx.process_command(&command)
            .expect("redeclare template and instantiate fresh epoch");
    }
    let new_template_id = ctx.parametric_datatype_ids["OptionFlipBox"].clone();
    let new_carrier = ctx.parametric_instance_sorts[&(new_template_id, vec![Sort::Int])].clone();
    let new_constructor = ctx.datatypes[&new_carrier][0].clone();
    assert_ne!(new_carrier, old_carrier);
    assert_ne!(new_constructor, old_constructor);
    assert!(ctx.is_live_datatype_carrier(&new_carrier));
}

#[test]
fn full_reset_clears_sticky_datatype_semantics() {
    let mut ctx = Context::new();
    for command in parse(
        "(declare-datatype ResetDt ((reset-ctor (reset-field Int)))) \
         (reset)",
    )
    .expect("parse datatype and reset")
    {
        ctx.process_command(&command)
            .expect("process datatype and full reset");
    }

    assert_eq!(ctx.datatype_iter().count(), 0);
    assert_eq!(ctx.live_datatype_iter().count(), 0);
    assert!(ctx.datatype_member_symbols.is_empty());
    assert!(ctx.nominal_sort_surfaces.is_empty());
    assert!(ctx.parametric_instance_args.is_empty());
    assert!(ctx.parametric_instance_sorts.is_empty());
}

#[test]
fn parametric_instance_identity_is_structural_not_display_mangled() {
    let mut ctx = Context::new();
    let script = r#"
        (declare-sort |Array!{Int}!{Bool}| 0)
        (declare-datatypes ((Box 1)) ((par (T) ((box (unbox T))))))
        (declare-const atom-box (Box |Array!{Int}!{Bool}|))
        (declare-const array-box (Box (Array Int Bool)))
    "#;
    for command in parse(script).expect("parse structurally colliding instances") {
        ctx.process_command(&command)
            .expect("structurally distinct instances must coexist");
    }

    let template_id = ctx.parametric_datatype_ids["Box"].clone();
    let atom_sort = ctx
        .sort_definition("Array!{Int}!{Bool}")
        .expect("declared atom sort")
        .clone();
    let atom_instance = ctx
        .parametric_instance_sorts
        .get(&(template_id.clone(), vec![atom_sort]))
        .expect("Box over the atom sort")
        .clone();
    let array_instance = ctx
        .parametric_instance_sorts
        .get(&(template_id, vec![Sort::array(Sort::Int, Sort::Bool)]))
        .expect("Box over the Array sort")
        .clone();

    assert_ne!(atom_instance, array_instance);
    assert_ne!(
        ctx.datatypes[&atom_instance][0],
        ctx.datatypes[&array_instance][0]
    );
    assert_eq!(
        ctx.sort_surface_name(&atom_instance),
        "Box!{Array!{Int}!{Bool}}"
    );
    assert_eq!(
        ctx.sort_surface_name(&array_instance),
        "Box!{Array!{Int}!{Bool}}"
    );
    assert_eq!(
        ctx.surface_sort(&Sort::Uninterpreted(atom_instance)),
        Some(command::Sort::Parameterized(
            "Box".to_string(),
            vec![command::Sort::Simple("Array!{Int}!{Bool}".to_string())]
        ))
    );
    assert_eq!(
        ctx.surface_sort(&Sort::seq(Sort::Uninterpreted(array_instance))),
        Some(command::Sort::Parameterized(
            "Seq".to_string(),
            vec![command::Sort::Parameterized(
                "Box".to_string(),
                vec![command::Sort::Parameterized(
                    "Array".to_string(),
                    vec![
                        command::Sort::Simple("Int".to_string()),
                        command::Sort::Simple("Bool".to_string())
                    ]
                )]
            )]
        ))
    );
}

#[test]
fn parametric_instance_does_not_capture_a_sort_alias_named_like_its_mangle() {
    let mut ctx = Context::new();
    let script = r#"
        (define-sort |Box!{Int}| () Int)
        (declare-datatypes ((Box 1)) ((par (T) ((box (unbox T))))))
        (declare-const boxed-int (Box Int))
        (declare-const alias-int |Box!{Int}|)
    "#;
    for command in parse(script).expect("parse alias-collision fixture") {
        ctx.process_command(&command)
            .expect("parametric instance must not overwrite the live alias");
    }

    assert_eq!(ctx.sort_definition("Box!{Int}"), Some(&Sort::Int));
    let template_id = ctx.parametric_datatype_ids["Box"].clone();
    let instance = ctx
        .parametric_instance_sorts
        .get(&(template_id, vec![Sort::Int]))
        .expect("Box Int instance carrier");
    assert_ne!(instance, "Box!{Int}");
    assert!(ctx.datatypes.contains_key(instance));
    assert_eq!(
        ctx.terms
            .sort(ctx.symbols["alias-int"].term.expect("alias constant")),
        &Sort::Int
    );
}

#[test]
fn failed_parametric_instance_registration_rolls_back_live_indices() {
    let commands = parse(
        "(declare-datatypes ((BrokenBox 1)) \
         ((par (T) ((broken-box (broken-field (Unknown T))))))) \
         (declare-const broken (BrokenBox Int))",
    )
    .expect("parse invalid parametric instance fixture");
    let mut ctx = Context::new();
    ctx.process_command(&commands[0])
        .expect("template registration is lazy");

    assert!(ctx.process_command(&commands[1]).is_err());
    assert!(ctx.parametric_instance_sorts.is_empty());
    assert!(ctx.parametric_instance_args.is_empty());
    assert!(ctx.datatypes.is_empty());
    assert!(!ctx.symbols.contains_key("broken-box"));
    assert!(!ctx.symbols.contains_key("broken-field"));
    assert!(!ctx.symbols.contains_key("is-broken-box"));

    assert!(ctx.process_command(&commands[1]).is_err());
    assert!(ctx.parametric_instance_sorts.is_empty());
    assert!(ctx.parametric_instance_args.is_empty());
    assert!(ctx.datatypes.is_empty());
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

#[test]
fn datatype_map_target_members_never_own_canonical_theory_identities() {
    let commands = parse("(declare-datatype Op ((div (mod Int))))").unwrap();
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).unwrap();
    }

    for (surface, kind) in [
        ("div", DeclarationKind::DatatypeConstructor),
        ("mod", DeclarationKind::DatatypeSelector),
    ] {
        let info = context.symbol_info(surface).expect("datatype member");
        let core = context.symbol_identity_name(surface, info);
        assert!(core.starts_with("__ay_overload_"));
        assert_ne!(core, surface);
        assert_eq!(info.declaration_kind(), kind);
        assert!(context.symbol_info_by_identity(surface).is_none());
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

/// An EXACTLY-identical datatype re-declaration is adopted as a no-op (the
/// adopt-identical embedder contract, mirroring `try_declare_fun`). An embedder
/// that re-asserts its canonical declaration before each selector/match use is
/// therefore not rejected.
#[test]
fn test_identical_datatype_redeclaration_is_adopted() {
    for script in [
        "(declare-datatype Color ((Red) (Green) (Blue)))\n\
         (declare-datatype Color ((Red) (Green) (Blue)))",
        "(declare-datatype Pt ((mk (x Int) (y Int))))\n\
         (declare-datatype Pt ((mk (x Int) (y Int))))",
    ] {
        let commands = parse(script).unwrap();
        let mut ctx = Context::new();
        for cmd in &commands {
            ctx.process_command(cmd)
                .expect("identical datatype re-declaration must be adopted as a no-op");
        }
    }
}

/// The adopt-identical path must NOT adopt a DIFFERENT datatype of the same name.
/// Same constructor NAME but a different selector SORT is a distinct
/// `DatatypeDec`, so it still hits the `SortRedeclaration` gate — the second
/// declaration's members can never silently shadow the first's. (A
/// constructor-names-only identity check would wrongly adopt this.)
#[test]
fn test_same_name_different_selector_sort_still_rejected() {
    let script = "(declare-datatype Dd ((mk (f Int))))\n\
                  (declare-datatype Dd ((mk (f Bool))))";
    let commands = parse(script).unwrap();
    let mut ctx = Context::new();
    let mut rejected = false;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            assert!(
                matches!(e, ElaborateError::SortRedeclaration(_)),
                "expected SortRedeclaration, got: {e:?}"
            );
            rejected = true;
            break;
        }
    }
    assert!(
        rejected,
        "a same-name datatype with a different selector sort must still be rejected"
    );
}

// ---------------------------------------------------------------------------
// Two datatypes may share a nullary constructor NAME (SMT-LIB 2.6 §4.2.3 is the
// standard's main source of ad-hoc overloading, and §3.6.4's `(as f σ)` exists
// precisely to disambiguate it). Each such constructor is a DISTINCT value of a
// DISTINCT sort.
//
// `Context::symbols` keeps only the last-registered signature for a name, so a
// bare lookup of the constructor handed back the most recently declared
// datatype's inhabitant regardless of which datatype was asked for. With
// `(declare-datatypes ((A 0) (B 0)) (((e)) ((e))))`, `(declare-const x A)` bound
// `x` to B's `e`: `(= x (as e A))` was rejected as `Sorts B and A are
// incompatible` while the B-only spelling was accepted — a pure
// declaration-order artifact — and `(distinct x y)` over `x : A`, `y : B`
// collapsed to `(distinct t t)` and answered `unsat`.

fn declared_const_term(ctx: &Context, name: &str) -> TermId {
    ctx.symbols
        .get(name)
        .and_then(|info| info.term)
        .unwrap_or_else(|| panic!("constant '{name}' has no bound term"))
}

fn elaborate_script(input: &str) -> Context {
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .unwrap_or_else(|e| panic!("elaboration failed on {cmd:?}: {e:?}"));
    }
    ctx
}

#[test]
fn test_overloaded_nullary_constructor_binds_the_right_datatype() {
    let ctx = elaborate_script(
        "(declare-datatypes ((A 0) (B 0)) (((e)) ((e))))\n\
         (declare-const x A)\n\
         (declare-const y B)",
    );
    let x = declared_const_term(&ctx, "x");
    let y = declared_const_term(&ctx, "y");
    assert_eq!(
        ctx.terms.sort(x),
        &Sort::Uninterpreted("A".to_string()),
        "x : A must be bound to a term of sort A, not to B's same-named constructor"
    );
    assert_eq!(
        ctx.terms.sort(y),
        &Sort::Uninterpreted("B".to_string()),
        "y : B must be bound to a term of sort B"
    );
    assert_ne!(
        x, y,
        "A's `e` and B's `e` are distinct values of distinct sorts and must not \
         be conflated into one term"
    );
}

#[test]
fn test_as_ascription_selects_the_ascribed_datatype_either_way() {
    // Both ascriptions must be accepted, and each must denote its OWN
    // datatype's constructor — the resolution is decided by the ascription, not
    // by declaration order.
    let ctx = elaborate_script(
        "(declare-datatypes ((A 0) (B 0)) (((e)) ((e))))\n\
         (declare-const x A)\n\
         (declare-const y B)\n\
         (assert (= x (as e A)))\n\
         (assert (= y (as e B)))",
    );
    assert_eq!(ctx.assertions.len(), 2);
    let x = declared_const_term(&ctx, "x");
    let y = declared_const_term(&ctx, "y");
    assert_ne!(
        x, y,
        "the two ascriptions must not resolve to the same term"
    );
    // A zero-field single-constructor datatype has exactly one inhabitant, so
    // each equality is the SAME trivially-true term.
    assert_eq!(
        ctx.assertions[0], ctx.assertions[1],
        "each constant is its own datatype's sole inhabitant, so both equalities \
         reduce to the same trivially-true term"
    );
}

#[test]
fn test_non_overloaded_nullary_constructor_still_binds_its_inhabitant() {
    // Guard against over-declining: the ordinary, non-overloaded case must
    // still eagerly bind the constant to the datatype's sole inhabitant.
    let ctx = elaborate_script(
        "(declare-datatypes ((Unit 0)) (((u))))\n\
         (declare-const p Unit)\n\
         (declare-const q Unit)",
    );
    assert_eq!(
        declared_const_term(&ctx, "p"),
        declared_const_term(&ctx, "q"),
        "a zero-field single-constructor datatype has exactly one inhabitant"
    );
}

// --- Alethe surface rendering of the invented single-constructor field
// --- constants (`Context::dt_field_surface_overrides`, `DtFieldSurface`).
//
// Eager single-constructor elimination rewrites `(declare-fun s_ () Record)`
// into `(Record s_!left s_!center s_!right)`. Those field names are minted by
// AY and appear in NO problem file, so an exported proof that spells them is
// unreadable to an external checker: on
// `QF_DT/20230720-blocksworld/..._bmc_2` they were 14 distinct names in 26,366
// occurrences under an EMPTY declaration preamble, and carcara 1.1.0 stopped in
// the PARSER — `identifier 's_tmp___!left' is not defined` — before checking a
// single rule. Each one must instead print as the selector application it
// denotes, over the constant the problem really declares.

fn ctor_args(ctx: &Context, term: TermId) -> Vec<TermId> {
    match ctx.terms.get(term) {
        TermData::App(_, args) => args.clone(),
        other => panic!("expected a constructor application, got {other:?}"),
    }
}

#[test]
fn test_dt_field_surface_renders_depth_one_field_as_selector_application() {
    let ctx = elaborate_script(
        "(declare-datatypes ((Rec 0)) (((mk (left Int) (right Int)))))\n\
         (declare-const s Rec)",
    );
    let fields = ctor_args(&ctx, declared_const_term(&ctx, "s"));
    let overrides = ctx.dt_field_surface_overrides();

    assert_eq!(
        overrides.get(&fields[0]).map(String::as_str),
        Some("(left s)"),
        "the invented field constant must print as the selector applied to the \
         DECLARED parent, which needs no new declaration"
    );
    assert_eq!(
        overrides.get(&fields[1]).map(String::as_str),
        Some("(right s)")
    );
    // The parent's constructor application prints structurally from the
    // already-rendered arguments; overriding it would collapse `(mk (left s)
    // (right s))` to `s` by surjective pairing, which no Alethe rule justifies.
    assert!(!overrides.contains_key(&declared_const_term(&ctx, "s")));
}

#[test]
fn test_dt_field_surface_composes_recursively_at_depth_two() {
    // `build_const_term` recurses when a field's sort is itself a
    // single-constructor datatype, minting `s!right!top`. The rendering must
    // compose through the whole chain: `(top s!right)` would just name another
    // symbol the problem never declared.
    let ctx = elaborate_script(
        "(declare-datatypes ((Inner 0)) (((mkI (top Int) (bot Int)))))\n\
         (declare-datatypes ((Outer 0)) (((mkO (right Inner) (lft Int)))))\n\
         (declare-const s Outer)",
    );
    let outer_fields = ctor_args(&ctx, declared_const_term(&ctx, "s"));
    let inner_fields = ctor_args(&ctx, outer_fields[0]);
    let overrides = ctx.dt_field_surface_overrides();

    assert_eq!(
        overrides.get(&inner_fields[0]).map(String::as_str),
        Some("(top (right s))"),
        "nested field constants must compose the full selector chain down to \
         the declared root"
    );
    assert_eq!(
        overrides.get(&inner_fields[1]).map(String::as_str),
        Some("(bot (right s))")
    );
    assert_eq!(
        overrides.get(&outer_fields[1]).map(String::as_str),
        Some("(lft s)")
    );
    assert!(
        !overrides.values().any(|rendering| rendering.contains('!')),
        "no rendering may leak an invented `parent!field` name: {overrides:?}"
    );
}

#[test]
fn test_dt_field_surface_never_rewrites_a_user_symbol_containing_bang() {
    // THE TRAP. QF_DT/blocksworld declares `c!0`, `c!1`, `c!2` as USER
    // constants. Any rule that recovers the parent by SPLITTING a name on '!'
    // turns `c!0` into the nonsense `(0 c)`. Membership comes from the
    // frontend's own mint-time record, keyed by `TermId`, so a user symbol can
    // never enter it however it is spelled.
    let ctx = elaborate_script(
        "(declare-datatypes ((Rec 0)) (((mk (left Int)))))\n\
         (declare-const c!0 Int)\n\
         (declare-const c!1 Int)\n\
         (declare-const s Rec)",
    );
    let overrides = ctx.dt_field_surface_overrides();

    for user in ["c!0", "c!1"] {
        assert!(
            !overrides.contains_key(&declared_const_term(&ctx, user)),
            "user symbol '{user}' must keep its own spelling, not be rewritten"
        );
    }
    assert!(
        !overrides
            .values()
            .any(|rendering| rendering.contains(" c)")),
        "no rendering may treat the '!' in a user symbol as a selector \
         boundary: {overrides:?}"
    );
    // The genuine field constant is still rendered.
    let field = ctor_args(&ctx, declared_const_term(&ctx, "s"))[0];
    assert_eq!(overrides.get(&field).map(String::as_str), Some("(left s)"));
}

#[test]
fn test_dt_field_surface_drops_a_field_whose_root_was_rebound() {
    // Liveness: after `pop`, `s` names a DIFFERENT constant. The old field
    // terms live on in the store, and rendering one of them as `(left s)` would
    // state something false about the new `s`. The guard re-walks the root's
    // current binding, so the stale entry is withheld.
    let commands = parse(
        "(declare-datatypes ((Rec 0)) (((mk (left Int)))))\n\
         (push 1)\n\
         (declare-const s Rec)",
    )
    .unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    let stale = ctor_args(&ctx, declared_const_term(&ctx, "s"))[0];
    assert_eq!(
        ctx.dt_field_surface_overrides()
            .get(&stale)
            .map(String::as_str),
        Some("(left s)")
    );

    for cmd in &parse("(pop 1)\n(declare-const s Rec)").unwrap() {
        ctx.process_command(cmd).unwrap();
    }
    let fresh = ctor_args(&ctx, declared_const_term(&ctx, "s"))[0];
    let overrides = ctx.dt_field_surface_overrides();

    assert_ne!(stale, fresh, "the redeclaration must mint a fresh field");
    assert!(
        !overrides.contains_key(&stale),
        "a field of the POPPED constant must never print as a selector over \
         the new binding of the same name"
    );
    assert_eq!(overrides.get(&fresh).map(String::as_str), Some("(left s)"));
}

#[test]
fn test_dt_field_surface_withholds_a_shadowed_selector_name() {
    // An external checker's symbol table is flat and last-declaration-wins
    // (measured on carcara 1.1.0), so a selector name registered twice may
    // resolve to the other binding — loudly when the signatures differ, but
    // SILENTLY when they match. Fail closed: emit nothing, leaving the term to
    // print as its (unreadable, but never wrong) invented name.
    let ctx = elaborate_script(
        "(declare-datatypes ((Rec 0)) (((mk (left Int)))))\n\
         (declare-datatypes ((Rec2 0)) (((mk2 (left Bool)))))\n\
         (declare-const s Rec)",
    );
    let field = ctor_args(&ctx, declared_const_term(&ctx, "s"))[0];
    assert!(
        !ctx.dt_field_surface_overrides().contains_key(&field),
        "a selector name bound by two datatypes is not safely renderable"
    );
}

#[test]
fn test_dt_field_surface_qualifies_polymorphic_overload_root() {
    let ctx = elaborate_script(
        "(declare-sort-parameter A)\n\
         (declare-datatype |Rec sort| ((mk (|left field| Bool))))\n\
         (declare-const |c root| A)",
    );
    let rec_sort = Sort::Uninterpreted("Rec sort".to_string());
    let rec_term = ctx
        .overloaded_symbols
        .get("c root")
        .expect("polymorphic constant has concrete overloads")
        .iter()
        .find(|info| info.arg_sorts.is_empty() && info.sort == rec_sort)
        .and_then(|info| info.term)
        .expect("datatype overload has an eager product term");
    let field = ctor_args(&ctx, rec_term)[0];

    assert_eq!(
        ctx.dt_field_surface_overrides()
            .get(&field)
            .map(String::as_str),
        Some("(|left field| (as |c root| |Rec sort|))")
    );
}
