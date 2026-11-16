// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn fixture() -> SerializableProofBundle {
    let terms = TermStore::new();
    let mut bundle = SerializableProofBundle::from_proof(&Proof::new(), &terms, Vec::new());
    bundle.datatype_declarations = vec![(
        "Pair".to_string(),
        vec!["empty".to_string(), "pair".to_string()],
    )];
    bundle.constructor_selectors = vec![
        ("empty".to_string(), Vec::new()),
        (
            "pair".to_string(),
            vec!["first".to_string(), "second".to_string()],
        ),
    ];
    bundle.term_entries.push((
        TermData::Var("empty".to_string(), 0),
        Sort::Uninterpreted("Pair".to_string()),
    ));
    bundle.term_entries.push((
        TermData::App(Symbol::named("pair"), vec![terms.true_term(); 2]),
        Sort::Uninterpreted("Pair".to_string()),
    ));
    bundle
}

fn validate(
    bundle: &SerializableProofBundle,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    validate_declaration_context_with_progress(bundle, progress)?;
    validate_declared_constructor_terms_with_progress(bundle, progress)
}

fn usage(bundle: &SerializableProofBundle) -> (usize, usize, usize) {
    let (mut work, mut bytes, mut polls) = (0usize, 0usize, 0usize);
    validate(bundle, &mut |w, b| {
        work = work.checked_add(w).expect("small fixture work");
        bytes = bytes.checked_add(b).expect("small fixture bytes");
        polls = polls.saturating_add(1);
        true
    })
    .expect("valid declaration fixture");
    (work, bytes, polls)
}

fn malformed(bundle: &SerializableProofBundle, expected: &str) {
    let result = validate(bundle, &mut |_, _| true);
    assert!(
        matches!(&result, Err(ProofCheckError::MalformedProofBundle { reason })
            if reason.contains(expected)),
        "expected {expected:?}, got {result:?}"
    );
}

#[test]
fn metered_declaration_namespace_preserves_exact_names_and_legacy_results() {
    let mut bundle = fixture();
    // Datatype names are not term symbols; neither case folding nor trimming
    // participates in identity. Derived tester spelling is exactly `is-`.
    bundle.datatype_declarations.push((
        "pair".to_string(),
        vec!["Pair".to_string(), " pair ".to_string(), "páir".to_string()],
    ));
    let symbols = validate_declaration_context_with_progress(&bundle, &mut |_, _| true)
        .expect("distinct raw identities");
    assert_eq!(symbols.len(), 12);
    assert_eq!(symbols.get("pair"), Some(&"a constructor"));
    assert_eq!(symbols.get("is-pair"), Some(&"a derived tester"));
    assert_eq!(symbols.get("first"), Some(&"a selector"));
    assert_eq!(symbols.get("is- pair "), Some(&"a derived tester"));
    assert_eq!(symbols.get("is-páir"), Some(&"a derived tester"));
    assert_eq!(validate_declaration_context(&bundle).unwrap(), symbols);
    validate_declared_constructor_terms(&bundle).expect("legacy constructor pass");
    validate(&bundle, &mut |_, _| true).expect("metered constructor pass");
}

/// The fixture with its datatype renamed to `""`, carrier sorts included.
fn empty_datatype_fixture() -> SerializableProofBundle {
    let mut bundle = fixture();
    bundle.datatype_declarations[0].0.clear();
    for (data, sort) in &mut bundle.term_entries {
        if matches!(data, TermData::Var(name, _) if name.as_str() == "empty")
            || matches!(data, TermData::App(Symbol::Named(name), _) if name.as_str() == "pair")
        {
            *sort = Sort::Uninterpreted(String::new());
        }
    }
    bundle
}

/// The fixture plus the nullary constructor `""`, its empty selector list and
/// its bound term.
fn empty_constructor_fixture() -> SerializableProofBundle {
    let mut bundle = fixture();
    bundle.datatype_declarations[0].1.push(String::new());
    bundle
        .constructor_selectors
        .push((String::new(), Vec::new()));
    bundle.term_entries.push((
        TermData::Var(String::new(), 0),
        Sort::Uninterpreted("Pair".to_string()),
    ));
    bundle
}

#[test]
fn metered_declaration_preflight_admits_empty_names_as_ordinary_identities() {
    let bundle = empty_datatype_fixture();
    validate(&bundle, &mut |_, _| true).expect("datatype `||`");

    let bundle = empty_constructor_fixture();
    let symbols = validate_declaration_context_with_progress(&bundle, &mut |_, _| true)
        .expect("constructor `||`");
    assert_eq!(symbols.get(""), Some(&"a constructor"));
    assert_eq!(symbols.get("is-"), Some(&"a derived tester"));
    validate(&bundle, &mut |_, _| true).expect("constructor `||` and its bound term");

    let mut bundle = fixture();
    bundle.constructor_selectors[1].1[0].clear();
    let symbols = validate_declaration_context_with_progress(&bundle, &mut |_, _| true)
        .expect("selector `||`");
    assert_eq!(symbols.get(""), Some(&"a selector"));
    validate(&bundle, &mut |_, _| true).expect("selector `||` and the constructor terms");
}

#[test]
fn metered_declaration_preflight_rejects_duplicate_and_cross_role_names() {
    let mut cases = Vec::new();
    let mut bundle = fixture();
    bundle
        .datatype_declarations
        .push(bundle.datatype_declarations[0].clone());
    cases.push((bundle, "datatype declaration name \"Pair\" is duplicated"));
    let mut bundle = empty_datatype_fixture();
    bundle
        .datatype_declarations
        .push((String::new(), vec!["other".to_string()]));
    cases.push((bundle, "datatype declaration name \"\" is duplicated"));
    let mut bundle = fixture();
    bundle.datatype_declarations[0].1.clear();
    cases.push((bundle, "datatype \"Pair\" has no constructors"));
    let mut bundle = fixture();
    bundle.datatype_declarations[0].1.push("empty".to_string());
    cases.push((
        bundle,
        "constructor declaration name \"empty\" is duplicated",
    ));
    let mut bundle = empty_constructor_fixture();
    bundle
        .datatype_declarations
        .push(("Other".to_string(), vec![String::new()]));
    cases.push((bundle, "constructor declaration name \"\" is duplicated"));
    let mut bundle = fixture();
    bundle.datatype_declarations[0]
        .1
        .push("is-empty".to_string());
    cases.push((bundle, "term symbol \"is-empty\" is ambiguous"));
    let mut bundle = empty_constructor_fixture();
    bundle.datatype_declarations[0].1.push("is-".to_string());
    cases.push((bundle, "term symbol \"is-\" is ambiguous"));
    let mut bundle = empty_constructor_fixture();
    bundle.constructor_selectors[1].1[0].clear();
    cases.push((bundle, "term symbol \"\" is ambiguous"));
    let mut bundle = fixture();
    bundle.constructor_selectors[0].0 = "unknown".to_string();
    cases.push((bundle, "references unknown constructor \"unknown\""));
    let mut bundle = fixture();
    bundle
        .constructor_selectors
        .push(bundle.constructor_selectors[0].clone());
    cases.push((
        bundle,
        "selector declaration for constructor \"empty\" is duplicated",
    ));
    for name in ["empty", "is-empty", "second"] {
        let mut bundle = fixture();
        bundle.constructor_selectors[1].1[0] = name.to_string();
        cases.push((bundle, "is ambiguous"));
    }
    for (bundle, expected) in cases {
        malformed(&bundle, expected);
    }
}

#[test]
fn metered_constructor_signature_preflight_keeps_sort_arity_and_symbol_semantics() {
    let mut bundle = fixture();
    let last = bundle.term_entries.len() - 1;
    bundle.term_entries[last].1 = Sort::Int;
    malformed(&bundle, "result sort outside datatype `Pair`");
    let mut bundle = fixture();
    bundle.constructor_selectors[1].1.pop();
    malformed(&bundle, "has arity 2, expected 1");
    let mut bundle = fixture();
    bundle.term_entries[last].1 = Sort::Datatype(ay_core::DatatypeSort::new(
        "Pair",
        vec![ay_core::DatatypeConstructor::unit("empty")],
    ));
    validate(&bundle, &mut |_, _| true).expect("embedded datatype carrier name");
    bundle.constructor_selectors.pop();
    validate(&bundle, &mut |_, _| true).expect("missing selector list stays unchecked here");
    bundle.term_entries[last] = (
        TermData::App(
            Symbol::indexed("empty", vec![0]),
            vec![bundle.true_term.expect("fixture preserves the true term")],
        ),
        Sort::Int,
    );
    validate(&bundle, &mut |_, _| true).expect("indexed symbols are not named constructors");
}

#[test]
fn metered_constructor_search_keeps_first_match_even_for_standalone_malformed_context() {
    let mut bundle = fixture();
    bundle
        .datatype_declarations
        .push(("Other".to_string(), vec!["pair".to_string()]));
    bundle
        .constructor_selectors
        .push(("pair".to_string(), Vec::new()));
    validate_declared_constructor_terms_with_progress(&bundle, &mut |_, _| true)
        .expect("first datatype and first selector list win exactly as before");
    assert!(validate_declaration_context(&bundle).is_err());
    bundle.datatype_declarations.swap(0, 1);
    let result = validate_declared_constructor_terms_with_progress(&bundle, &mut |_, _| true);
    assert!(
        matches!(result, Err(ProofCheckError::MalformedProofBundle { reason })
        if reason.contains("outside datatype `Other`"))
    );
}

#[test]
fn metered_declaration_preflight_can_cancel_at_every_poll_without_mutating_input() {
    let bundle = fixture();
    let original = serde_json::to_vec(&bundle).unwrap();
    let (_, _, polls) = usage(&bundle);
    for stop in 1..=polls {
        let mut calls = 0;
        let result = validate(&bundle, &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert_eq!(result, Err(ProofCheckError::ResourceLimit));
        assert_eq!(calls, stop, "no callback after refusal");
    }
    assert_eq!(serde_json::to_vec(&bundle).unwrap(), original);
}

#[test]
fn metered_declaration_preflight_charges_one_shared_exact_work_and_byte_envelope() {
    let bundle = fixture();
    let (work, bytes, _) = usage(&bundle);
    for (work_limit, byte_limit, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut used_work, mut used_bytes) = (0usize, 0usize);
        let mut progress = |w, b| {
            used_work = used_work.checked_add(w).expect("small work budget");
            used_bytes = used_bytes.checked_add(b).expect("small byte budget");
            used_work <= work_limit && used_bytes <= byte_limit
        };
        assert_eq!(validate(&bundle, &mut progress).is_ok(), accepted);
        if accepted {
            assert_eq!(
                validate(&bundle, &mut progress),
                Err(ProofCheckError::ResourceLimit)
            );
        }
    }
}

#[test]
fn metered_constructor_preflight_prices_wide_negative_and_late_match_searches() {
    let mut bundle = fixture();
    bundle.term_entries = vec![(
        TermData::Var("late".to_string(), 0),
        Sort::Uninterpreted("Wide".to_string()),
    )];
    bundle.datatype_declarations = vec![(
        "Wide".to_string(),
        (0..4_096).map(|i| format!("constructor-{i}")).collect(),
    )];
    bundle.constructor_selectors = (0..4_096)
        .map(|i| (format!("constructor-{i}"), Vec::new()))
        .collect();
    bundle.datatype_declarations[0].1.push("late".to_string());
    bundle
        .constructor_selectors
        .push(("late".to_string(), Vec::new()));
    for missing in [false, true] {
        if missing {
            bundle.datatype_declarations[0].1.pop();
        }
        let mut spent = 0usize;
        let result = validate_declared_constructor_terms_with_progress(&bundle, &mut |w, _| {
            spent += w;
            spent <= 100
        });
        assert_eq!(result, Err(ProofCheckError::ResourceLimit));
        assert!(
            spent <= 110,
            "stops at an individual comparison, not after the whole scan"
        );
    }
    // Isolate the independent wide selector search after an immediate hit.
    bundle.datatype_declarations[0].1 = vec!["late".to_string()];
    let mut spent = 0usize;
    assert_eq!(
        validate_declared_constructor_terms_with_progress(&bundle, &mut |w, _| {
            spent += w;
            spent <= 100
        }),
        Err(ProofCheckError::ResourceLimit)
    );
}

#[test]
fn metered_declaration_preflight_prices_strings_and_diagnostics_before_allocating() {
    let mut bundle = fixture();
    let long = "\u{0001}".repeat(4_096);
    bundle.datatype_declarations[0].0 = long.clone();
    let mut saw_copy = false;
    let result = validate_declaration_context_with_progress(&bundle, &mut |_, bytes| {
        saw_copy |= bytes == long.len();
        bytes != long.len()
    });
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert!(saw_copy);
    bundle.datatype_declarations[0].1.clear();
    let mut saw_diagnostic = false;
    let result = validate_declaration_context_with_progress(&bundle, &mut |work, bytes| {
        saw_diagnostic |= work >= 10 * long.len() && bytes >= work;
        bytes < 10 * long.len()
    });
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert!(saw_diagnostic);
    malformed(&bundle, "has no constructors");
}

#[test]
fn metered_declaration_table_growth_prices_existing_long_keys_before_rehash() {
    let mut names = HashSet::default();
    names.insert("long".repeat(2_048));
    let mut next = 0;
    while names.len() < names.capacity() {
        names.insert(format!("s{next}"));
        next += 1;
    }
    let mut saw_long = false;
    let mut progress = |work, _| {
        saw_long |= work >= 8_192;
        work < 8_192
    };
    let mut meter = DeclarationMeter::new(&mut progress);
    assert_eq!(
        meter.insert_name(&mut names, "new"),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(saw_long);
    assert!(!names.contains("new"));

    let mut names = HashMap::default();
    names.insert("long".repeat(2_048), "a constructor");
    let mut next = 0;
    while names.len() < names.capacity() {
        names.insert(format!("m{next}"), "a constructor");
        next += 1;
    }
    let mut saw_long = false;
    let mut progress = |work, _| {
        saw_long |= work >= 8_192;
        work < 8_192
    };
    let mut meter = DeclarationMeter::new(&mut progress);
    assert_eq!(
        insert_declaration_term_symbol(&mut names, "new", "a selector", &mut meter),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(saw_long);
    assert!(!names.contains_key("new"));
}

#[test]
fn metered_declaration_lookup_overflow_is_a_typed_resource_refusal() {
    let mut called = false;
    let mut progress = |_, _| {
        called = true;
        true
    };
    let mut meter = DeclarationMeter::new(&mut progress);
    assert_eq!(
        meter.lookup("name", usize::MAX),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(
        !called,
        "checked arithmetic refuses before a wrapped charge"
    );
}
