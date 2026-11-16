// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Proof, TheoryLemmaKind};

struct Fixture {
    terms: TermStore,
    base: TermId,
    indices: [TermId; 3],
    values: [TermId; 3],
}

impl Fixture {
    fn new(index_sort: Sort, value_sort: Sort) -> Self {
        let mut terms = TermStore::new();
        let base = terms.mk_var("a", Sort::array(index_sort.clone(), value_sort.clone()));
        let indices = ["i", "j", "k"].map(|s| terms.mk_var(s, index_sort.clone()));
        let values = ["u", "v", "w"].map(|s| terms.mk_var(s, value_sort.clone()));
        Self {
            terms,
            base,
            indices,
            values,
        }
    }

    fn chain(&mut self, writes: &[(usize, usize)]) -> TermId {
        let mut term = self.base;
        for &(i, v) in writes {
            term = self.terms.mk_app(
                Symbol::named("store"),
                [term, self.indices[i], self.values[v]],
                self.terms.sort(self.base).clone(),
            );
        }
        term
    }

    fn equality(&mut self, left: &[(usize, usize)], right: &[(usize, usize)]) -> TermId {
        let l = self.chain(left);
        let r = self.chain(right);
        self.terms.mk_app(Symbol::named("="), [l, r], Sort::Bool)
    }
}

#[test]
fn an_unchecked_rule_is_refused_before_the_derivation_spends_or_advances() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let mut derivation = Derivation {
        printer: &printer,
        prefix: "s".into(),
        next: 0,
        output: String::new(),
        witness: String::new(),
        selected: String::new(),
        ext: String::new(),
        not_false: String::new(),
    };
    let before_work = printer.work_used();

    assert_eq!(derivation.step("p", "invented_rule", &[]), None);
    assert_eq!(derivation.output, "");
    assert_eq!(printer.work_used(), before_work);
    assert_eq!(derivation.step("p", "refl", &[]).as_deref(), Some("s.0"));
    assert_eq!(derivation.output, "(step s.0 (cl p) :rule refl)\n");
}

fn publish(terms: &mut TermStore, equality: TermId, declarations: &str, name: &str) {
    let root = terms.mk_not_raw(equality);
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let lemma =
        proof.add_theory_lemma_with_kind("array", vec![equality], TheoryLemmaKind::ArrayRowChain);
    proof.add_resolution(vec![], equality, lemma, assume);
    crate::check_proof_strict(&proof, terms).expect("native strict validation");
    let text =
        crate::try_export_alethe_with_problem_scope_and_overrides(&proof, terms, &[root], None)
            .expect("checked Alethe lowering");
    assert!(text.contains(":rule arrays_ext") && text.contains(":rule arrays_row"));
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    let problem = format!(
        "{declarations}\n(assert {})\n(check-sat)\n",
        crate::format_term_alethe(terms, root)
    );
    let path = std::env::temp_dir().join(format!("ay-shadow-{name}-{}.json", std::process::id()));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":text})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn shadowed_writes_emit_replayable_proofs_for_aliasing_indices_and_opaque_bases() {
    for (name, index_sort, value_sort, index_text, value_text) in [
        ("int", Sort::Int, Sort::Int, "Int", "Int"),
        (
            "uninterpreted",
            Sort::Uninterpreted("Index".into()),
            Sort::Uninterpreted("Element".into()),
            "Index",
            "Element",
        ),
        (
            "bv",
            Sort::bitvec(64),
            Sort::bitvec(8),
            "(_ BitVec 64)",
            "(_ BitVec 8)",
        ),
    ] {
        for (n, (left, right)) in [
            (vec![(0, 0), (0, 2)], vec![(0, 2)]),
            (vec![(0, 0), (1, 1), (0, 2)], vec![(1, 1), (0, 2)]),
            (vec![(1, 1), (0, 2)], vec![(0, 0), (1, 1), (0, 2)]),
            (
                vec![(0, 0), (1, 0), (2, 1), (0, 2), (1, 2)],
                vec![(0, 1), (2, 1), (0, 2), (1, 2)],
            ),
        ]
        .iter()
        .enumerate()
        {
            let mut f = Fixture::new(index_sort.clone(), value_sort.clone());
            f.base = f.terms.mk_app(
                Symbol::named("opaque"),
                [f.base],
                f.terms.sort(f.base).clone(),
            );
            let eq = f.equality(left, right);
            let decl = format!("(set-logic ALL)\n(declare-fun a () (Array {index_text} {value_text}))\n(declare-fun opaque ((Array {index_text} {value_text})) (Array {index_text} {value_text}))\n{}\n{}", ["i", "j", "k"].map(|s| format!("(declare-fun {s} () {index_text})")).join("\n"), ["u", "v", "w"].map(|s| format!("(declare-fun {s} () {value_text})")).join("\n"));
            let decl = if name == "uninterpreted" {
                decl.replace(
                    "(set-logic ALL)",
                    "(set-logic ALL)\n(declare-sort Index 0)\n(declare-sort Element 0)",
                )
            } else {
                decl
            };
            publish(&mut f.terms, eq, &decl, &format!("{name}-{n}"));
        }
    }
}

#[test]
fn shadowed_store_recognizer_rejects_order_value_base_sort_and_bound_changes() {
    let mut f = Fixture::new(Sort::bitvec(64), Sort::bitvec(8));
    let original = [(0, 0), (1, 1), (0, 2)];
    for other in [
        vec![(1, 1), (0, 0)],
        vec![(0, 2), (1, 1)],
        vec![(2, 1), (0, 2)],
        vec![(0, 2)],
    ] {
        let eq = f.equality(&original, &other);
        assert!(shadowed_stores(&f.terms, &[eq]).is_none());
    }
    let good = f.equality(&original, &[(1, 1), (0, 2)]);
    assert!(shadowed_stores(&f.terms, &[good]).is_some());
    assert!(shadowed_stores(&f.terms, &[good, good]).is_none());
    let not = f.terms.mk_not_raw(good);
    assert!(shadowed_stores(&f.terms, &[not]).is_none());
    let left = f.chain(&original);
    f.base = f.terms.mk_var("other", f.terms.sort(f.base).clone());
    let right = f.chain(&[(1, 1), (0, 2)]);
    let eq = f
        .terms
        .mk_app(Symbol::named("="), [left, right], Sort::Bool);
    assert!(shadowed_stores(&f.terms, &[eq]).is_none());
    let wrong_index = f.terms.mk_var("bad", Sort::Bool);
    let bad = f.terms.mk_app(
        Symbol::named("store"),
        [f.base, wrong_index, f.values[0]],
        f.terms.sort(f.base).clone(),
    );
    let saved = f.base;
    f.base = bad;
    let left = f.chain(&[(0, 0), (0, 2)]);
    f.base = saved;
    let right = f.chain(&[(0, 2)]);
    let eq = f
        .terms
        .mk_app(Symbol::named("="), [left, right], Sort::Bool);
    assert!(shadowed_stores(&f.terms, &[eq]).is_none());
    for size in [128, 129] {
        let eq = f.equality(&vec![(0, 2); size], &[(0, 2)]);
        assert_eq!(shadowed_stores(&f.terms, &[eq]).is_some(), size == 128);
    }
}

#[test]
fn shadowed_store_printer_rejects_surface_changes_capture_and_work_exhaustion() {
    let mut f = Fixture::new(Sort::Int, Sort::Int);
    let eq = f.equality(&[(0, 0), (1, 1), (0, 2)], &[(1, 1), (0, 2)]);
    let shape = shadowed_stores(&f.terms, &[eq]).unwrap();
    for (term, text) in [
        (eq, "true"),
        (shape.left, "a"),
        (f.indices[0], "j"),
        (f.values[0], "v"),
    ] {
        let mut overrides = HashMap::default();
        overrides.insert(term, text.to_owned());
        assert!(
            AlethePrinter::new_with_overrides(&f.terms, Some(&overrides))
                .format_shadowed_stores(ProofId(5), &[eq])
                .is_none()
        );
    }
    assert!(
        AlethePrinter::new_with_overrides_and_budget(&f.terms, None, Some(1024))
            .format_shadowed_stores(ProofId(5), &[eq])
            .is_none()
    );
    f.indices[0] = f.terms.mk_var("x", Sort::Int);
    let eq = f.equality(&[(0, 0), (0, 2)], &[(0, 2)]);
    assert!(AlethePrinter::new(&f.terms)
        .format_shadowed_stores(ProofId(5), &[eq])
        .is_none());
}

#[test]
fn shadowed_store_order_is_valid_with_every_two_element_alias_assignment() {
    // Exhaustive independent array interpreter: all 3 index/value assignments
    // and all initial arrays over a two-element index and value carrier.
    let patterns = [
        (vec![(0, 0), (1, 1), (0, 2)], vec![(1, 1), (0, 2)]),
        (
            vec![(0, 0), (1, 0), (2, 1), (0, 2), (1, 2)],
            vec![(2, 1), (0, 2), (1, 2)],
        ),
    ];
    for (left, right) in patterns {
        let mut f = Fixture::new(Sort::Int, Sort::Int);
        let eq = f.equality(&left, &right);
        assert!(shadowed_stores(&f.terms, &[eq]).is_some());
        for state in 0..256 {
            let base = [state & 1, (state >> 1) & 1];
            let indices = [(state >> 2) & 1, (state >> 3) & 1, (state >> 4) & 1];
            let values = [(state >> 5) & 1, (state >> 6) & 1, (state >> 7) & 1];
            let eval = |writes: &[(usize, usize)]| {
                let mut array = base;
                for &(i, v) in writes {
                    array[indices[i]] = values[v];
                }
                array
            };
            assert_eq!(eval(&left), eval(&right));
        }
    }
}

fn raw_term(context: &mut ay_frontend::Context, term: &ay_frontend::Term) -> TermId {
    use ay_frontend::Term;
    let inferred = context.elaborate_surface_subterm(term).unwrap();
    let sort = context.terms.sort(inferred).clone();
    let (symbol, args) = match term {
        Term::Symbol(_) | Term::Const(_) => return inferred,
        Term::IndexedApp(_, _, args) if args.is_empty() => return inferred,
        Term::App(name, args) => (Symbol::named(name), args),
        Term::IndexedApp(name, indices, args) => (
            Symbol::indexed(
                name,
                indices
                    .iter()
                    .map(|i| i.as_numeral().unwrap().parse().unwrap())
                    .collect(),
            ),
            args,
        ),
        _ => panic!("unexpected fixture grammar"),
    };
    let args: Vec<_> = args.iter().map(|arg| raw_term(context, arg)).collect();
    if symbol.name() == "not" {
        context.terms.mk_not_raw(args[0])
    } else {
        context.terms.mk_app(symbol, args, sort)
    }
}

#[test]
fn shadowed_stores_prove_original_callback_public_input_projection() {
    for (name, problem) in [
        (
            "callback32",
            include_str!("shadowed_stores_fixtures/cell32-public-input.smt2"),
        ),
        (
            "callback64",
            include_str!("shadowed_stores_fixtures/cell64-public-input.smt2"),
        ),
    ] {
        let mut context = ay_frontend::Context::new();
        for command in ay_frontend::parse(problem).unwrap() {
            context.process_command(&command).unwrap();
        }
        let parsed = context.assertions_parsed().last().unwrap().clone();
        let root = raw_term(&mut context, &parsed);
        let TermData::Not(eq) = context.terms.get(root) else {
            panic!("negative equality")
        };
        let eq = *eq;
        let shape = shadowed_stores(&context.terms, &[eq]).expect("all saved bytes are shadowed");
        assert_eq!(shape.right_writes.len() - shape.left_writes.len(), 32);
        // The additional premises stay in the problem although this identity
        // is unconditional. The full callback theorem remains separate.
        let declarations = problem
            .lines()
            .filter(|line| {
                !line.starts_with("(assert (not")
                    && !line.starts_with("(check-sat")
                    && !line.starts_with("(exit")
            })
            .collect::<Vec<_>>()
            .join("\n");
        publish(&mut context.terms, eq, &declarations, name);
    }
}

#[test]
fn shadowed_store_publication_screen_spends_its_shared_allowance() {
    let mut f = Fixture::new(Sort::Int, Sort::Int);
    let eq = f.equality(&[(0, 0), (1, 1), (0, 2)], &[(1, 1), (0, 2)]);
    let mut work = 64 * 1024 * 1024;
    assert!(checked_shadowed_stores_lowering_supported(
        &f.terms,
        &[eq],
        None,
        &mut work
    ));
    assert!(work < 64 * 1024 * 1024);
    let spent = 64 * 1024 * 1024 - work;
    let mut too_small = spent - 1;
    assert!(!checked_shadowed_stores_lowering_supported(
        &f.terms,
        &[eq],
        None,
        &mut too_small
    ));
    assert_eq!(too_small, 0);
    assert!(!checked_shadowed_stores_lowering_supported(
        &f.terms,
        &[eq],
        None,
        &mut too_small
    ));
}
