// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{parse, Command};

fn source(text: &str) -> Term {
    let commands = parse(&format!("(assert {text})")).unwrap();
    let Command::Assert(term) = &commands[0] else {
        panic!("assertion")
    };
    term.clone()
}

fn commands(context: &mut Context, text: &str) {
    for command in parse(text).unwrap() {
        context.process_command(&command).unwrap();
    }
}

fn context(text: &str) -> Context {
    let mut context = Context::new();
    commands(&mut context, text);
    context
}

fn limits() -> SharedSurfaceLimits {
    SharedSurfaceLimits {
        distinct_nodes: 16_384,
        depth: 96,
        node_visits: 1_048_576,
        token_visits: 8 * 1024 * 1024,
    }
}

fn batch<'a>(context: &mut Context, term: &'a Term) -> Option<SharedSurfaceElaboration<'a>> {
    context.elaborate_shared_surface(term, limits(), |_| false)
}

#[test]
fn exact_syntax_shares_ordinary_typing_without_canonical_source_equality() {
    let mut context = context("(declare-const x (_ BitVec 8))");
    let term = source("(and (= (bvadd x #x00) x) (= (bvadd x #x00) x))");
    let expected = context.elaborate_surface_subterm(&term).unwrap();
    let result = batch(&mut context, &term).unwrap();
    assert_eq!(result.canonical(&context, &term), Some(expected));
    let Term::App(_, conjuncts) = &term else {
        panic!("and")
    };
    assert_eq!(
        result.node_index(&context, &conjuncts[0]),
        result.node_index(&context, &conjuncts[1])
    );
    let Term::App(_, sides) = &conjuncts[0] else {
        panic!("equality")
    };
    assert_ne!(
        result.node_index(&context, &sides[0]),
        result.node_index(&context, &sides[1])
    );
    assert_eq!(
        result.canonical(&context, &sides[0]),
        result.canonical(&context, &sides[1])
    );
    assert_eq!(
        result.canonical(&context, &term.clone()),
        None,
        "foreign equal AST has no pointer custody"
    );
}

#[test]
fn ordinary_arity_width_and_skipped_branch_checks_remain_authoritative() {
    let mut context = context("(declare-const x (_ BitVec 8))");
    for text in [
        "(bvadd x)",
        "(bvadd x #b0)",
        "((_ extract 8 0) x)",
        "(ite true x #b0)",
        "(ite false missing x)",
        "(ite true x (bvadd x))",
        "(ite true x (ite false #b0 x))",
    ] {
        assert!(batch(&mut context, &source(text)).is_none(), "{text}");
        assert!(context.shared_surface.0.is_none());
    }
    let term = source("(ite true x (bvnot x))");
    assert!(batch(&mut context, &term).is_some());
}

#[test]
fn declaration_shadowing_and_qualified_const_keep_ordinary_head_identity() {
    let mut declared =
        context("(declare-fun const ((_ BitVec 8)) (Array (_ BitVec 8) (_ BitVec 8)))");
    let term = source("((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00)");
    let expected = declared.elaborate_surface_subterm(&term).unwrap();
    let result = batch(&mut declared, &term).unwrap();
    assert_eq!(result.canonical(&declared, &term), Some(expected));
    let ay_core::term::TermData::App(head, _) = declared.terms.get(expected) else {
        panic!("declared const")
    };
    assert_eq!(head.name(), "const");
    let mut builtin = Context::new();
    let builtin_term = builtin.elaborate_surface_subterm(&term).unwrap();
    assert!(batch(&mut builtin, &term).is_some());
    assert_ne!(
        format!("{:?}", builtin.terms.get(builtin_term)),
        format!("{:?}", declared.terms.get(expected))
    );

    let mut shadowed = context("(declare-fun rem ((_ BitVec 8) (_ BitVec 8)) Bool)");
    let term = source("(rem #x00 #x00)");
    let expected = shadowed.elaborate_surface_subterm(&term).unwrap();
    let result = batch(&mut shadowed, &term).unwrap();
    assert_eq!(result.canonical(&shadowed, &term), Some(expected));
    assert_eq!(shadowed.terms.sort(expected), &Sort::Bool);
}

#[test]
fn defined_and_adopted_heads_including_qualified_const_are_refused() {
    let mut defined = context("(define-fun const ((x (_ BitVec 8))) (Array (_ BitVec 8) (_ BitVec 8)) ((as const (Array (_ BitVec 8) (_ BitVec 8))) x))");
    let term = source("((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00)");
    assert!(defined.is_defined_fun("const"));
    assert!(batch(&mut defined, &term).is_none());
    let mut adopted = context("(declare-fun f ((_ BitVec 8)) (_ BitVec 8)) (assert (forall ((x (_ BitVec 8))) (= (f x) x)))");
    assert!(adopted.adopted_macro_interp("f").is_some());
    assert!(batch(&mut adopted, &source("(f #x00)")).is_none());
    let mut plain = Context::new();
    for text in [
        "(let ((x true)) x)",
        "(forall ((x Bool)) x)",
        "(! true :named tag)",
    ] {
        assert!(batch(&mut plain, &source(text)).is_none());
    }
}

#[test]
fn fresh_producing_identical_occurrences_are_never_merged() {
    let mut context = context("(declare-const x Real)");
    let term = source("(^ x (- (bv2nat #b1)))");
    let before = context.terms.var_counter();
    let first = context
        .elaborate_surface_subterm(&term)
        .expect("negative integer power");
    let second = context.elaborate_surface_subterm(&term).unwrap();
    assert_ne!(
        first, second,
        "ordinary occurrences mint independent underspecified values"
    );
    assert_eq!(context.terms.var_counter(), before + 2);
    let duplicate = Term::App("=".into(), vec![term.clone(), term]);
    assert!(batch(&mut context, &duplicate).is_none());
    assert!(context.shared_surface.0.is_none());
}

#[test]
fn batch_allows_ordinary_append_but_refuses_foreign_rollback_replacement_and_metadata() {
    let term = source("(bvnot #x00)");
    let mut context = Context::new();
    let checkpoint = context.terms.rollback_checkpoint();
    let result = batch(&mut context, &term).unwrap();
    assert!(result.canonical(&context, &term).is_some());
    let _ = context
        .terms
        .mk_app(ay_core::Symbol::named("unrelated"), [], Sort::Bool);
    assert!(
        result.canonical(&context, &term).is_some(),
        "ordinary appends preserve the universe"
    );
    assert!(result.canonical(&context.clone(), &term).is_none());
    context.terms.rollback_to(checkpoint);
    assert!(result.canonical(&context, &term).is_none());
    let result = batch(&mut context, &term).unwrap();
    context.terms = context.terms.clone();
    assert!(result.canonical(&context, &term).is_none());
    let result = batch(&mut context, &term).unwrap();
    context.terms.mark_to_real_shadowed();
    assert!(result.canonical(&context, &term).is_none());
}

#[test]
fn compaction_retires_batches_even_when_the_canonical_term_survives() {
    let term = source("(bvnot #x00)");
    let mut context = Context::new();
    let result = batch(&mut context, &term).unwrap();
    let canonical = result.canonical(&context, &term).unwrap();
    let _ = context.terms.mark_and_compact(&[canonical]);
    assert!(result.canonical(&context, &term).is_none());

    let result = batch(&mut context, &term).expect("fresh batch after arena compaction");
    assert!(context.compact_terms_for_derived_query());
    assert!(result.canonical(&context, &term).is_none());
    assert!(batch(&mut context, &term).is_some());
}

#[test]
fn declaration_scope_reset_and_typing_policy_changes_retire_batches() {
    let term = source("true");
    for command in [
        "(push 1)",
        "(pop 1)",
        "(reset)",
        "(declare-const fresh Bool)",
    ] {
        let mut context = context("(push 1)");
        let result = batch(&mut context, &term).unwrap();
        commands(&mut context, command);
        assert!(result.canonical(&context, &term).is_none(), "{command}");
    }
    let mut context = context("(declare-const i Int) (declare-const r Real)");
    let term = source("(+ i r)");
    let result = batch(&mut context, &term).expect("enabled coercions");
    commands(&mut context, "(set-option :int-real-coercions false)");
    assert!(result.canonical(&context, &term).is_none());
    assert!(context.elaborate_surface_subterm(&term).is_none());
}

#[test]
fn interrupted_error_and_caught_panic_leave_no_partial_session_and_clone_is_empty() {
    let mut context = Context::new();
    let term = source("(and true false)");
    let mut saw_partial = false;
    assert!(context
        .elaborate_shared_surface(&term, limits(), |context| {
            if let Some(active) = &context.shared_surface.0 {
                assert!(context.clone().shared_surface.0.is_none());
                if active.canonical.iter().any(Option::is_some) {
                    saw_partial = true;
                    return true;
                }
            }
            false
        })
        .is_none());
    assert!(saw_partial);
    assert!(context.shared_surface.0.is_none());
    assert!(batch(&mut context, &source("(and true missing)")).is_none());
    assert!(context.shared_surface.0.is_none());
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        context.elaborate_shared_surface(&term, limits(), |context| {
            assert!(context.shared_surface.0.is_none(), "active attempt fixture");
            false
        });
    }));
    assert!(panic.is_err());
    assert!(context.shared_surface.0.is_none());
    assert!(batch(&mut context, &term).is_some());
    assert!(context.elaborate_surface_subterm(&term).is_some());
}

#[test]
fn unchanged_depth_distinct_and_actual_work_envelopes_refuse() {
    let mut context = Context::new();
    let term = source("(bvnot #x00)");
    for bound in [
        SharedSurfaceLimits {
            distinct_nodes: 1,
            ..limits()
        },
        SharedSurfaceLimits {
            depth: 0,
            ..limits()
        },
        SharedSurfaceLimits {
            node_visits: 1,
            ..limits()
        },
        SharedSurfaceLimits {
            token_visits: 1,
            ..limits()
        },
    ] {
        assert!(context
            .elaborate_shared_surface(&term, bound, |_| false)
            .is_none());
    }
    let term = source("(and true false)");
    // Input is three nodes; the ordinary shared dispatch also visits children.
    let bound = SharedSurfaceLimits {
        node_visits: 3,
        ..limits()
    };
    assert!(context
        .elaborate_shared_surface(&term, bound, |_| false)
        .is_none());
}

#[test]
fn bounded_wide_repetition_shares_but_repeated_connective_inspection_is_still_capped() {
    let mut context = Context::new();
    let leaves = (0..128)
        .map(|index| source(if index % 2 == 0 { "true" } else { "false" }))
        .collect();
    let inner = Term::App("and".into(), leaves);
    let wide = Term::App("and".into(), vec![inner; 128]);
    let result = batch(&mut context, &wide)
        .expect("shallow wide repetition stays in the unchanged envelope");
    assert_eq!(result.len(), 4);
    assert_eq!(
        result.canonical(&context, &wide),
        Some(context.terms.false_term())
    );

    let mut chain = source("true");
    for _ in 0..94 {
        let mut arguments = vec![source("true"); 127];
        arguments.push(chain);
        chain = Term::App("and".into(), arguments);
    }
    let source = Term::App("and".into(), vec![chain; 3]);
    // Under depth 96 and only 96 exact shapes, but connected source scans at
    // every distinct ancestor still do real repeated work. They remain capped.
    assert!(batch(&mut context, &source).is_none());
    assert!(context.shared_surface.0.is_none());
}

#[test]
fn shared_skipped_sort_keeps_numeric_join_and_refuses_wrong_untaken_sort() {
    let mut context = context("(declare-const i Int) (declare-const r Real)");
    for text in ["(ite true i r)", "(ite false i r)"] {
        let term = source(text);
        let expected = context
            .with_skip_journal(&term, |context| context.elaborate_surface_subterm(&term))
            .unwrap();
        let result = batch(&mut context, &term).unwrap();
        assert_eq!(result.canonical(&context, &term), Some(expected));
        assert_eq!(context.terms.sort(expected), &Sort::Real);
    }
    for text in ["(ite true i true)", "(ite false false r)"] {
        let term = source(text);
        assert!(context
            .with_skip_journal(&term, |context| context.elaborate_surface_subterm(&term))
            .is_none());
        assert!(batch(&mut context, &term).is_none());
    }
}

#[test]
fn ordinary_gathered_connectives_still_check_original_skipped_branches_and_labels() {
    for text in [
        "(ite true true #b0)",
        "(ite true true (! #b0 :named skipped))",
    ] {
        let mut term = source(text);
        for _ in 0..2_000 {
            term = Term::App("and".into(), vec![term, source("true")]);
        }
        let mut context = Context::new();
        assert!(
            context.process_command(&Command::Assert(term)).is_err(),
            "{text}"
        );
    }
    let mut term = source("(ite true true (! false :named skipped))");
    for _ in 0..2_000 {
        term = Term::App("and".into(), vec![term, source("true")]);
    }
    let mut context = Context::new();
    context.process_command(&Command::Assert(term)).unwrap();
    let named = source("skipped");
    assert!(
        context.elaborate_surface_subterm(&named).is_some(),
        "the skipped label remains bound after gathering"
    );
}

#[test]
fn logic_sort_signature_policy_changes_retire_existing_batches() {
    let mut context = context("(set-logic QF_UF)");
    let term = source("(bvnot #x00)");
    let result =
        batch(&mut context, &term).expect("logic signature enforcement initially disabled");
    context.set_enforce_logic_sort_signatures(false);
    assert!(
        result.canonical(&context, &term).is_some(),
        "unchanged policy keeps the batch live"
    );
    context.set_enforce_logic_sort_signatures(true);
    assert!(result.canonical(&context, &term).is_none());
    assert!(context.elaborate_surface_subterm(&term).is_none());
}

#[test]
fn completed_batches_and_new_attempts_refuse_active_command_windows() {
    let mut context = context("(declare-const x (_ BitVec 8))");
    let term = source("(= x #x00)");
    let checked = batch(&mut context, &term).unwrap();
    let window = source("(ite true #x00 #xff)");
    context.with_skip_journal(&window, |context| {
        assert!(context.skip_journal.is_some());
        assert!(checked.canonical(context, &term).is_none());
        assert!(batch(context, &term).is_none());
    });
    context.label_journal = Some(super::super::named_labels::LabelJournal::default());
    assert!(checked.canonical(&context, &term).is_none());
    assert!(batch(&mut context, &term).is_none());
    context.label_journal = None;
    assert!(checked.canonical(&context, &term).is_some());

    let next = source("(bvnot #x00)");
    let mut saw_active = false;
    assert!(context
        .elaborate_shared_surface(&next, limits(), |context| {
            if context.shared_surface.0.is_some() {
                saw_active = true;
                assert!(checked.canonical(context, &term).is_none());
            }
            false
        })
        .is_some());
    assert!(saw_active);
    assert!(checked.canonical(&context, &term).is_some());
}

#[test]
fn every_scalar_option_write_retires_batches_without_comparing_option_payloads() {
    let term = source("true");
    let mut context = Context::new();
    for command in [
        "(set-option :inert-cache-policy \"same\")",
        "(set-option :inert-cache-policy \"same\")",
        "(set-option :global-decls true)",
        "(set-option :global-declarations true)",
        "(set-option :numeral-as-real true)",
        "(set-option :int-real-coercions false)",
    ] {
        let checked = batch(&mut context, &term).unwrap();
        let stamp = context.source_context_stamp();
        let revision = context.elaboration_revision;
        commands(&mut context, command);
        assert_eq!(context.source_context_stamp(), stamp, "{command}");
        assert_ne!(context.elaboration_revision, revision, "{command}");
        assert!(checked.canonical(&context, &term).is_none(), "{command}");
    }
    let checked = batch(&mut context, &term).unwrap();
    let clone = context.clone();
    assert!(checked.canonical(&clone, &term).is_none());
    commands(&mut context, "(reset)");
    assert!(checked.canonical(&context, &term).is_none());
}

#[test]
fn large_inert_option_does_not_add_per_node_copy_or_comparison_work() {
    let term = source(&format!("(and {})", vec!["(= #x00 #x00)"; 64].join(" ")));
    let mut context = Context::new();
    let mut work = Work::default();
    assert!(context
        .elaborate_shared_surface(&term, limits(), |context| {
            if let Some(active) = &context.shared_surface.0 {
                work = active.work.get();
            }
            false
        })
        .is_some());
    commands(
        &mut context,
        &format!(
            "(set-option :inert-cache-policy \"{}\")",
            "v".repeat(1024 * 1024)
        ),
    );
    let mut with_option = Work::default();
    let checked = context
        .elaborate_shared_surface(&term, limits(), |context| {
            if let Some(active) = &context.shared_surface.0 {
                with_option = active.work.get();
            }
            false
        })
        .unwrap();
    assert_eq!(
        (work.nodes, work.tokens),
        (with_option.nodes, with_option.tokens)
    );
    assert!(checked.canonical(&context, &term).is_some());
}

#[test]
fn host_policy_and_session_markers_are_part_of_the_same_typing_environment() {
    let mutations: [fn(&mut Context); 8] = [
        |c| c.numeral_as_real = !c.numeral_as_real,
        |c| c.int_real_coercions = !c.int_real_coercions,
        |c| c.strict_logic_compliance = !c.strict_logic_compliance,
        |c| c.enforce_logic_sort_signatures = !c.enforce_logic_sort_signatures,
        |c| c.z3_mode = !c.z3_mode,
        |c| c.lenient_sort_coercions = !c.lenient_sort_coercions,
        |c| c.multivar_lambda_curry_allowed = !c.multivar_lambda_curry_allowed,
        Context::note_z3_session_started,
    ];
    for mutate in mutations {
        let mut context = Context::new();
        let term = source("true");
        let checked = batch(&mut context, &term).unwrap();
        let revision = context.elaboration_revision;
        mutate(&mut context);
        assert_eq!(context.elaboration_revision, revision);
        assert!(checked.canonical(&context, &term).is_none());
    }
}

#[test]
fn exact_source_sharing_keeps_overloads_and_refuses_context_sensitive_numerals() {
    let mut context =
        context("(declare-fun f ((_ BitVec 8)) Bool) (declare-fun f ((_ BitVec 16)) Bool)");
    let term = source("(and (f #x00) (f #x0000))");
    let checked = batch(&mut context, &term).unwrap();
    let Term::App(_, args) = &term else {
        panic!("and")
    };
    assert_ne!(
        checked.canonical(&context, &args[0]),
        checked.canonical(&context, &args[1])
    );
    for text in ["0", "(+ 0 0)", "(bvadd #x00 #x0000)", "(f #x00000000)"] {
        assert!(batch(&mut context, &source(text)).is_none(), "{text}");
    }
}
