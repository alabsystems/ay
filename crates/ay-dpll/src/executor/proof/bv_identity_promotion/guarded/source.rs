// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded syntactic expansion of authenticated source macros for proof premises.

use super::{bounded_source, FrontendTerm};
use ay_frontend::Context;

// Expansion precedes raw interning, whose ground source-work bound still
// applies. Count repeated macro uses and chain depth before cloning; a compact
// definition DAG must not allocate an exponentially large assertion tree.
pub(super) fn expand(context: &Context, root: &FrontendTerm) -> Option<FrontendTerm> {
    expand_with_definition_use(context, root).map(|(term, _)| term)
}

/// Record actual definition consumption during the existing bounded walk.
/// This is presentation metadata, never an additional source premise.
pub(super) fn expand_with_definition_use(
    context: &Context,
    root: &FrontendTerm,
) -> Option<(FrontendTerm, bool)> {
    bounded_source(root)?;
    let mut used_definition = false;
    let term = visit(
        context,
        root,
        0,
        &mut 16_384,
        &mut Vec::new(),
        &mut used_definition,
    )?;
    Some((term, used_definition))
}

fn visit(
    context: &Context,
    term: &FrontendTerm,
    depth: usize,
    remaining: &mut usize,
    active: &mut Vec<String>,
    used_definition: &mut bool,
) -> Option<FrontendTerm> {
    if depth > 96 {
        return None;
    }
    *remaining = remaining.checked_sub(1)?;
    if let FrontendTerm::Symbol(name) = term {
        if context.is_defined_fun(name) {
            let body = context.source_nullary_definition_for_proof(name)?;
            bounded_source(body)?;
            if active.contains(name) {
                return None;
            }
            *used_definition = true;
            active.push(name.clone());
            let result = visit(context, body, depth + 1, remaining, active, used_definition);
            let _ = active.pop();
            return result;
        }
        return Some(term.clone());
    }
    let mut rebuild = |args: &[FrontendTerm], remaining: &mut usize, active: &mut Vec<String>| {
        args.iter()
            .map(|arg| visit(context, arg, depth + 1, remaining, active, used_definition))
            .collect::<Option<Vec<_>>>()
    };
    Some(match term {
        FrontendTerm::App(head, args) => {
            FrontendTerm::App(head.clone(), rebuild(args, remaining, active)?)
        }
        FrontendTerm::IndexedApp(head, indices, args) => FrontendTerm::IndexedApp(
            head.clone(),
            indices.clone(),
            rebuild(args, remaining, active)?,
        ),
        FrontendTerm::QualifiedApp(head, sort, args) => FrontendTerm::QualifiedApp(
            head.clone(),
            sort.clone(),
            rebuild(args, remaining, active)?,
        ),
        FrontendTerm::Const(_) => term.clone(),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn process(context: &mut Context, text: &str) {
        for command in ay_frontend::parse(text).unwrap() {
            context.process_command(&command).unwrap();
        }
    }

    #[test]
    fn source_macros_keep_foldable_operations_and_nested_original_bodies() {
        let mut context = Context::new();
        process(&mut context, "(declare-const x (_ BitVec 8))(define-fun first () (_ BitVec 8) (bvadd x #x00))(define-fun second () (_ BitVec 8) first)(assert (= second x))");
        let (expanded, used_definition) =
            expand_with_definition_use(&context, &context.assertions_parsed()[0]).unwrap();
        assert!(used_definition);
        let mut expected = Context::new();
        process(
            &mut expected,
            "(declare-const x (_ BitVec 8))(assert (= (bvadd x #x00) x))",
        );
        assert_eq!(expanded, expected.assertions_parsed()[0]);
        let (_, used_definition) =
            expand_with_definition_use(&expected, &expected.assertions_parsed()[0]).unwrap();
        assert!(!used_definition);
    }

    #[test]
    fn recursive_and_exponential_macros_decline_before_unbounded_expansion() {
        let mut context = Context::new();
        process(
            &mut context,
            "(define-fun-rec recursive () (_ BitVec 8) #x00)",
        );
        assert!(expand(&context, &FrontendTerm::Symbol("recursive".into())).is_none());
        process(
            &mut context,
            "(declare-const x (_ BitVec 8))(define-fun a0 () (_ BitVec 8) x)",
        );
        for i in 1..15 {
            process(
                &mut context,
                &format!(
                    "(define-fun a{i} () (_ BitVec 8) (bvadd a{} a{}))",
                    i - 1,
                    i - 1
                ),
            );
        }
        assert!(expand(&context, &FrontendTerm::Symbol("a14".into())).is_none());
    }
}
