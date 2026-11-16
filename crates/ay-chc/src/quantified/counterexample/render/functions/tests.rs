// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::{QuantifiedChcFunction, QuantifiedHornClause};
use crate::{CancellationToken, ChcProblem, ChcSort, ClauseBody};
use ay_core::time::Instant;
use std::time::Duration;

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(30), token)
}

fn source() -> QuantifiedChcProblem {
    QuantifiedChcProblem::new_with_functions(
        ChcProblem::new(),
        vec![
            QuantifiedChcFunction::new("ay_qcex_0".into(), vec![], ChcSort::BitVec(136)),
            QuantifiedChcFunction::new(
                "unused function".into(),
                vec![ChcSort::Bool, ChcSort::BitVec(72)],
                ChcSort::BitVec(1),
            ),
        ],
        vec![QuantifiedHornClause::new(
            HornClause::new(
                ClauseBody::new(
                    vec![],
                    Some(ChcExpr::var(ChcVar::new("local", ChcSort::Bool))),
                ),
                ClauseHead::False,
            ),
            vec![],
        )],
    )
    .unwrap()
}

#[test]
fn unused_functions_are_emitted_once_and_reserve_occurrence_names() {
    let source = source();
    let token = CancellationToken::new();
    let output = super::super::render(&source, &[0], &control(&token)).unwrap();
    assert!(output.contains("(declare-fun ay_qcex_0 () (_ BitVec 136))"));
    assert!(output.contains("(declare-fun |unused function| (Bool (_ BitVec 72)) (_ BitVec 1))"));
    assert_eq!(output.matches("(declare-fun ").count(), 2);
    assert!(output.contains("(declare-const ay_qcex_1 Bool)"));
    assert!(!output.contains("(declare-const ay_qcex_0 "));
    ay_frontend::parse(&output).unwrap();
}

#[test]
fn declaration_output_admits_the_whole_registry_before_allocating_text() {
    let source = source();
    let token = CancellationToken::new();
    let exhausted = control(&token);
    exhausted
        .bytes(64 * 1024 * 1024 - source.functions.copy_bytes() + 1)
        .unwrap();
    let mut output = Output::new(&exhausted);
    assert!(render(&source, &mut output, &exhausted).is_err());
    assert_eq!(output.finish(), "");
    assert!(exhausted.poll().is_none());
    let stopped = control(&token);
    token.cancel();
    let mut output = Output::new(&stopped);
    assert!(render(&source, &mut output, &stopped).is_err());
    token.reset();
    assert!(render(&source, &mut output, &stopped).is_err());
    assert_eq!(output.finish(), "");
    let fresh = control(&token);
    let mut output = Output::new(&fresh);
    render(&source, &mut output, &fresh).unwrap();
    assert_eq!(output.finish().matches("(declare-fun ").count(), 2);
}

#[test]
fn manifest_identifies_only_the_complete_global_function_declaration_segment() {
    let source = source();
    let token = CancellationToken::new();
    let rendered =
        super::super::render_with_bindings(&source, &[0], &[vec![]], &control(&token)).unwrap();
    let segment = &rendered.function_declarations;
    assert_eq!(
        &rendered.obligation[segment.clone()],
        "(declare-fun ay_qcex_0 () (_ BitVec 136))\n\
         (declare-fun |unused function| (Bool (_ BitVec 72)) (_ BitVec 1))\n",
    );
    assert_eq!(&rendered.obligation[..segment.start], "(set-logic ALL)\n");
    let suffix = &rendered.obligation[segment.end..];
    assert!(suffix.starts_with("(declare-const ay_qcex_1 Bool)\n"));
    assert!(suffix.ends_with("(check-sat)\n"));
    assert_eq!(rendered.bindings.len(), 1);
    assert_eq!(
        rendered.obligation,
        super::super::render(&source, &[0], &control(&token)).unwrap(),
    );
}
