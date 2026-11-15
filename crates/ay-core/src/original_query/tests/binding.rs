// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn quantified(outer: u32, inner: u32, capture: bool, names: (&str, &str)) -> QueryDraft {
    let mut draft = base();
    let body = node(
        &mut draft,
        0,
        NodeKind::Bound(BinderId(if capture { inner } else { outer })),
    );
    let nested = node(
        &mut draft,
        0,
        NodeKind::Quantified {
            quantifier: Quantifier::Exists,
            binders: vec![binder(inner, names.1, 0)],
            body,
        },
    );
    let root = node(
        &mut draft,
        0,
        NodeKind::Quantified {
            quantifier: Quantifier::Forall,
            binders: vec![binder(outer, names.0, 0)],
            body: nested,
        },
    );
    assert_root(&mut draft, root);
    draft
}

#[test]
fn alpha_renamed_bound_names_match_across_arenas() {
    assert!(matches(
        quantified(0, 1, false, ("x", "y")),
        quantified(91, 73, false, ("outer", "inner"))
    ));
}

#[test]
fn captured_inner_reference_does_not_match_outer_reference() {
    assert!(!matches(
        quantified(0, 1, false, ("x", "x")),
        quantified(91, 73, true, ("x", "x"))
    ));
}

fn simultaneous(first: u32, second: u32, third: u32, sibling_rhs: bool) -> QueryDraft {
    let mut draft = base();
    let outside = node(&mut draft, 0, NodeKind::Bound(BinderId(first)));
    let inside = node(&mut draft, 0, NodeKind::Bound(BinderId(second)));
    let let_node = node(
        &mut draft,
        0,
        NodeKind::Let {
            bindings: vec![
                LetBinding {
                    binder: binder(second, "x", 0),
                    value: outside,
                },
                LetBinding {
                    binder: binder(third, "y", 0),
                    value: if sibling_rhs { inside } else { outside },
                },
            ],
            body: inside,
        },
    );
    let root = node(
        &mut draft,
        0,
        NodeKind::Quantified {
            quantifier: Quantifier::Forall,
            binders: vec![binder(first, "x", 0)],
            body: let_node,
        },
    );
    assert_root(&mut draft, root);
    draft
}

#[test]
fn simultaneous_let_shadowing_keeps_rhs_in_incoming_environment() {
    assert!(matches(
        simultaneous(0, 1, 2, false),
        simultaneous(10, 20, 30, false)
    ));
    assert!(matches!(
        refused(simultaneous(0, 1, 2, true)),
        QueryError::Invalid("unbound variable or binder sort mismatch")
    ));
}

#[test]
fn shared_nodes_are_compared_under_each_complete_binder_environment() {
    let make = |left: bool| {
        let mut draft = base();
        let ids = if left { [0, 1] } else { [8, 9] };
        let shared = node(
            &mut draft,
            0,
            NodeKind::Bound(BinderId(if left { 0 } else { 9 })),
        );
        let bad = node(
            &mut draft,
            0,
            NodeKind::Quantified {
                quantifier: Quantifier::Forall,
                binders: vec![binder(ids[0], "a", 0), binder(ids[1], "b", 0)],
                body: shared,
            },
        );
        let good = node(
            &mut draft,
            0,
            NodeKind::Quantified {
                quantifier: Quantifier::Forall,
                binders: vec![binder(if left { 0 } else { 9 }, "c", 0)],
                body: shared,
            },
        );
        // The equal tail is processed first; a node-only memo would hide mismatch.
        assert_root(&mut draft, bad);
        assert_root(&mut draft, good);
        draft
    };
    assert!(!matches(make(true), make(false)));
}

#[test]
fn binder_scope_cannot_leak_from_a_prior_assertion() {
    let mut draft = quantified(0, 1, false, ("x", "y"));
    assert_root(&mut draft, NodeId(0));
    assert!(matches!(
        refused(draft),
        QueryError::Invalid("unbound variable or binder sort mismatch")
    ));
}

#[test]
fn forall_exists_and_lambda_are_distinct_forms() {
    let a = quantified(0, 1, false, ("x", "y"));
    let mut b = a.clone();
    if let NodeKind::Quantified { quantifier, .. } = &mut b.nodes[2].kind {
        *quantifier = Quantifier::Lambda;
    }
    assert!(!matches(a, b));
}

#[test]
fn annotation_wrapper_and_ordered_payload_are_not_erased() {
    let mut a = base();
    a.data.push(DataNode::Symbol(SymbolToken {
        kind: SymbolKind::Quoted,
        text: "forall".into(),
    }));
    let body = boolean(&mut a, true);
    let root = node(
        &mut a,
        0,
        NodeKind::Annotated {
            body,
            attributes: vec![Attribute {
                keyword: "named".into(),
                value: Some(DataId(0)),
            }],
        },
    );
    assert_root(&mut a, root);
    let mut b = a.clone();
    b.data[0] = DataNode::Symbol(token("forall"));
    assert!(!matches(a.clone(), b));
    let mut b = a.clone();
    b.commands[0] = QueryCommand::Roots {
        kind: RootKind::Assert,
        roots: vec![body],
        attributes: vec![],
    };
    assert!(!matches(a, b));
}

#[test]
fn resolved_annotation_references_follow_alpha_renamed_binder_scope() {
    let make = |id, name: &str| {
        let mut draft = base();
        draft
            .data
            .push(DataNode::Reference(OperatorHead::Bound(BinderId(id))));
        draft.data.push(DataNode::List(vec![DataId(0)]));
        let body = boolean(&mut draft, true);
        let annotated = node(
            &mut draft,
            0,
            NodeKind::Annotated {
                body,
                attributes: vec![Attribute {
                    keyword: "pattern".into(),
                    value: Some(DataId(1)),
                }],
            },
        );
        let root = node(
            &mut draft,
            0,
            NodeKind::Quantified {
                quantifier: Quantifier::Forall,
                binders: vec![binder(id, name, 0)],
                body: annotated,
            },
        );
        assert_root(&mut draft, root);
        draft
    };
    assert!(matches(make(0, "x"), make(17, "y")));
}

#[test]
fn resolved_annotation_reference_cannot_borrow_an_unrelated_root_scope() {
    let mut draft = base();
    draft
        .data
        .push(DataNode::Reference(OperatorHead::Bound(BinderId(0))));
    draft.typing.push(Attribute {
        keyword: "forged-pattern".into(),
        value: Some(DataId(0)),
    });
    assert!(matches!(
        refused(draft),
        QueryError::Invalid("unbound operator")
    ));
}

#[test]
fn unused_polymorphic_identity_definition_has_type_and_term_alpha_scopes() {
    let make = |type_id, term_id, type_name: &str, term_name: &str| {
        let mut draft = base();
        draft
            .sorts
            .push(SortNode::Parameter(TypeParameterId(type_id)));
        let body = node(&mut draft, 2, NodeKind::Bound(BinderId(term_id)));
        draft.declarations.push(Declaration {
            name: token("identity"),
            kind: DeclarationKind::Term {
                role: TermRole::Function,
                type_parameters: vec![TypeParameter {
                    id: TypeParameterId(type_id),
                    name: token(type_name),
                }],
                arguments: vec![SortId(2)],
                result: SortId(2),
                definition: Some(Definition {
                    kind: DefinitionKind::NonRecursive,
                    parameters: vec![binder(term_id, term_name, 2)],
                    body,
                }),
            },
        });
        declare(&mut draft, 0, DeclarationSyntax::DefineFun);
        draft
    };
    assert!(matches(make(0, 1, "T", "x"), make(19, 91, "A", "argument")));
}
