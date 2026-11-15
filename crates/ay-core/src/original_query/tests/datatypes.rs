// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn datatype() -> QueryDraft {
    let mut draft = base();
    draft.sorts.push(SortNode::Parameter(TypeParameterId(0)));
    draft.sorts.push(SortNode::Nominal {
        declaration: DeclId(0),
        arguments: vec![SortId(2)],
    });
    draft.sorts.push(SortNode::Nominal {
        declaration: DeclId(0),
        arguments: vec![SortId(1)],
    });
    let parameter = TypeParameter {
        id: TypeParameterId(0),
        name: token("T"),
    };
    draft.declarations.push(Declaration {
        name: token("Box"),
        kind: DeclarationKind::Datatype {
            parameters: vec![parameter.clone()],
            constructors: vec![DeclId(1)],
        },
    });
    draft.declarations.push(Declaration {
        name: token("box"),
        kind: DeclarationKind::Term {
            role: TermRole::Constructor(DeclId(0)),
            type_parameters: vec![parameter.clone()],
            arguments: vec![SortId(2)],
            result: SortId(3),
            definition: None,
        },
    });
    draft.declarations.push(Declaration {
        name: token("value"),
        kind: DeclarationKind::Term {
            role: TermRole::Selector {
                constructor: DeclId(1),
                field: 0,
            },
            type_parameters: vec![parameter],
            arguments: vec![SortId(3)],
            result: SortId(2),
            definition: None,
        },
    });
    draft.commands.push(QueryCommand::Declarations {
        syntax: DeclarationSyntax::DeclareDatatype,
        kind: DeclarationGroupKind::MutualDatatypes,
        entries: vec![DeclId(0), DeclId(1), DeclId(2)],
        synthesis: None,
    });
    draft
}

fn matching_case(pattern: MatchPattern) -> QueryDraft {
    let mut draft = datatype();
    let value = node(
        &mut draft,
        1,
        NodeKind::Literal(Literal {
            kind: LiteralKind::Numeral,
            text: "0".into(),
        }),
    );
    let scrutinee = node(
        &mut draft,
        4,
        NodeKind::Apply {
            operator: Operator {
                head: OperatorHead::Declaration(DeclId(1)),
                indices: vec![],
                qualification: Some(SortId(4)),
            },
            arguments: vec![value],
        },
    );
    let body = boolean(&mut draft, true);
    let root = node(
        &mut draft,
        0,
        NodeKind::Match {
            scrutinee,
            cases: vec![MatchCase { pattern, body }],
        },
    );
    assert_root(&mut draft, root);
    draft
}

#[test]
fn constructor_pattern_is_distinct_from_variable_default() {
    let constructor = MatchPattern::Constructor {
        declaration: DeclId(1),
        fields: vec![PatternField::Binder(binder(0, "x", 1))],
    };
    let variable = MatchPattern::Variable(binder(0, "x", 4));
    assert!(!matches(
        matching_case(constructor),
        matching_case(variable)
    ));
}

#[test]
fn constructor_field_wildcard_is_not_an_alpha_renamable_binder() {
    let wildcard = MatchPattern::Constructor {
        declaration: DeclId(1),
        fields: vec![PatternField::Wildcard(SortId(1))],
    };
    let named = MatchPattern::Constructor {
        declaration: DeclId(1),
        fields: vec![PatternField::Binder(binder(0, "_", 1))],
    };
    assert!(!matches(matching_case(wildcard), matching_case(named)));
}

#[test]
fn default_wildcard_is_distinct_from_variable_default() {
    assert!(!matches(
        matching_case(MatchPattern::Wildcard),
        matching_case(MatchPattern::Variable(binder(0, "x", 4)))
    ));
}

#[test]
fn unused_polymorphic_datatype_selector_tampering_is_detected() {
    let a = datatype();
    let mut b = a.clone();
    if let DeclarationKind::Term { result, .. } = &mut b.declarations[2].kind {
        *result = SortId(1);
    }
    assert!(!matches(a, b));
}

#[test]
fn datatype_constructor_ownership_is_checked() {
    let mut draft = datatype();
    if let DeclarationKind::Term { role, .. } = &mut draft.declarations[1].kind {
        *role = TermRole::Constructor(DeclId(2));
    }
    assert!(matches!(refused(draft), QueryError::Invalid(_)));
}

#[test]
fn mutual_datatype_templates_may_reference_each_others_nominal_sorts() {
    let mut draft = base();
    draft.sorts.push(SortNode::Nominal {
        declaration: DeclId(0),
        arguments: vec![],
    });
    draft.sorts.push(SortNode::Nominal {
        declaration: DeclId(1),
        arguments: vec![],
    });
    for (name, constructor) in [("A", 2), ("B", 3)] {
        draft.declarations.push(Declaration {
            name: token(name),
            kind: DeclarationKind::Datatype {
                parameters: vec![],
                constructors: vec![DeclId(constructor)],
            },
        });
    }
    for (name, owner, input, result) in [("mkA", 0, 3, 2), ("mkB", 1, 2, 3)] {
        draft.declarations.push(Declaration {
            name: token(name),
            kind: DeclarationKind::Term {
                role: TermRole::Constructor(DeclId(owner)),
                type_parameters: vec![],
                arguments: vec![SortId(input)],
                result: SortId(result),
                definition: None,
            },
        });
    }
    draft.commands.push(QueryCommand::Declarations {
        syntax: DeclarationSyntax::DeclareDatatypes,
        kind: DeclarationGroupKind::MutualDatatypes,
        entries: (0..4).map(DeclId).collect(),
        synthesis: None,
    });
    assert!(matches(draft.clone(), draft));
}
