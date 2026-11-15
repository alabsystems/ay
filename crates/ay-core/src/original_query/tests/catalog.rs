// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn unused_definition_body_tampering_is_detected() {
    let mut a = base();
    let body = boolean(&mut a, true);
    a.declarations.push(Declaration {
        name: token("unused"),
        kind: DeclarationKind::Term {
            role: TermRole::Function,
            type_parameters: vec![],
            arguments: vec![],
            result: SortId(0),
            definition: Some(Definition {
                kind: DefinitionKind::NonRecursive,
                parameters: vec![],
                body,
            }),
        },
    });
    declare(&mut a, 0, DeclarationSyntax::DefineFun);
    let mut b = a.clone();
    b.nodes[0].kind = NodeKind::Literal(Literal {
        kind: LiteralKind::Boolean,
        text: "false".into(),
    });
    assert!(!matches(a, b));
}

#[test]
fn unused_nominal_names_cannot_be_alpha_renamed() {
    let mut a = base();
    a.declarations.push(constant("x"));
    declare(&mut a, 0, DeclarationSyntax::DeclareConst);
    let mut b = a.clone();
    b.declarations[0].name = token("y");
    assert!(!matches(a, b));
}

#[test]
fn declaration_command_head_is_not_normalized_away() {
    let mut a = base();
    a.declarations.push(constant("x"));
    declare(&mut a, 0, DeclarationSyntax::DeclareConst);
    let mut b = a.clone();
    b.commands[0] = QueryCommand::Declarations {
        syntax: DeclarationSyntax::DeclareFun,
        kind: DeclarationGroupKind::Sequential,
        entries: vec![DeclId(0)],
        synthesis: None,
    };
    assert!(!matches(a, b));
}

#[test]
fn builtin_sort_and_nominal_alias_are_distinct_authored_shapes() {
    let mut a = base();
    a.declarations.push(Declaration {
        name: token("Alias"),
        kind: DeclarationKind::SortAlias {
            parameters: vec![],
            body: SortId(0),
        },
    });
    a.sorts.push(SortNode::Nominal {
        declaration: DeclId(0),
        arguments: vec![],
    });
    declare(&mut a, 0, DeclarationSyntax::DefineSort);
    let root = node(
        &mut a,
        2,
        NodeKind::Literal(Literal {
            kind: LiteralKind::Boolean,
            text: "true".into(),
        }),
    );
    assert_root(&mut a, root);
    let mut b = a.clone();
    b.nodes[0].sort = SortId(0);
    assert!(!matches(a, b));
}

#[test]
fn builtin_operator_cannot_alias_nominal_same_spelling() {
    let mut a = base();
    a.declarations.push(constant("true"));
    declare(&mut a, 0, DeclarationSyntax::DeclareConst);
    let root = node(
        &mut a,
        0,
        NodeKind::Apply {
            operator: Operator {
                head: OperatorHead::Builtin(builtin("true")),
                indices: vec![],
                qualification: None,
            },
            arguments: vec![],
        },
    );
    assert_root(&mut a, root);
    let mut b = a.clone();
    if let NodeKind::Apply { operator, .. } = &mut b.nodes[0].kind {
        operator.head = OperatorHead::Declaration(DeclId(0));
    }
    assert!(!matches(a, b));
}

#[test]
fn type_parameters_are_scoped_and_their_arity_is_identity() {
    let make = |second: bool| {
        let mut draft = base();
        draft.sorts.push(SortNode::Parameter(TypeParameterId(0)));
        let mut parameters = vec![TypeParameter {
            id: TypeParameterId(0),
            name: token("T"),
        }];
        if second {
            parameters.push(TypeParameter {
                id: TypeParameterId(1),
                name: token("U"),
            });
        }
        draft.declarations.push(Declaration {
            name: token("Alias"),
            kind: DeclarationKind::SortAlias {
                parameters,
                body: SortId(2),
            },
        });
        declare(&mut draft, 0, DeclarationSyntax::DefineSort);
        draft
    };
    assert!(!matches(make(false), make(true)));
    let mut invalid = make(false);
    invalid.sorts[2] = SortNode::Parameter(TypeParameterId(9));
    assert!(matches!(
        refused(invalid),
        QueryError::Invalid("unbound type parameter")
    ));
}

#[test]
fn definition_environment_is_captured_before_later_declarations() {
    let mut draft = base();
    draft.declarations.push(constant("future"));
    let body = node(&mut draft, 0, NodeKind::Free(DeclId(0)));
    draft.declarations.insert(
        0,
        Declaration {
            name: token("f"),
            kind: DeclarationKind::Term {
                role: TermRole::Function,
                type_parameters: vec![],
                arguments: vec![],
                result: SortId(0),
                definition: Some(Definition {
                    kind: DefinitionKind::NonRecursive,
                    parameters: vec![],
                    body,
                }),
            },
        },
    );
    // Fix the locator to the later declaration; bodies cannot borrow final catalog visibility.
    draft.nodes[0].kind = NodeKind::Free(DeclId(1));
    declare(&mut draft, 0, DeclarationSyntax::DefineFun);
    declare(&mut draft, 1, DeclarationSyntax::DeclareConst);
    assert!(matches!(
        refused(draft),
        QueryError::Invalid("declaration is not visible at this occurrence")
    ));
}

#[test]
fn mutual_recursive_function_group_admits_only_group_forward_references() {
    let mut draft = base();
    for id in [1, 0] {
        node(&mut draft, 0, NodeKind::Free(DeclId(id)));
    }
    for (name, body) in [("f", 0), ("g", 1)] {
        draft.declarations.push(Declaration {
            name: token(name),
            kind: DeclarationKind::Term {
                role: TermRole::Function,
                type_parameters: vec![],
                arguments: vec![],
                result: SortId(0),
                definition: Some(Definition {
                    kind: DefinitionKind::Recursive,
                    parameters: vec![],
                    body: NodeId(body),
                }),
            },
        });
    }
    draft.commands.push(QueryCommand::Declarations {
        syntax: DeclarationSyntax::DefineFunsRec,
        kind: DeclarationGroupKind::RecursiveFunctions,
        entries: vec![DeclId(0), DeclId(1)],
        synthesis: None,
    });
    assert!(matches(draft.clone(), draft));
}

#[test]
fn popped_declaration_cannot_reappear_via_catalog_locator() {
    let mut draft = base();
    draft.declarations.push(constant("x"));
    draft.commands.push(scope(ScopeKind::Push));
    declare(&mut draft, 0, DeclarationSyntax::DeclareConst);
    draft.commands.push(scope(ScopeKind::Pop));
    let root = node(&mut draft, 0, NodeKind::Free(DeclId(0)));
    assert_root(&mut draft, root);
    assert!(matches!(
        refused(draft),
        QueryError::Invalid("declaration is not visible at this occurrence")
    ));
}

#[test]
fn global_lifetime_option_preserves_future_declarations_across_pop() {
    let mut draft = base();
    draft.declarations.push(constant("x"));
    draft.data.push(DataNode::Literal(Literal {
        kind: LiteralKind::Boolean,
        text: "true".into(),
    }));
    draft.commands.push(QueryCommand::SetOption {
        attribute: Attribute {
            keyword: "global-decls".into(),
            value: Some(DataId(0)),
        },
        lifetime: LifetimeEffect::Global,
    });
    draft.commands.push(scope(ScopeKind::Push));
    declare(&mut draft, 0, DeclarationSyntax::DeclareConst);
    draft.commands.push(scope(ScopeKind::Pop));
    let root = node(&mut draft, 0, NodeKind::Free(DeclId(0)));
    assert_root(&mut draft, root);
    checked(draft);
}

#[test]
fn reset_removes_global_declaration_visibility() {
    let mut draft = base();
    draft.initial_lifetime = DeclarationLifetime::Global;
    draft.declarations.push(constant("x"));
    declare(&mut draft, 0, DeclarationSyntax::DeclareConst);
    draft.commands.push(QueryCommand::Reset);
    let root = node(&mut draft, 0, NodeKind::Free(DeclId(0)));
    assert_root(&mut draft, root);
    assert!(matches!(
        refused(draft),
        QueryError::Invalid("declaration is not visible at this occurrence")
    ));
}

#[test]
fn reset_assertions_host_scope_policy_is_explicit() {
    let mut draft = base();
    draft.declarations.push(constant("x"));
    draft.commands.push(scope(ScopeKind::Push));
    declare(&mut draft, 0, DeclarationSyntax::DeclareConst);
    draft.commands.push(QueryCommand::ResetAssertions);
    let root = node(&mut draft, 0, NodeKind::Free(DeclId(0)));
    assert_root(&mut draft, root);
    assert!(matches!(
        refused(draft.clone()),
        QueryError::Invalid("declaration is not visible at this occurrence")
    ));
    draft.reset_assertions = ResetAssertionsPolicy::RetainDepthAndDeclarations;
    checked(draft);
}

#[test]
fn reset_lifetime_policy_preserves_or_restores_actual_host_behavior() {
    let mut draft = base();
    draft.initial_lifetime = DeclarationLifetime::Global;
    draft.reset_lifetime = ResetLifetimePolicy::PreserveCurrent;
    draft.declarations.push(constant("after_reset"));
    draft.commands.push(QueryCommand::Reset);
    draft.commands.push(scope(ScopeKind::Push));
    declare(&mut draft, 0, DeclarationSyntax::DeclareConst);
    draft.commands.push(scope(ScopeKind::Pop));
    let root = node(&mut draft, 0, NodeKind::Free(DeclId(0)));
    assert_root(&mut draft, root);
    checked(draft.clone());
    draft.reset_lifetime = ResetLifetimePolicy::RestoreScopedDefault;
    assert!(matches!(
        refused(draft),
        QueryError::Invalid("declaration is not visible at this occurrence")
    ));
}

#[test]
fn quoted_and_ignored_options_retain_payload_separately_from_effect() {
    let mut draft = base();
    draft.data.push(DataNode::Symbol(SymbolToken {
        kind: SymbolKind::Quoted,
        text: "true".into(),
    }));
    draft.data.push(DataNode::Literal(Literal {
        kind: LiteralKind::Numeral,
        text: "7".into(),
    }));
    draft.commands.push(QueryCommand::SetOption {
        attribute: Attribute {
            keyword: "global-declarations".into(),
            value: Some(DataId(0)),
        },
        lifetime: LifetimeEffect::Global,
    });
    draft.commands.push(QueryCommand::SetOption {
        attribute: Attribute {
            keyword: "global-decls".into(),
            value: Some(DataId(1)),
        },
        lifetime: LifetimeEffect::Unchanged,
    });
    draft.commands.push(scope(ScopeKind::Push));
    draft.declarations.push(constant("x"));
    declare(&mut draft, 0, DeclarationSyntax::DeclareConst);
    draft.commands.push(scope(ScopeKind::Pop));
    let root = node(&mut draft, 0, NodeKind::Free(DeclId(0)));
    assert_root(&mut draft, root);
    checked(draft);
}

fn synthesis(id: u32, name: &str) -> QueryDraft {
    let mut draft = base();
    let mut function = constant("synthesized");
    if let DeclarationKind::Term {
        arguments, result, ..
    } = &mut function.kind
    {
        arguments.push(SortId(1));
        *result = SortId(1);
    }
    draft.declarations.push(function);
    draft
        .data
        .push(DataNode::Reference(OperatorHead::Bound(BinderId(id))));
    draft.data.push(DataNode::List(vec![DataId(0)]));
    draft.commands.push(QueryCommand::Declarations {
        syntax: DeclarationSyntax::SynthFun,
        kind: DeclarationGroupKind::Sequential,
        entries: vec![DeclId(0)],
        synthesis: Some(SynthesisSyntax {
            parameters: vec![binder(id, name, 1)],
            grammar: Some(DataId(1)),
        }),
    });
    draft
}

#[test]
fn synthesis_formals_and_grammar_compare_under_local_alpha_environment() {
    assert!(matches(synthesis(0, "x"), synthesis(19, "argument")));
}

#[test]
fn synthesis_grammar_cannot_borrow_an_undeclared_formal() {
    let mut draft = synthesis(0, "x");
    draft.data[0] = DataNode::Reference(OperatorHead::Bound(BinderId(1)));
    assert!(matches!(
        refused(draft),
        QueryError::Invalid("unbound operator")
    ));
}

#[test]
fn synthesis_formals_remain_when_grammar_is_absent() {
    let mut draft = synthesis(0, "x");
    if let QueryCommand::Declarations {
        synthesis: Some(syntax),
        ..
    } = &mut draft.commands[0]
    {
        syntax.grammar = None;
    }
    checked(draft);
}

#[test]
fn bare_frontend_reset_assertions_clears_depth_unlike_cli_reopened_levels() {
    let mut draft = base();
    draft.reset_assertions = ResetAssertionsPolicy::ClearDepthRetainDeclarations;
    draft.declarations.push(constant("retained"));
    draft.commands.push(scope(ScopeKind::Push));
    declare(&mut draft, 0, DeclarationSyntax::DeclareConst);
    draft.commands.push(QueryCommand::ResetAssertions);
    let root = node(&mut draft, 0, NodeKind::Free(DeclId(0)));
    assert_root(&mut draft, root);
    checked(draft.clone());
    let mut cli = draft.clone();
    cli.reset_assertions = ResetAssertionsPolicy::RetainDepthAndDeclarations;
    assert!(!matches(draft.clone(), cli.clone()));
    draft.commands.insert(3, scope(ScopeKind::Pop));
    assert_eq!(refused(draft), QueryError::Invalid("scope underflow"));
    cli.commands.insert(3, scope(ScopeKind::Pop));
    checked(cli);
}
