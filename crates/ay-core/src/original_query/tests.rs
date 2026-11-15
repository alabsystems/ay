// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::ops::ControlFlow;

mod binding;
mod catalog;
mod datatypes;
mod indexed;
mod resources;
mod scope_identity;

fn token(text: &str) -> SymbolToken {
    SymbolToken {
        kind: SymbolKind::Simple,
        text: text.into(),
    }
}

fn builtin(text: &str) -> Builtin {
    Builtin {
        family: BuiltinFamily::Core,
        symbol: token(text),
    }
}

fn base() -> QueryDraft {
    QueryDraft {
        sorts: vec![
            SortNode::Builtin {
                head: builtin("Bool"),
                indices: vec![],
                arguments: vec![],
            },
            SortNode::Builtin {
                head: Builtin {
                    family: BuiltinFamily::Arithmetic,
                    symbol: token("Int"),
                },
                indices: vec![],
                arguments: vec![],
            },
        ],
        ..QueryDraft::default()
    }
}

fn node(draft: &mut QueryDraft, sort: u32, kind: NodeKind) -> NodeId {
    let id = NodeId(draft.nodes.len() as u32);
    draft.nodes.push(TypedNode {
        sort: SortId(sort),
        kind,
    });
    id
}

fn boolean(draft: &mut QueryDraft, value: bool) -> NodeId {
    node(
        draft,
        0,
        NodeKind::Literal(Literal {
            kind: LiteralKind::Boolean,
            text: value.to_string(),
        }),
    )
}

fn binder(id: u32, name: &str, sort: u32) -> Binder {
    Binder {
        id: BinderId(id),
        name: token(name),
        sort: SortId(sort),
    }
}

fn assert_root(draft: &mut QueryDraft, root: NodeId) {
    draft.commands.push(QueryCommand::Roots {
        kind: RootKind::Assert,
        roots: vec![root],
        attributes: vec![],
    });
}

fn declare(draft: &mut QueryDraft, id: u32, syntax: DeclarationSyntax) {
    draft.commands.push(QueryCommand::Declarations {
        syntax,
        kind: DeclarationGroupKind::Sequential,
        entries: vec![DeclId(id)],
        synthesis: None,
    });
}

fn checked(draft: QueryDraft) -> AuthoredQuery {
    let mut poll = || ControlFlow::Continue(());
    AuthoredQuery::validate(draft, &mut WorkBudget::new(100_000_000, &mut poll))
        .expect("valid fixture")
}

fn matches(a: QueryDraft, b: QueryDraft) -> bool {
    let a = checked(a);
    let b = checked(b);
    let mut poll = || ControlFlow::Continue(());
    a.structurally_matches(&b, &mut WorkBudget::new(100_000_000, &mut poll))
        .expect("finite comparison")
}

fn refused(draft: QueryDraft) -> QueryError {
    let mut poll = || ControlFlow::Continue(());
    AuthoredQuery::validate(draft, &mut WorkBudget::new(1_000_000, &mut poll))
        .expect_err("malformed fixture")
        .error()
}

fn constant(name: &str) -> Declaration {
    Declaration {
        name: token(name),
        kind: DeclarationKind::Term {
            role: TermRole::Function,
            type_parameters: vec![],
            arguments: vec![],
            result: SortId(0),
            definition: None,
        },
    }
}

fn scope(kind: ScopeKind) -> QueryCommand {
    QueryCommand::Scope {
        kind,
        levels: 1,
        numeral: None,
    }
}

#[test]
fn cross_arena_offsets_do_not_supply_term_identity() {
    let mut a = base();
    let root = boolean(&mut a, true);
    assert_root(&mut a, root);
    let mut b = base();
    boolean(&mut b, false); // Unreferenced arena scratch is not a source occurrence.
    let root = boolean(&mut b, true);
    assert_root(&mut b, root);
    assert!(matches(a, b));
}

#[test]
fn duplicate_assertion_occurrences_are_not_a_set() {
    let mut a = base();
    let root = boolean(&mut a, true);
    assert_root(&mut a, root);
    let mut b = a.clone();
    assert_root(&mut b, root);
    assert!(!matches(a, b));
}

#[test]
fn assertion_order_is_not_commuted() {
    let mut a = base();
    let first = boolean(&mut a, true);
    let second = boolean(&mut a, false);
    assert_root(&mut a, first);
    assert_root(&mut a, second);
    let mut b = a.clone();
    b.commands.swap(0, 1);
    assert!(!matches(a, b));
}

#[test]
fn assumptions_keep_order_and_duplicates() {
    let mut a = base();
    let root = boolean(&mut a, true);
    a.commands.push(QueryCommand::Check {
        kind: CheckKind::Assuming,
        assumptions: vec![root, root],
    });
    let mut b = a.clone();
    b.commands[0] = QueryCommand::Check {
        kind: CheckKind::Assuming,
        assumptions: vec![root],
    };
    assert!(!matches(a, b));
}

#[test]
fn host_identity_and_option_history_are_part_of_structure() {
    let mut a = base();
    a.data.push(DataNode::Literal(Literal {
        kind: LiteralKind::Boolean,
        text: "true".into(),
    }));
    a.commands.push(QueryCommand::SetOption {
        attribute: Attribute {
            keyword: "int-real-coercions".into(),
            value: Some(DataId(0)),
        },
        lifetime: LifetimeEffect::Unchanged,
    });
    let mut b = a.clone();
    b.data[0] = DataNode::Literal(Literal {
        kind: LiteralKind::Boolean,
        text: "false".into(),
    });
    assert!(!matches(a.clone(), b));
    let mut b = a.clone();
    b.typing.push(Attribute {
        keyword: "host-typing-version".into(),
        value: Some(DataId(0)),
    });
    assert!(!matches(a, b));
}

#[test]
fn indexed_qualified_operator_token_kind_is_significant() {
    let make = |index| {
        let mut draft = base();
        let root = node(
            &mut draft,
            0,
            NodeKind::Apply {
                operator: Operator {
                    head: OperatorHead::Builtin(builtin("plugin")),
                    indices: vec![index],
                    qualification: Some(SortId(0)),
                },
                arguments: vec![],
            },
        );
        assert_root(&mut draft, root);
        draft
    };
    assert!(!matches(
        make(IndexToken::Numeral("8".into())),
        make(IndexToken::Symbol(SymbolToken {
            kind: SymbolKind::Quoted,
            text: "8".into()
        }))
    ));
    assert!(!matches(
        make(IndexToken::Hexadecimal("8".into())),
        make(IndexToken::Numeral("8".into()))
    ));
    assert!(matches(
        make(IndexToken::Decimal("8.0".into())),
        make(IndexToken::Decimal("8.0".into()))
    ));
}

#[test]
fn numeral_spelling_is_not_numeric_equivalence() {
    let make = |text: &str| {
        let mut draft = base();
        let root = node(
            &mut draft,
            1,
            NodeKind::Literal(Literal {
                kind: LiteralKind::Numeral,
                text: text.into(),
            }),
        );
        draft.commands.push(QueryCommand::Request {
            head: token("get-value"),
            payload: vec![],
            terms: vec![root],
        });
        draft
    };
    assert!(!matches(make("1"), make("01")));
}
