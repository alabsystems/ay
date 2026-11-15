// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
enum Site {
    Operator,
    Sort,
}

fn reference(name: &str, head: OperatorHead) -> IndexToken {
    IndexToken::Reference {
        symbol: token(name),
        reference: head,
    }
}

fn indexed(draft: &mut QueryDraft, index: IndexToken, site: Site) -> NodeId {
    // The sort-index branch is a structural extension fixture, not a claim
    // that a native language plugin accepts an indexed sort with this name.
    let sort = match site {
        Site::Operator => 0,
        Site::Sort => {
            let id = draft.sorts.len() as u32;
            draft.sorts.push(SortNode::Builtin {
                head: Builtin {
                    family: BuiltinFamily::Extension,
                    symbol: token("indexed-carrier"),
                },
                indices: vec![index],
                arguments: vec![],
            });
            return node(
                draft,
                id,
                NodeKind::Apply {
                    operator: Operator {
                        head: OperatorHead::Builtin(builtin("carrier-value")),
                        indices: vec![],
                        qualification: None,
                    },
                    arguments: vec![],
                },
            );
        }
    };
    node(
        draft,
        sort,
        NodeKind::Apply {
            operator: Operator {
                head: OperatorHead::Builtin(builtin("indexed-predicate")),
                indices: vec![index],
                qualification: None,
            },
            arguments: vec![],
        },
    )
}

fn nominal(site: Site, index: IndexToken) -> QueryDraft {
    let mut draft = base();
    draft.declarations.push(constant("f"));
    declare(&mut draft, 0, DeclarationSyntax::DeclareConst);
    let root = indexed(&mut draft, index, site);
    draft.commands.push(QueryCommand::Request {
        head: token("get-value"),
        payload: vec![],
        terms: vec![root],
    });
    draft
}

fn bound(site: Site, outer: u32, inner: u32, capture: bool, name: &str) -> QueryDraft {
    let mut draft = base();
    let body = indexed(
        &mut draft,
        reference(
            name,
            OperatorHead::Bound(BinderId(if capture { inner } else { outer })),
        ),
        site,
    );
    let nested = node(
        &mut draft,
        0,
        NodeKind::Quantified {
            quantifier: Quantifier::Exists,
            binders: vec![binder(inner, "inner", 0)],
            body,
        },
    );
    let root = node(
        &mut draft,
        0,
        NodeKind::Quantified {
            quantifier: Quantifier::Forall,
            binders: vec![binder(outer, name, 0)],
            body: nested,
        },
    );
    assert_root(&mut draft, root);
    draft
}

#[test]
fn resolved_indices_match_in_both_operator_and_builtin_sort_sites() {
    for site in [Site::Operator, Site::Sort] {
        let a = nominal(site, reference("f", OperatorHead::Declaration(DeclId(0))));
        let b = a.clone();
        assert!(matches(a, b));
    }
}

#[test]
fn resolved_index_is_not_unresolved_symbol_metadata() {
    for site in [Site::Operator, Site::Sort] {
        assert!(!matches(
            nominal(site, reference("f", OperatorHead::Declaration(DeclId(0)))),
            nominal(site, IndexToken::Symbol(token("f")))
        ));
    }
}

#[test]
fn indexed_nominal_tokens_and_quotation_remain_significant() {
    for site in [Site::Operator, Site::Sort] {
        let make = |symbol| {
            nominal(
                site,
                IndexToken::Reference {
                    symbol,
                    reference: OperatorHead::Declaration(DeclId(0)),
                },
            )
        };
        assert!(!matches(make(token("f")), make(token("different"))));
        assert!(!matches(
            make(token("f")),
            make(SymbolToken {
                kind: SymbolKind::Quoted,
                text: "f".into(),
            })
        ));
    }
}

#[test]
fn indexed_builtin_and_nominal_same_spelling_are_distinct() {
    for site in [Site::Operator, Site::Sort] {
        assert!(!matches(
            nominal(site, reference("f", OperatorHead::Declaration(DeclId(0)))),
            nominal(site, reference("f", OperatorHead::Builtin(builtin("f"))))
        ));
    }
}

#[test]
fn indexed_missing_and_nonterm_declaration_locators_are_refused() {
    for site in [Site::Operator, Site::Sort] {
        let missing = nominal(site, reference("f", OperatorHead::Declaration(DeclId(99))));
        assert_eq!(
            refused(missing),
            QueryError::Invalid("term locator does not refer to a term declaration")
        );
        let mut nonterm = nominal(site, reference("f", OperatorHead::Declaration(DeclId(0))));
        nonterm.declarations[0].kind = DeclarationKind::Sort { arity: 0 };
        nonterm.commands[0] = QueryCommand::Declarations {
            syntax: DeclarationSyntax::DeclareSort,
            kind: DeclarationGroupKind::Sequential,
            entries: vec![DeclId(0)],
            synthesis: None,
        };
        assert_eq!(
            refused(nonterm),
            QueryError::Invalid("term locator does not refer to a term declaration")
        );
    }
}

#[test]
fn indexed_forward_reference_does_not_borrow_final_catalog_visibility() {
    for site in [Site::Operator, Site::Sort] {
        let mut draft = nominal(site, reference("f", OperatorHead::Declaration(DeclId(0))));
        draft.commands.swap(0, 1);
        assert_eq!(
            refused(draft),
            QueryError::Invalid("declaration is not visible at this occurrence")
        );
    }
}

#[test]
fn indexed_popped_reference_cannot_borrow_sticky_declaration_metadata() {
    for site in [Site::Operator, Site::Sort] {
        let mut draft = nominal(site, reference("f", OperatorHead::Declaration(DeclId(0))));
        draft.commands.insert(0, scope(ScopeKind::Push));
        draft.commands.insert(2, scope(ScopeKind::Pop));
        assert_eq!(
            refused(draft),
            QueryError::Invalid("declaration is not visible at this occurrence")
        );
    }
}

#[test]
fn same_spelling_indexed_overloads_retain_exact_nominal_identity() {
    let make = |selected| {
        let mut draft = base();
        draft.declarations.push(constant("f"));
        let mut second = constant("f");
        if let DeclarationKind::Term { arguments, .. } = &mut second.kind {
            arguments.push(SortId(1));
        }
        draft.declarations.push(second);
        declare(&mut draft, 0, DeclarationSyntax::DeclareConst);
        declare(&mut draft, 1, DeclarationSyntax::DeclareFun);
        let root = indexed(
            &mut draft,
            reference("f", OperatorHead::Declaration(DeclId(selected))),
            Site::Operator,
        );
        assert_root(&mut draft, root);
        draft
    };
    assert!(!matches(make(0), make(1)));
}

#[test]
fn indexed_bound_names_are_alpha_renamable_under_the_full_environment() {
    for site in [Site::Operator, Site::Sort] {
        assert!(matches(
            bound(site, 0, 1, false, "x"),
            bound(site, 71, 83, false, "renamed")
        ));
        assert!(!matches(
            bound(site, 0, 1, false, "x"),
            bound(site, 71, 83, true, "inner")
        ));
    }
}

#[test]
fn indexed_bound_reference_cannot_escape_its_occurrence_environment() {
    for site in [Site::Operator, Site::Sort] {
        let mut draft = bound(site, 0, 1, false, "x");
        assert_root(&mut draft, NodeId(0));
        assert_eq!(refused(draft), QueryError::Invalid("unbound operator"));
    }
}

#[test]
fn indexed_shared_node_is_memoized_with_paired_binder_environment() {
    let make = |left| {
        let mut draft = base();
        let ids = if left { [0, 1] } else { [8, 9] };
        let shared = indexed(
            &mut draft,
            reference("x", OperatorHead::Bound(BinderId(if left { 0 } else { 9 }))),
            Site::Operator,
        );
        let wide = node(
            &mut draft,
            0,
            NodeKind::Quantified {
                quantifier: Quantifier::Forall,
                binders: vec![binder(ids[0], "x", 0), binder(ids[1], "y", 0)],
                body: shared,
            },
        );
        let narrow = node(
            &mut draft,
            0,
            NodeKind::Quantified {
                quantifier: Quantifier::Forall,
                binders: vec![binder(if left { 0 } else { 9 }, "x", 0)],
                body: shared,
            },
        );
        assert_root(&mut draft, wide);
        assert_root(&mut draft, narrow);
        draft
    };
    assert!(!matches(make(true), make(false)));
}

#[test]
fn indexed_bound_token_kind_is_not_erased_by_alpha_renaming() {
    let a = bound(Site::Operator, 0, 1, false, "x");
    let mut b = a.clone();
    if let NodeKind::Apply { operator, .. } = &mut b.nodes[0].kind {
        if let IndexToken::Reference { symbol, .. } = &mut operator.indices[0] {
            symbol.kind = SymbolKind::Quoted;
        }
    }
    assert!(!matches(a, b));
}
