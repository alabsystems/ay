// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn invalid(message: &'static str) -> QueryError {
    QueryError::Invalid(message)
}

pub(super) fn symbol(value: &SymbolToken, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    work.text(&value.text)?;
    if value.text.is_empty() && value.kind == SymbolKind::Simple {
        return Err(invalid("empty symbol"));
    }
    Ok(())
}

pub(super) fn literal(value: &Literal, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    literal_text(value.kind, &value.text, work)
}

fn literal_text(
    kind: LiteralKind,
    text: &str,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    if kind == LiteralKind::Boolean {
        work.text(text)?;
        return if matches!(text, "true" | "false") {
            Ok(())
        } else {
            Err(invalid("malformed Boolean token"))
        };
    }
    if kind == LiteralKind::String {
        return work.text(text);
    }
    let mut dot = None;
    for (offset, chunk) in text.as_bytes().chunks(128).enumerate() {
        work.charge(chunk.len())?;
        for (index, byte) in chunk.iter().enumerate() {
            let valid = match kind {
                LiteralKind::Numeral => byte.is_ascii_digit(),
                LiteralKind::Decimal if *byte == b'.' => {
                    if dot.is_some() {
                        false
                    } else {
                        dot = Some(offset * 128 + index);
                        true
                    }
                }
                LiteralKind::Decimal => byte.is_ascii_digit(),
                LiteralKind::Hexadecimal => byte.is_ascii_hexdigit(),
                LiteralKind::Binary => matches!(byte, b'0' | b'1'),
                LiteralKind::String => true,
                LiteralKind::Boolean => false,
            };
            if !valid {
                return Err(invalid("malformed literal token"));
            }
        }
    }
    work.charge(1)?;
    if text.is_empty()
        || (kind == LiteralKind::Decimal && !dot.is_some_and(|at| at > 0 && at + 1 < text.len()))
    {
        return Err(invalid("malformed literal token"));
    }
    Ok(())
}

pub(super) fn indices(
    draft: &QueryDraft,
    values: &[IndexToken],
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    for value in values {
        work.charge(1)?;
        match value {
            IndexToken::Numeral(text) => {
                for chunk in text.as_bytes().chunks(128) {
                    work.charge(chunk.len())?;
                    if !chunk.iter().all(u8::is_ascii_digit) {
                        return Err(invalid("malformed numeral index"));
                    }
                }
                if text.is_empty() {
                    return Err(invalid("empty numeral index"));
                }
            }
            IndexToken::Decimal(text)
            | IndexToken::Hexadecimal(text)
            | IndexToken::Binary(text) => {
                let kind = match value {
                    IndexToken::Decimal(_) => LiteralKind::Decimal,
                    IndexToken::Hexadecimal(_) => LiteralKind::Hexadecimal,
                    _ => LiteralKind::Binary,
                };
                literal_text(kind, text, work)?;
            }
            IndexToken::Symbol(token) => symbol(token, work)?,
            IndexToken::Reference {
                symbol: token,
                reference,
            } => {
                symbol(token, work)?;
                reference_header(draft, reference, work)?;
            }
        }
    }
    Ok(())
}

fn reference_header(
    draft: &QueryDraft,
    head: &OperatorHead,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    work.charge(1)?;
    match head {
        OperatorHead::Builtin(head) => symbol(&head.symbol, work),
        OperatorHead::Declaration(id) => term_arity(draft, *id).map(|_| ()),
        OperatorHead::Bound(_) => Ok(()),
    }
}

pub(super) fn sort_arity(draft: &QueryDraft, id: DeclId) -> Result<usize, QueryError> {
    match draft.declarations.get(id.0 as usize).map(|d| &d.kind) {
        Some(DeclarationKind::Sort { arity }) => Ok(*arity as usize),
        Some(DeclarationKind::SortParameter) => Ok(0),
        Some(DeclarationKind::SortAlias { parameters, .. })
        | Some(DeclarationKind::Datatype { parameters, .. }) => Ok(parameters.len()),
        _ => Err(invalid("sort locator does not refer to a sort declaration")),
    }
}

pub(super) fn term_arity(draft: &QueryDraft, id: DeclId) -> Result<usize, QueryError> {
    match draft.declarations.get(id.0 as usize).map(|d| &d.kind) {
        Some(DeclarationKind::Term { arguments, .. }) => Ok(arguments.len()),
        _ => Err(invalid("term locator does not refer to a term declaration")),
    }
}

fn prior(id: u32, at: usize) -> Result<(), QueryError> {
    if (id as usize) < at {
        Ok(())
    } else {
        Err(invalid("non-topological arena edge"))
    }
}

pub(super) fn sort_ref(draft: &QueryDraft, id: SortId) -> Result<(), QueryError> {
    if (id.0 as usize) < draft.sorts.len() {
        Ok(())
    } else {
        Err(invalid("missing sort"))
    }
}

pub(super) fn node_ref(draft: &QueryDraft, id: NodeId) -> Result<(), QueryError> {
    if (id.0 as usize) < draft.nodes.len() {
        Ok(())
    } else {
        Err(invalid("missing term"))
    }
}

pub(super) fn attrs(
    draft: &QueryDraft,
    values: &[Attribute],
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    for value in values {
        work.charge(1)?;
        work.text(&value.keyword)?;
        if value.keyword.is_empty() {
            return Err(invalid("empty attribute keyword"));
        }
        if value
            .value
            .is_some_and(|id| id.0 as usize >= draft.data.len())
        {
            return Err(invalid("missing attribute payload"));
        }
    }
    Ok(())
}

pub(super) fn headers(draft: &QueryDraft, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    for (at, data) in draft.data.iter().enumerate() {
        work.charge(1)?;
        match data {
            DataNode::Symbol(token) => symbol(token, work)?,
            DataNode::Reference(OperatorHead::Builtin(head)) => symbol(&head.symbol, work)?,
            DataNode::Reference(OperatorHead::Declaration(id)) => {
                term_arity(draft, *id)?;
            }
            DataNode::Reference(OperatorHead::Bound(_)) => {}
            DataNode::Keyword(text) => work.text(text)?,
            DataNode::Literal(token) => literal(token, work)?,
            DataNode::List(children) => {
                for child in children {
                    work.charge(1)?;
                    prior(child.0, at)?;
                }
            }
        }
    }
    for (at, sort) in draft.sorts.iter().enumerate() {
        work.charge(1)?;
        let children = match sort {
            SortNode::Builtin {
                head,
                indices: tags,
                arguments,
            } => {
                symbol(&head.symbol, work)?;
                indices(draft, tags, work)?;
                arguments
            }
            SortNode::Nominal {
                declaration,
                arguments,
            } => {
                if sort_arity(draft, *declaration)? != arguments.len() {
                    return Err(invalid("nominal sort arity mismatch"));
                }
                arguments
            }
            SortNode::Parameter(_) => continue,
        };
        for child in children {
            work.charge(1)?;
            prior(child.0, at)?;
        }
    }
    for (at, node) in draft.nodes.iter().enumerate() {
        work.charge(1)?;
        sort_ref(draft, node.sort)?;
        node_header(draft, at, &node.kind, work)?;
    }
    Ok(())
}

fn binder_header(
    draft: &QueryDraft,
    binder: &Binder,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    work.charge(1)?;
    symbol(&binder.name, work)?;
    sort_ref(draft, binder.sort)
}

fn operator_header(
    draft: &QueryDraft,
    op: &Operator,
    arity: usize,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    match &op.head {
        OperatorHead::Builtin(head) => symbol(&head.symbol, work)?,
        OperatorHead::Declaration(id) if term_arity(draft, *id)? != arity => {
            return Err(invalid("nominal function arity mismatch"));
        }
        _ => {}
    }
    indices(draft, &op.indices, work)?;
    if let Some(sort) = op.qualification {
        sort_ref(draft, sort)?;
    }
    Ok(())
}

fn node_header(
    draft: &QueryDraft,
    at: usize,
    kind: &NodeKind,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    match kind {
        NodeKind::Literal(token) => literal(token, work)?,
        NodeKind::Free(id) if term_arity(draft, *id)? != 0 => {
            return Err(invalid("non-nullary free reference"))
        }
        NodeKind::Free(_) | NodeKind::Bound(_) => {}
        NodeKind::Apply {
            operator,
            arguments,
        } => {
            operator_header(draft, operator, arguments.len(), work)?;
            for child in arguments {
                work.charge(1)?;
                prior(child.0, at)?;
            }
        }
        NodeKind::Let { bindings, body } => {
            prior(body.0, at)?;
            for binding in bindings {
                binder_header(draft, &binding.binder, work)?;
                prior(binding.value.0, at)?;
                if draft.nodes[binding.value.0 as usize].sort != binding.binder.sort {
                    return Err(invalid("let binder/value sort locator mismatch"));
                }
            }
        }
        NodeKind::Quantified { binders, body, .. } => {
            prior(body.0, at)?;
            for binder in binders {
                binder_header(draft, binder, work)?;
            }
        }
        NodeKind::Match { scrutinee, cases } => {
            prior(scrutinee.0, at)?;
            if cases.is_empty() {
                return Err(invalid("empty match"));
            }
            for case in cases {
                work.charge(1)?;
                prior(case.body.0, at)?;
                match &case.pattern {
                    MatchPattern::Variable(binder) => binder_header(draft, binder, work)?,
                    MatchPattern::Wildcard => {}
                    MatchPattern::Constructor {
                        declaration,
                        fields,
                    } => {
                        if !matches!(
                            draft
                                .declarations
                                .get(declaration.0 as usize)
                                .map(|d| &d.kind),
                            Some(DeclarationKind::Term {
                                role: TermRole::Constructor(_),
                                ..
                            })
                        ) || term_arity(draft, *declaration)? != fields.len()
                        {
                            return Err(invalid("invalid constructor pattern"));
                        }
                        for field in fields {
                            match field {
                                PatternField::Binder(binder) => binder_header(draft, binder, work)?,
                                PatternField::Wildcard(sort) => {
                                    work.charge(1)?;
                                    sort_ref(draft, *sort)?;
                                }
                            }
                        }
                    }
                }
            }
        }
        NodeKind::Annotated { body, attributes } => {
            prior(body.0, at)?;
            attrs(draft, attributes, work)?;
        }
    }
    Ok(())
}
