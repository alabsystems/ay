// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::validate_headers::{invalid, symbol};
use super::validate_nodes::{Environment, Walker};
use super::*;
use std::collections::BTreeSet;

pub(super) fn declaration(
    draft: &QueryDraft,
    id: DeclId,
    visible: &BTreeSet<DeclId>,
    group: DeclarationGroupKind,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let declaration = draft
        .declarations
        .get(id.0 as usize)
        .ok_or_else(|| invalid("missing declaration"))?;
    work.charge(1)?;
    symbol(&declaration.name, work)?;
    let mut walker = Walker::new(draft, visible);
    let empty = Environment::default();
    match &declaration.kind {
        DeclarationKind::Sort { .. } | DeclarationKind::SortParameter => {}
        DeclarationKind::SortAlias { parameters, body } => {
            let env = walker.types(empty, parameters, work)?;
            walker.sort(*body, &env, work)?;
        }
        DeclarationKind::Datatype {
            parameters,
            constructors,
        } => {
            if group != DeclarationGroupKind::MutualDatatypes || constructors.is_empty() {
                return Err(invalid(
                    "datatype outside a datatype group or without constructors",
                ));
            }
            walker.types(empty, parameters, work)?;
            for ctor in constructors {
                work.charge(1)?;
                work.tree(visible.len())?;
                if !visible.contains(ctor)
                    || !matches!(draft.declarations.get(ctor.0 as usize).map(|d| &d.kind),
                    Some(DeclarationKind::Term { role: TermRole::Constructor(owner), .. }) if *owner == id)
                {
                    return Err(invalid("datatype constructor ownership mismatch"));
                }
            }
        }
        DeclarationKind::Term {
            role,
            type_parameters,
            arguments,
            result,
            definition,
        } => {
            validate_role(draft, id, role, visible, group, work)?;
            let env = walker.types(empty, type_parameters, work)?;
            for argument in arguments {
                walker.sort(*argument, &env, work)?;
            }
            walker.sort(*result, &env, work)?;
            if let Some(body) = definition {
                if !matches!(role, TermRole::Function)
                    || body.parameters.len() != arguments.len()
                    || (body.kind == DefinitionKind::Recursive)
                        != (group == DeclarationGroupKind::RecursiveFunctions)
                {
                    return Err(invalid("definition role/arity/recursion mismatch"));
                }
                for (param, argument) in body.parameters.iter().zip(arguments) {
                    work.charge(1)?;
                    symbol(&param.name, work)?;
                    if param.sort != *argument {
                        return Err(invalid("definition parameter sort locator mismatch"));
                    }
                }
                validate_headers::node_ref(draft, body.body)?;
                if draft.nodes[body.body.0 as usize].sort != *result {
                    return Err(invalid("definition body/result sort locator mismatch"));
                }
                let bound = walker.parameters(env, &body.parameters, work)?;
                walker.node(body.body, &bound, work)?;
            } else if group == DeclarationGroupKind::RecursiveFunctions {
                return Err(invalid(
                    "recursive function group contains an undeﬁned entry",
                ));
            }
        }
    }
    walker.run(work)
}

fn validate_role(
    draft: &QueryDraft,
    id: DeclId,
    role: &TermRole,
    visible: &BTreeSet<DeclId>,
    group: DeclarationGroupKind,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    work.charge(1)?;
    work.tree(visible.len())?;
    match role {
        TermRole::Constructor(owner) => {
            if group != DeclarationGroupKind::MutualDatatypes || !visible.contains(owner) {
                return Err(invalid("constructor outside its datatype group"));
            }
            match draft.declarations.get(owner.0 as usize).map(|d| &d.kind) {
                Some(DeclarationKind::Datatype { constructors, .. }) => {
                    let mut found = false;
                    for constructor in constructors {
                        work.charge(1)?;
                        if *constructor == id {
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return Err(invalid("unlisted datatype constructor"));
                    }
                }
                _ => return Err(invalid("constructor owner is not a datatype")),
            }
        }
        TermRole::Selector { constructor, field } => {
            if group != DeclarationGroupKind::MutualDatatypes || !visible.contains(constructor) {
                return Err(invalid("selector outside its datatype group"));
            }
            match draft
                .declarations
                .get(constructor.0 as usize)
                .map(|d| &d.kind)
            {
                Some(DeclarationKind::Term {
                    role: TermRole::Constructor(_),
                    arguments,
                    ..
                }) if (*field as usize) < arguments.len() => {}
                _ => return Err(invalid("selector field/constructor mismatch")),
            }
        }
        _ if group == DeclarationGroupKind::MutualDatatypes => {
            return Err(invalid("non-datatype term in datatype group"))
        }
        _ => {}
    }
    Ok(())
}

pub(super) fn synthesis(
    draft: &QueryDraft,
    owner: DeclId,
    syntax: &SynthesisSyntax,
    visible: &BTreeSet<DeclId>,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let (types, arguments) = match draft.declarations.get(owner.0 as usize).map(|d| &d.kind) {
        Some(DeclarationKind::Term {
            type_parameters,
            arguments,
            ..
        }) => (type_parameters, arguments),
        _ => return Err(invalid("synthesis owner is not a function")),
    };
    if arguments.len() != syntax.parameters.len() {
        return Err(invalid("synthesis formal arity mismatch"));
    }
    for (formal, sort) in syntax.parameters.iter().zip(arguments) {
        work.charge(1)?;
        if formal.sort != *sort {
            return Err(invalid("synthesis formal sort locator mismatch"));
        }
    }
    let mut walker = Walker::new(draft, visible);
    let env = walker.types(Environment::default(), types, work)?;
    let bound = walker.parameters(env, &syntax.parameters, work)?;
    if let Some(grammar) = syntax.grammar {
        walker.data(grammar, &bound, work)?;
    }
    walker.run(work)
}

pub(super) fn group_shape(
    draft: &QueryDraft,
    syntax: DeclarationSyntax,
    kind: DeclarationGroupKind,
    entries: &[DeclId],
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    use DeclarationSyntax::*;
    work.charge(1)?;
    let required = match syntax {
        DefineFunRec | DefineFunsRec => DeclarationGroupKind::RecursiveFunctions,
        DeclareDatatype | DeclareDatatypes => DeclarationGroupKind::MutualDatatypes,
        _ => DeclarationGroupKind::Sequential,
    };
    if kind != required || entries.is_empty() {
        return Err(invalid("declaration command/group mismatch"));
    }
    if kind == DeclarationGroupKind::Sequential && entries.len() != 1 {
        return Err(invalid(
            "one source declaration command must not collapse multiple commands",
        ));
    }
    for id in entries {
        work.charge(1)?;
        let entry = draft
            .declarations
            .get(id.0 as usize)
            .ok_or_else(|| invalid("missing declaration"))?;
        let valid = match (&entry.kind, syntax) {
            (DeclarationKind::Sort { .. }, DeclareSort)
            | (DeclarationKind::SortParameter, DeclareSortParameter)
            | (DeclarationKind::SortAlias { .. }, DefineSort)
            | (DeclarationKind::Datatype { .. }, DeclareDatatype | DeclareDatatypes) => true,
            (
                DeclarationKind::Term {
                    role: TermRole::Constructor(_) | TermRole::Selector { .. },
                    ..
                },
                DeclareDatatype | DeclareDatatypes,
            ) => true,
            (
                DeclarationKind::Term {
                    role: TermRole::RuleVariable,
                    arguments,
                    definition: None,
                    ..
                },
                DeclareVar,
            ) => arguments.is_empty(),
            (
                DeclarationKind::Term {
                    role: TermRole::Relation,
                    definition: None,
                    ..
                },
                DeclareRel,
            ) => true,
            (
                DeclarationKind::Term {
                    role: TermRole::Function,
                    arguments,
                    definition: None,
                    ..
                },
                DeclareConst,
            ) => arguments.is_empty(),
            (
                DeclarationKind::Term {
                    role: TermRole::Function,
                    definition: None,
                    ..
                },
                DeclareFun | SynthFun | SynthInv,
            ) => true,
            (
                DeclarationKind::Term {
                    role: TermRole::Function,
                    definition: Some(_),
                    ..
                },
                DefineFun | DefineFunRec | DefineFunsRec,
            ) => true,
            _ => false,
        };
        if !valid {
            return Err(invalid("declaration command/kind mismatch"));
        }
    }
    Ok(())
}
