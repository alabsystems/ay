// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::scopes::Scopes;
use super::validate_headers::{attrs, headers, invalid, symbol};
use super::validate_nodes::{Environment, Walker};
use super::*;
use std::collections::BTreeSet;

pub(super) fn validate(draft: &QueryDraft, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    work.charge(1)?;
    for count in [
        draft.sorts.len(),
        draft.nodes.len(),
        draft.data.len(),
        draft.declarations.len(),
    ] {
        if count > u32::MAX as usize {
            return Err(invalid("arena exceeds locator range"));
        }
    }
    headers(draft, work)?;
    attrs(draft, &draft.typing, work)?;
    payloads_in_scope(draft, &draft.typing, &[], &BTreeSet::new(), work)?;
    let mut state = State {
        draft,
        visible: BTreeSet::new(),
        scopes: Scopes::default(),
        lifetime: draft.initial_lifetime,
        next_declaration: 0,
    };
    for command in &draft.commands {
        work.charge(1)?;
        state.command(command, work)?;
    }
    if state.next_declaration != draft.declarations.len() {
        return Err(invalid("unrecorded catalog declaration"));
    }
    work.charge(0)
}

struct State<'a> {
    draft: &'a QueryDraft,
    visible: BTreeSet<DeclId>,
    scopes: Scopes,
    lifetime: DeclarationLifetime,
    next_declaration: usize,
}

impl State<'_> {
    fn command(
        &mut self,
        command: &QueryCommand,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        let draft = self.draft;
        match command {
            QueryCommand::Declarations {
                syntax,
                kind,
                entries,
                synthesis,
            } => {
                self.declarations(*syntax, *kind, entries, synthesis.as_ref(), work)?;
            }
            QueryCommand::Roots {
                roots, attributes, ..
            } => {
                if roots.len() != 1 {
                    return Err(invalid(
                        "one root command must retain exactly one source occurrence",
                    ));
                }
                attrs(draft, attributes, work)?;
                payloads_in_scope(draft, attributes, &[], &self.visible, work)?;
                roots_in_scope(draft, roots, &self.visible, work)?;
            }
            QueryCommand::Check { kind, assumptions } => {
                if *kind != CheckKind::Assuming && !assumptions.is_empty() {
                    return Err(invalid("assumptions on a non-assuming check"));
                }
                roots_in_scope(draft, assumptions, &self.visible, work)?;
            }
            QueryCommand::SetLogic(token) => symbol(token, work)?,
            QueryCommand::SetOption {
                attribute: attr,
                lifetime,
            } => {
                attrs(draft, std::slice::from_ref(attr), work)?;
                payloads_in_scope(draft, std::slice::from_ref(attr), &[], &self.visible, work)?;
                if matches!(
                    attr.keyword.as_str(),
                    "global-declarations" | "global-decls"
                ) {
                    self.lifetime = match lifetime {
                        LifetimeEffect::Unchanged => self.lifetime,
                        LifetimeEffect::Scoped => DeclarationLifetime::Scoped,
                        LifetimeEffect::Global => DeclarationLifetime::Global,
                    };
                } else if *lifetime != LifetimeEffect::Unchanged {
                    return Err(invalid("lifetime effect attached to unrelated option"));
                }
            }
            QueryCommand::SetInfo(attr) => {
                attrs(draft, std::slice::from_ref(attr), work)?;
                payloads_in_scope(draft, std::slice::from_ref(attr), &[], &self.visible, work)?;
            }
            QueryCommand::Scope {
                kind,
                levels,
                numeral,
            } => {
                self.scope(*kind, *levels, numeral.as_deref(), work)?;
            }
            QueryCommand::Reset => {
                self.scopes.reset(&mut self.visible, work)?;
                if draft.reset_lifetime == ResetLifetimePolicy::RestoreScopedDefault {
                    self.lifetime = DeclarationLifetime::Scoped;
                }
            }
            QueryCommand::ResetAssertions => {
                self.scopes
                    .reset_assertions(draft.reset_assertions, &mut self.visible, work)?
            }
            QueryCommand::Request {
                head,
                payload,
                terms,
            } => {
                symbol(head, work)?;
                payloads_in_scope(draft, &[], payload, &self.visible, work)?;
                roots_in_scope(draft, terms, &self.visible, work)?;
            }
        }
        Ok(())
    }

    fn declarations(
        &mut self,
        syntax: DeclarationSyntax,
        kind: DeclarationGroupKind,
        entries: &[DeclId],
        synthesis: Option<&SynthesisSyntax>,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        if synthesis.is_some()
            != matches!(
                syntax,
                DeclarationSyntax::SynthFun | DeclarationSyntax::SynthInv
            )
        {
            return Err(invalid("synthesis formal descriptor/command mismatch"));
        }
        validate_catalog::group_shape(self.draft, syntax, kind, entries, work)?;
        for entry in entries {
            work.charge(1)?;
            if entry.0 as usize != self.next_declaration {
                return Err(invalid("catalog history missing/repeated/reordered entry"));
            }
            self.next_declaration += 1;
        }
        if kind != DeclarationGroupKind::Sequential {
            for id in entries {
                work.tree(self.visible.len())?;
                self.visible.insert(*id);
            }
        }
        for id in entries {
            validate_catalog::declaration(self.draft, *id, &self.visible, kind, work)?;
            if let Some(synthesis) = synthesis {
                validate_catalog::synthesis(self.draft, *id, synthesis, &self.visible, work)?;
            }
            work.tree(self.visible.len())?;
            self.visible.insert(*id);
            self.scopes.record(*id, self.lifetime, work)?;
        }
        Ok(())
    }

    fn scope(
        &mut self,
        kind: ScopeKind,
        levels: u32,
        numeral: Option<&str>,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        numeral_matches(levels, numeral, work)?;
        match kind {
            ScopeKind::Push => self.scopes.push(levels, work),
            ScopeKind::Pop => self.scopes.pop(levels as usize, &mut self.visible, work),
        }
    }
}

fn roots_in_scope(
    draft: &QueryDraft,
    roots: &[NodeId],
    visible: &BTreeSet<DeclId>,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let mut walker = Walker::new(draft, visible);
    for root in roots {
        walker.node(*root, &Environment::default(), work)?;
    }
    walker.run(work)
}

fn payloads_in_scope(
    draft: &QueryDraft,
    attributes: &[Attribute],
    payload: &[DataId],
    visible: &BTreeSet<DeclId>,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let mut walker = Walker::new(draft, visible);
    let env = Environment::default();
    walker.attributes(attributes, &env, work)?;
    for id in payload {
        walker.data(*id, &env, work)?;
    }
    walker.run(work)
}

fn numeral_matches(
    levels: u32,
    token: Option<&str>,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let Some(token) = token else {
        return if levels == 1 {
            Ok(())
        } else {
            Err(invalid("omitted scope count is not one"))
        };
    };
    let mut count = 0u32;
    for chunk in token.as_bytes().chunks(128) {
        work.charge(chunk.len())?;
        for byte in chunk {
            if !byte.is_ascii_digit() {
                return Err(invalid("malformed scope numeral"));
            }
            count = count
                .checked_mul(10)
                .and_then(|n| n.checked_add((byte - b'0') as u32))
                .ok_or_else(|| invalid("scope numeral exceeds representation"))?;
        }
    }
    if token.is_empty() || count != levels {
        return Err(invalid("scope numeral/value mismatch"));
    }
    Ok(())
}
