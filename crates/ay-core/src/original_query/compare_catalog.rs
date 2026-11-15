// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::compare::{Engine, Environment};
use super::compare_syntax::symbol;
use super::*;

impl Engine<'_> {
    pub(super) fn declaration(
        &mut self,
        a: &Declaration,
        b: &Declaration,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        if !symbol(&a.name, &b.name, work)? {
            return Ok(false);
        }
        match (&a.kind, &b.kind) {
            (DeclarationKind::Sort { arity: a }, DeclarationKind::Sort { arity: b }) => Ok(a == b),
            (DeclarationKind::SortParameter, DeclarationKind::SortParameter) => Ok(true),
            (
                DeclarationKind::SortAlias {
                    parameters: ap,
                    body: a,
                },
                DeclarationKind::SortAlias {
                    parameters: bp,
                    body: b,
                },
            ) => {
                let Some(env) = self.type_parameters(ap, bp, work)? else {
                    return Ok(false);
                };
                self.sort(*a, *b, &env, work)?;
                Ok(true)
            }
            (
                DeclarationKind::Datatype {
                    parameters: ap,
                    constructors: ac,
                },
                DeclarationKind::Datatype {
                    parameters: bp,
                    constructors: bc,
                },
            ) => Ok(self.type_parameters(ap, bp, work)?.is_some() && locators(ac, bc, work)?),
            (
                DeclarationKind::Term {
                    role: ar,
                    type_parameters: ap,
                    arguments: aa,
                    result: a,
                    definition: ad,
                },
                DeclarationKind::Term {
                    role: br,
                    type_parameters: bp,
                    arguments: ba,
                    result: b,
                    definition: bd,
                },
            ) => {
                if ar != br {
                    return Ok(false);
                }
                let Some(env) = self.type_parameters(ap, bp, work)? else {
                    return Ok(false);
                };
                if !self.sorts(aa, ba, &env, work)? {
                    return Ok(false);
                }
                self.sort(*a, *b, &env, work)?;
                match (ad, bd) {
                    (Some(a), Some(b)) => {
                        if a.kind != b.kind {
                            return Ok(false);
                        }
                        let Some(bound) = self.binders(&a.parameters, &b.parameters, &env, work)?
                        else {
                            return Ok(false);
                        };
                        self.node(a.body, b.body, &bound, work)?;
                    }
                    (None, None) => {}
                    _ => return Ok(false),
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    pub(super) fn command(
        &mut self,
        a: &QueryCommand,
        b: &QueryCommand,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        if let Some(result) = self.control_command(a, b, work)? {
            return Ok(result);
        }
        let env = Environment::default();
        match (a, b) {
            (
                QueryCommand::Declarations {
                    syntax: asyn,
                    kind: ak,
                    entries: a,
                    synthesis: ag,
                },
                QueryCommand::Declarations {
                    syntax: bsyn,
                    kind: bk,
                    entries: b,
                    synthesis: bg,
                },
            ) => Ok(asyn == bsyn
                && ak == bk
                && locators(a, b, work)?
                && self.synthesis(ag.as_ref(), bg.as_ref(), a.first().copied(), work)?),
            (
                QueryCommand::Roots {
                    kind: ak,
                    roots: a,
                    attributes: aa,
                },
                QueryCommand::Roots {
                    kind: bk,
                    roots: b,
                    attributes: ba,
                },
            ) => Ok(ak == bk
                && self.nodes(a, b, &env, work)?
                && self.attributes(aa, ba, &env, work)?),
            (
                QueryCommand::Check {
                    kind: ak,
                    assumptions: a,
                },
                QueryCommand::Check {
                    kind: bk,
                    assumptions: b,
                },
            ) => Ok(ak == bk && self.nodes(a, b, &env, work)?),
            (
                QueryCommand::Request {
                    head: a,
                    payload: ap,
                    terms: at,
                },
                QueryCommand::Request {
                    head: b,
                    payload: bp,
                    terms: bt,
                },
            ) => Ok(symbol(a, b, work)?
                && self.payload(ap, bp, work)?
                && self.nodes(at, bt, &env, work)?),
            _ => Ok(false),
        }
    }

    fn control_command(
        &mut self,
        a: &QueryCommand,
        b: &QueryCommand,
        work: &mut WorkBudget<'_>,
    ) -> Result<Option<bool>, QueryError> {
        let env = Environment::default();
        let result = match (a, b) {
            (QueryCommand::SetLogic(a), QueryCommand::SetLogic(b)) => symbol(a, b, work),
            (
                QueryCommand::SetOption {
                    attribute: a,
                    lifetime: al,
                },
                QueryCommand::SetOption {
                    attribute: b,
                    lifetime: bl,
                },
            ) => Ok(al == bl
                && self.attributes(
                    std::slice::from_ref(a),
                    std::slice::from_ref(b),
                    &env,
                    work,
                )?),
            (QueryCommand::SetInfo(a), QueryCommand::SetInfo(b)) => {
                self.attributes(std::slice::from_ref(a), std::slice::from_ref(b), &env, work)
            }
            (
                QueryCommand::Scope {
                    kind: ak,
                    levels: a,
                    numeral: an,
                },
                QueryCommand::Scope {
                    kind: bk,
                    levels: b,
                    numeral: bn,
                },
            ) => {
                if ak != bk || a != b {
                    return Ok(Some(false));
                }
                match (an, bn) {
                    (Some(a), Some(b)) => work.text_eq(a, b),
                    (None, None) => Ok(true),
                    _ => Ok(false),
                }
            }
            (QueryCommand::Reset, QueryCommand::Reset)
            | (QueryCommand::ResetAssertions, QueryCommand::ResetAssertions) => Ok(true),

            _ => return Ok(None),
        }?;
        Ok(Some(result))
    }

    fn payload(
        &mut self,
        a: &[DataId],
        b: &[DataId],
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            self.data(*a, *b, &Environment::default(), work)?;
        }
        Ok(true)
    }

    fn synthesis(
        &mut self,
        a: Option<&SynthesisSyntax>,
        b: Option<&SynthesisSyntax>,
        owner: Option<DeclId>,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        match (a, b) {
            (Some(a), Some(b)) => {
                let owner = owner.ok_or(QueryError::Invalid("missing synthesis declaration"))?;
                let left = self.left;
                let right = self.right;
                let (ap, bp) = match (
                    &left.declarations[owner.0 as usize].kind,
                    &right.declarations[owner.0 as usize].kind,
                ) {
                    (
                        DeclarationKind::Term {
                            type_parameters: a, ..
                        },
                        DeclarationKind::Term {
                            type_parameters: b, ..
                        },
                    ) => (a, b),
                    _ => return Err(QueryError::Invalid("synthesis owner is not a function")),
                };
                let Some(env) = self.type_parameters(ap, bp, work)? else {
                    return Ok(false);
                };
                let Some(bound) = self.binders(&a.parameters, &b.parameters, &env, work)? else {
                    return Ok(false);
                };
                match (a.grammar, b.grammar) {
                    (Some(a), Some(b)) => self.data(a, b, &bound, work)?,
                    (None, None) => {}
                    _ => return Ok(false),
                }
                Ok(true)
            }
            (None, None) => Ok(true),
            _ => Ok(false),
        }
    }
}

fn locators(a: &[DeclId], b: &[DeclId], work: &mut WorkBudget<'_>) -> Result<bool, QueryError> {
    work.charge(1)?;
    if a.len() != b.len() {
        return Ok(false);
    }
    for (a, b) in a.iter().zip(b) {
        work.charge(2)?;
        if a != b {
            return Ok(false);
        }
    }
    Ok(true)
}
