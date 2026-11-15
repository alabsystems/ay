// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::compare::{Engine, Environment};
use super::*;

pub(super) fn symbol(
    a: &SymbolToken,
    b: &SymbolToken,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    work.charge(1)?;
    Ok(a.kind == b.kind && work.text_eq(&a.text, &b.text)?)
}

fn builtin(a: &Builtin, b: &Builtin, work: &mut WorkBudget<'_>) -> Result<bool, QueryError> {
    work.charge(1)?;
    Ok(a.family == b.family && symbol(&a.symbol, &b.symbol, work)?)
}

pub(super) fn literal(
    a: &Literal,
    b: &Literal,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    work.charge(1)?;
    Ok(a.kind == b.kind && work.text_eq(&a.text, &b.text)?)
}

impl Engine<'_> {
    fn indices(
        &self,
        a: &[IndexToken],
        b: &[IndexToken],
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        work.charge(1)?;
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            work.charge(1)?;
            let equal = match (a, b) {
                (IndexToken::Numeral(a), IndexToken::Numeral(b))
                | (IndexToken::Decimal(a), IndexToken::Decimal(b))
                | (IndexToken::Hexadecimal(a), IndexToken::Hexadecimal(b))
                | (IndexToken::Binary(a), IndexToken::Binary(b)) => work.text_eq(a, b)?,
                (IndexToken::Symbol(a), IndexToken::Symbol(b)) => symbol(a, b, work)?,
                (
                    IndexToken::Reference {
                        symbol: a,
                        reference: ah,
                    },
                    IndexToken::Reference {
                        symbol: b,
                        reference: bh,
                    },
                ) => {
                    let lexical = match (ah, bh) {
                        (OperatorHead::Bound(_), OperatorHead::Bound(_)) => a.kind == b.kind,
                        _ => symbol(a, b, work)?,
                    };
                    lexical && self.head(ah, bh, env, work)?
                }
                _ => false,
            };
            if !equal {
                return Ok(false);
            }
        }
        Ok(true)
    }
    pub(super) fn attributes(
        &mut self,
        a: &[Attribute],
        b: &[Attribute],
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        work.charge(1)?;
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            work.charge(1)?;
            if !work.text_eq(&a.keyword, &b.keyword)? {
                return Ok(false);
            }
            match (a.value, b.value) {
                (Some(a), Some(b)) => self.data(a, b, env, work)?,
                (None, None) => {}
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    pub(super) fn operator(
        &mut self,
        a: &Operator,
        b: &Operator,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        work.charge(1)?;
        let head = self.head(&a.head, &b.head, env, work)?;
        if !head || !self.indices(&a.indices, &b.indices, env, work)? {
            return Ok(false);
        }
        match (a.qualification, b.qualification) {
            (Some(a), Some(b)) => self.sort(a, b, env, work)?,
            (None, None) => {}
            _ => return Ok(false),
        }
        Ok(true)
    }

    fn head(
        &self,
        a: &OperatorHead,
        b: &OperatorHead,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        work.charge(1)?;
        Ok(match (a, b) {
            (OperatorHead::Builtin(a), OperatorHead::Builtin(b)) => builtin(a, b, work)?,
            (OperatorHead::Declaration(a), OperatorHead::Declaration(b)) => a == b,
            (OperatorHead::Bound(a), OperatorHead::Bound(b)) => {
                self.environments.terms_match(*env, *a, *b, work)?
            }
            _ => false,
        })
    }

    pub(super) fn sort_pair(
        &mut self,
        a: SortId,
        b: SortId,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        let left = self.left;
        let right = self.right;
        match (&left.sorts[a.0 as usize], &right.sorts[b.0 as usize]) {
            (SortNode::Parameter(a), SortNode::Parameter(b)) => {
                self.environments.types_match(*env, *a, *b, work)
            }
            (
                SortNode::Nominal {
                    declaration: a,
                    arguments: aa,
                },
                SortNode::Nominal {
                    declaration: b,
                    arguments: ba,
                },
            ) => Ok(a == b && self.sorts(aa, ba, env, work)?),
            (
                SortNode::Builtin {
                    head: a,
                    indices: ai,
                    arguments: aa,
                },
                SortNode::Builtin {
                    head: b,
                    indices: bi,
                    arguments: ba,
                },
            ) => Ok(builtin(a, b, work)?
                && self.indices(ai, bi, env, work)?
                && self.sorts(aa, ba, env, work)?),
            _ => Ok(false),
        }
    }

    pub(super) fn data_pair(
        &mut self,
        a: DataId,
        b: DataId,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        let left = self.left;
        let right = self.right;
        match (&left.data[a.0 as usize], &right.data[b.0 as usize]) {
            (DataNode::Symbol(a), DataNode::Symbol(b)) => symbol(a, b, work),
            (DataNode::Reference(a), DataNode::Reference(b)) => self.head(a, b, env, work),
            (DataNode::Keyword(a), DataNode::Keyword(b)) => work.text_eq(a, b),
            (DataNode::Literal(a), DataNode::Literal(b)) => literal(a, b, work),
            (DataNode::List(a), DataNode::List(b)) => {
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (a, b) in a.iter().zip(b) {
                    self.data(*a, *b, env, work)?;
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }
}
