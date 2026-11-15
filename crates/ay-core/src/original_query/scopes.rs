// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Flat declaration/scope history, with no scope-vector bulk copies or clears.

use super::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Default)]
pub(super) struct Scopes {
    depth: usize,
    entries: BTreeMap<(usize, DeclId), ()>,
}

impl Scopes {
    pub(super) fn record(
        &mut self,
        id: DeclId,
        lifetime: DeclarationLifetime,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        let scope = match lifetime {
            DeclarationLifetime::Scoped => self.depth,
            DeclarationLifetime::Global => 0,
        };
        work.tree(self.entries.len())?;
        if self.entries.insert((scope, id), ()).is_some() {
            return Err(QueryError::Invalid("repeated declaration scope record"));
        }
        Ok(())
    }

    pub(super) fn push(
        &mut self,
        levels: u32,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        // Empty levels have no stored payload; count them without materializing frames.
        work.charge(1)?;
        self.depth = self
            .depth
            .checked_add(levels as usize)
            .ok_or_else(|| work.exhausted())?;
        Ok(())
    }

    pub(super) fn pop(
        &mut self,
        levels: usize,
        visible: &mut BTreeSet<DeclId>,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        work.charge(1)?;
        let depth = self
            .depth
            .checked_sub(levels)
            .ok_or(QueryError::Invalid("scope underflow"))?;
        loop {
            work.tree(self.entries.len())?;
            let Some((&(scope, _), _)) = self.entries.last_key_value() else {
                break;
            };
            if scope <= depth {
                break;
            }
            self.remove_last(visible, work)?;
        }
        self.depth = depth;
        Ok(())
    }

    fn remove_last(
        &mut self,
        visible: &mut BTreeSet<DeclId>,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        work.tree(self.entries.len())?;
        let ((_, id), _) = self
            .entries
            .pop_last()
            .ok_or(QueryError::Invalid("missing scope record"))?;
        work.tree(visible.len())?;
        if !visible.remove(&id) {
            return Err(QueryError::Invalid("scope/visibility mismatch"));
        }
        Ok(())
    }

    pub(super) fn reset(
        &mut self,
        visible: &mut BTreeSet<DeclId>,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        while !self.entries.is_empty() {
            self.remove_last(visible, work)?;
        }
        if !visible.is_empty() {
            return Err(QueryError::Invalid("unrecorded visible declaration"));
        }
        self.depth = 0;
        work.charge(0)
    }

    pub(super) fn reset_assertions(
        &mut self,
        policy: ResetAssertionsPolicy,
        visible: &mut BTreeSet<DeclId>,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        match policy {
            ResetAssertionsPolicy::PopScopes => self.pop(self.depth, visible, work),
            ResetAssertionsPolicy::RetainDepthAndDeclarations
            | ResetAssertionsPolicy::ClearDepthRetainDeclarations => {
                loop {
                    work.tree(self.entries.len())?;
                    let Some((&(scope, _), _)) = self.entries.last_key_value() else {
                        break;
                    };
                    if scope == 0 {
                        break;
                    }
                    work.tree(self.entries.len())?;
                    let ((_, id), _) = self
                        .entries
                        .pop_last()
                        .ok_or(QueryError::Invalid("missing scope record"))?;
                    work.tree(self.entries.len())?;
                    if self.entries.insert((0, id), ()).is_some() {
                        return Err(QueryError::Invalid("duplicate flattened scope record"));
                    }
                }
                if policy == ResetAssertionsPolicy::ClearDepthRetainDeclarations {
                    self.depth = 0;
                }
                work.charge(0)
            }
        }
    }
}
