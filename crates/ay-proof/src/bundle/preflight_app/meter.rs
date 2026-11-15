// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod sorts;

pub(super) struct App<'a, 'p> {
    pub(super) entries: &'a [(TermData, Sort)],
    pub(super) node_index: usize,
    pub(super) name: &'a str,
    pub(super) args: &'a [TermId],
    pub(super) result: &'a Sort,
    pub(super) progress: &'p mut dyn FnMut(usize, usize) -> bool,
}

fn add(a: usize, b: usize) -> Result<usize, ProofCheckError> {
    a.checked_add(b).ok_or(ProofCheckError::ResourceLimit)
}

fn mul(a: usize, b: usize) -> Result<usize, ProofCheckError> {
    a.checked_mul(b).ok_or(ProofCheckError::ResourceLimit)
}

impl<'a> App<'a, '_> {
    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if (self.progress)(work, bytes) {
            Ok(())
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    }

    fn diagnostic(&mut self, reason_len: usize) -> Result<(), ProofCheckError> {
        // No recursive Sort display: only the borrowed symbol, fixed text and
        // <=3 bounded integers. Price formatting/String growth before format!.
        let bound = mul(add(add(self.name.len(), reason_len)?, 128)?, 4)?;
        self.charge(bound, bound)
    }

    pub(super) fn invalid<T>(&mut self, reason: &'static str) -> Result<T, ProofCheckError> {
        self.diagnostic(reason.len())?;
        Err(malformed_bundle(format!(
            "application term t{} has invalid builtin signature: builtin `{}` {reason}",
            self.node_index, self.name,
        )))
    }

    pub(super) fn arity(&mut self, expected: usize) -> Result<(), ProofCheckError> {
        self.charge(1, 0)?;
        if self.args.len() == expected {
            return Ok(());
        }
        self.diagnostic(64)?;
        Err(malformed_bundle(format!(
            "application term t{} has invalid builtin signature: `{}` expects {expected} arguments, got {}",
            self.node_index, self.name, self.args.len(),
        )))
    }

    pub(super) fn arg(&mut self, index: usize) -> Result<&'a Sort, ProofCheckError> {
        self.charge(1, 0)?;
        let Some(id) = self.args.get(index) else {
            return self.invalid("references a missing argument");
        };
        match self.entries.get(id.index()) {
            Some((_, sort)) => Ok(sort),
            None => self.invalid("argument references term outside the snapshot"),
        }
    }

    pub(super) fn named(&mut self, name: &str) -> Result<bool, ProofCheckError> {
        self.charge(add(self.name.len().min(name.len()), 1)?, 0)?;
        Ok(self.name == name)
    }

    pub(super) fn equal_sorts(
        &mut self,
        left: &Sort,
        right: &Sort,
    ) -> Result<bool, ProofCheckError> {
        // Price and depth-guard BOTH complete trees before recursive Eq. The
        // sort-shape authority remains in the enclosing term preflight; this
        // walk does not introduce new width/name restrictions on app matching.
        sorts::price(left, 0, self)?;
        sorts::price(right, 0, self)?;
        self.charge(0, 0)?;
        Ok(left == right)
    }

    pub(super) fn args_boolean(&mut self) -> Result<bool, ProofCheckError> {
        for index in 0..self.args.len() {
            if !matches!(self.arg(index)?, Sort::Bool) {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
