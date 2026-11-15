// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrow actual live datatype declarations for the shared exact eta proof.

use ay_core::{Sort, TermId};
use ay_frontend::DeclarationKind;
use ay_model_check::dt_eta::{self, Arguments, Budget, Fields, Kind, Member, Registry};

use crate::executor::Executor;

struct Declarations<'exec>(&'exec Executor);

impl Registry for Declarations<'_> {
    fn fields<'a>(
        &'a self,
        _owner: &'a Sort,
        constructor: &str,
        budget: &mut Budget<'_>,
    ) -> Option<Fields<'a>> {
        budget.charge(1)?;
        let member = self.0.ctx.exact_datatype_member_info(constructor)?;
        if member.declaration_kind() != DeclarationKind::DatatypeConstructor
            || !self.0.ctx.is_live_datatype_member_identity(constructor)
        {
            return None;
        }
        self.0
            .ctx
            .constructor_selector_info(constructor)
            .map(Fields::Tuples)
    }

    fn member<'a>(
        &'a self,
        _owner: &'a Sort,
        name: &'a str,
        budget: &mut Budget<'_>,
    ) -> Option<Member<'a>> {
        budget.charge(1)?;
        let member = self.0.ctx.exact_datatype_member_info(name)?;
        let kind = match member.declaration_kind() {
            DeclarationKind::DatatypeConstructor => {
                if !self.0.ctx.is_live_datatype_member_identity(name) {
                    return None;
                }
                Kind::Constructor
            }
            // Membership in the complete fields of the live constructor and
            // the exact owner/result signature are checked by the kernel.
            // Avoid the frontend's global reverse-selector liveness scan.
            DeclarationKind::DatatypeSelector => Kind::Selector,
            DeclarationKind::DatatypeTester => {
                // Exact member metadata establishes that this is a tester;
                // its generated core identity retains the constructor core.
                let constructor = name.strip_prefix("is-")?;
                if self
                    .0
                    .ctx
                    .exact_datatype_member_info(constructor)?
                    .declaration_kind()
                    != DeclarationKind::DatatypeConstructor
                    || !self.0.ctx.is_live_datatype_member_identity(name)
                    || !self.0.ctx.is_live_datatype_member_identity(constructor)
                {
                    return None;
                }
                Kind::Tester(constructor)
            }
            _ => return None,
        };
        Some(Member {
            kind,
            arguments: Arguments::Slice(&member.arg_sorts),
            result: &member.sort,
        })
    }
}

pub(super) fn is_eta(executor: &Executor, term: TermId, depth: u32) -> bool {
    if depth == 0 || !executor.ctx.canonical_operator_binding_is_unambiguous("=") {
        return false;
    }
    let stopped = || executor.poll_evaluation_stop().is_err();
    let mut budget = Budget::new(4096, &stopped);
    dt_eta::is_constructor_eta(
        &executor.ctx.terms,
        term,
        &Declarations(executor),
        &mut budget,
    )
}

#[cfg(test)]
mod tests;
