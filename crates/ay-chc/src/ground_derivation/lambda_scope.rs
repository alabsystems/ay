// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private template binders are typed code, not ground environment bindings.

use super::*;
use crate::expr::ChcArrayLambda;

impl GroundSourceSurfaceCache<'_> {
    pub(super) fn reserve_lambda_metadata(
        &mut self,
        lambda: &ChcArrayLambda,
        control: &mut GroundValidationControl<'_>,
    ) -> Result<usize, GroundSourceSurfaceError> {
        let start = self.work_used;
        for variable in std::iter::once(lambda.binder()).chain(lambda.formals()) {
            control.poll()?;
            self.charge(
                variable
                    .name
                    .len()
                    .checked_add(64)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
            )?;
            self.reserve_source_sort(&variable.sort, control)?;
        }
        self.work_used
            .checked_sub(start)
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)
    }

    pub(super) fn reserve_bound_variable(
        &mut self,
        lambda: &ChcArrayLambda,
        variable: &ChcVar,
        sort_work: usize,
    ) -> Result<(), GroundSourceSurfaceError> {
        self.charge(
            lambda
                .formals()
                .len()
                .checked_add(1)
                .and_then(|n| {
                    variable
                        .name
                        .len()
                        .checked_add(1)
                        .and_then(|bytes| n.checked_mul(bytes))
                })
                .and_then(|work| work.checked_add(sort_work))
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
        )?;
        let declared = std::iter::once(lambda.binder())
            .chain(lambda.formals())
            .find(|formal| formal.name == variable.name);
        if declared != Some(variable) {
            return Err(GroundSourceSurfaceError::InvalidVariableSurface);
        }
        Ok(())
    }
}
