// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lexically scoped single-binder SMT array lambdas.

use super::ChcParser;
use crate::{ChcError, ChcExpr, ChcResult, ChcVar};

impl ChcParser {
    pub(super) fn parse_lambda_expr(&mut self) -> ChcResult<ChcExpr> {
        self.skip_whitespace_and_comments();
        self.expect_char('(')?;
        self.skip_whitespace_and_comments();
        self.expect_char('(')?;
        let name = self.parse_symbol()?;
        self.skip_whitespace_and_comments();
        let sort = self.parse_sort()?;
        self.skip_whitespace_and_comments();
        self.expect_char(')')?;
        self.skip_whitespace_and_comments();
        self.expect_char(')')?;

        let fresh = self.fresh_binder_name(&name);
        let old = self.variables.insert(fresh.clone(), sort.clone());
        let renames = self.active_renames.len();
        self.active_renames.push((name, fresh.clone()));
        self.lambda_depth += 1;
        let body = self.parse_expr();
        self.lambda_depth -= 1;
        self.active_renames.truncate(renames);
        match old {
            Some(value) => {
                self.variables.insert(fresh.clone(), value);
            }
            None => {
                self.variables.remove(&fresh);
            }
        }
        let body = body?;
        self.skip_whitespace_and_comments();
        self.expect_char(')')?;
        ChcExpr::array_lambda(ChcVar::new(fresh, sort), body)
            .map_err(|error| ChcError::Parse(format!("invalid array lambda: {error}")))
    }
}
