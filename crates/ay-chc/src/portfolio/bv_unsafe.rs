// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::Counterexample;

impl PortfolioSolver {
    pub(super) fn confirm_bv_abstracted_unsafe(
        &self,
        cex: &Counterexample,
        idx: usize,
        engine_name: &str,
    ) -> Option<PortfolioResult> {
        // Early bail if the portfolio has been cancelled (#8630).
        // This avoids entering the expensive validate_unsafe path (which
        // creates a fresh PdrSolver and runs verify_counterexample) when
        // the portfolio's timeout has already expired or another engine won.
        if self.cancellation_token.is_cancelled() {
            if self.config.verbose {
                safe_eprintln!(
                    "Portfolio: Engine {} ({}) BV-domain confirmation skipped — cancelled",
                    idx,
                    engine_name,
                );
            }
            return None;
        }
        match self.validate_unsafe(cex) {
            ValidationResult::Valid => Some(PortfolioResult::Unsafe(
                self.back_translator.translate_invalidity(cex.clone()),
            )),
            ValidationResult::Invalid(reason) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Engine {} ({}) Unsafe rejected \
                         during original-domain confirmation: {}",
                        idx,
                        engine_name,
                        reason
                    );
                }
                None
            }
        }
    }
}
