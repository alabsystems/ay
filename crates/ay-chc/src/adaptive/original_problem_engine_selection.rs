// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::AdaptivePortfolio;
use crate::portfolio::features::ChcFeatureExtractor;
use crate::portfolio::selector::EngineSelector;
use crate::portfolio::PortfolioConfig;

impl AdaptivePortfolio {
    /// Prioritize a guarded route's existing engines using original-problem features.
    ///
    /// W4-2C must not replace the specialized non-Real portfolios: those
    /// configurations carry route-specific PDR variants, complete BMC lanes,
    /// and the datatype guards from #7930. Reordering the existing roster puts
    /// fragment-matched engines in the first capacity wave while retaining
    /// every fallback and its configuration. Call this only at an
    /// original-problem route boundary, never inside a builder reused by a
    /// transformed BV-to-Bool/BV-to-Int lane.
    pub(crate) fn apply_original_problem_engine_selection(&self, config: &mut PortfolioConfig) {
        let features = ChcFeatureExtractor::extract(&self.problem);
        let selection = EngineSelector::select(&features);

        // Match one existing lane per selected lane. A type-only partition
        // would pull every PDR variant forward when the selector requested
        // one, crowding complementary engines out of a caller-capped first
        // wave. Unmatched duplicates and fragment fallbacks remain in their
        // route-defined relative order at the tail.
        let mut remaining = std::mem::take(&mut config.engines);
        for selected in &selection.engines {
            if let Some(position) = remaining
                .iter()
                .position(|engine| engine.engine_type() == selected.engine_type())
            {
                config.engines.push(remaining.remove(position));
            }
        }
        config.engines.extend(remaining);
    }
}
