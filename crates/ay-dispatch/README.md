# ay-dispatch

Shared engine-dispatch primitives for AY portfolios.

Today both `ay-chc` and `ay-sat` carry their own classifier / selector /
scheduler / bandit code. This crate is the shared home for those pieces and
for future solver portfolio integrations.

## What's in the box (Phase 1)

* `ProblemFeatures` and `EngineId` marker traits.
* `ProblemClassifier` — extract features from a raw problem encoding.
* `EngineSelector` — pick an ordered engine list from those features.
* `PortfolioSchedule` — allocate per-engine time budgets.
* `FixedOrderSchedule` — reference implementation of `PortfolioSchedule`
  with `equal_share` and `weighted` constructors.
* `MultiplicativeWeights` — full-information Hedge bandit.
* `Exp3` — partial-information adversarial bandit.
* Deterministic xorshift `Rng` for reproducible sampling.

## What's **not** in the box yet

* No migration of the existing `ay-chc` / `ay-sat` portfolios (Phases 2 & 3).
* No stochastic-bandit algorithms (`UCB1`, Thompson sampling) — the SAT
  portfolio keeps its own `BranchSelectorUCB1` until Phase 3.
* No persistence / serde for bandit state — downstream crates can add
  feature-gated serde on top if needed.

## Worked example

```rust
use std::time::Duration;
use ay_dispatch::{
    EngineId, ProblemFeatures, ProblemClassifier, EngineSelector,
    PortfolioSchedule, FixedOrderSchedule, MultiplicativeWeights,
};

// 1. Define your domain types.
#[derive(Debug, Clone)]
struct CnfFeatures {
    num_vars: usize,
    clause_var_ratio: f64,
}
impl ProblemFeatures for CnfFeatures {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum SatStrategy {
    VsidsLuby,
    VsidsGlucose,
    AggressiveInprocessing,
}
impl EngineId for SatStrategy {}

// 2. Plug in your classifier.
struct CnfClassifier;
impl ProblemClassifier for CnfClassifier {
    type Features = CnfFeatures;
    fn classify(&self, input: &[u8]) -> CnfFeatures {
        // ... walk the DIMACS header, count variables, etc.
        CnfFeatures { num_vars: input.len(), clause_var_ratio: 4.2 }
    }
}

// 3. Plug in your selector.
struct RatioSelector;
impl EngineSelector for RatioSelector {
    type Features = CnfFeatures;
    type Engine = SatStrategy;
    fn select(&self, f: &CnfFeatures) -> Vec<SatStrategy> {
        if f.clause_var_ratio > 4.0 {
            vec![
                SatStrategy::VsidsGlucose,
                SatStrategy::AggressiveInprocessing,
                SatStrategy::VsidsLuby,
            ]
        } else {
            vec![SatStrategy::VsidsLuby, SatStrategy::VsidsGlucose]
        }
    }
}

// 4. Dispatch.
let features = CnfClassifier.classify(b"p cnf ...");
let engines = RatioSelector.select(&features);
let schedule = FixedOrderSchedule::equal_share(engines, Duration::from_secs(30));
for (engine, budget) in schedule.next_engines(Duration::ZERO, Duration::from_secs(30)) {
    // Run your solver for `engine` with timeout `budget`.
    let _ = (engine, budget);
}

// 5. Update a bandit once you have per-engine rewards.
let mut mw = MultiplicativeWeights::new(
    [
        SatStrategy::VsidsLuby,
        SatStrategy::VsidsGlucose,
        SatStrategy::AggressiveInprocessing,
    ],
    0.2,
    /* seed */ 1,
);
mw.update(SatStrategy::VsidsGlucose, 1.0);
let distribution = mw.distribution();
let _ = distribution;
```

## Testing

```bash
cargo test -p ay-dispatch
```

## Stability

`ay-dispatch` is pre-1.0 and will change as Phases 2 and 3 of #8775 migrate
the existing portfolios. Consumers outside of the workspace should pin the
exact revision.
