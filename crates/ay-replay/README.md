# ay-replay

Deterministic replay for LRAT proofs and a deliberately limited sequential
DRAT path.

`ay-replay` consumes a proof and its originating CNF, then rechecks the proof
without invoking SAT search again.

## Current scope

- A typed API: `ReplayPlan`, `ReplayTrace`, `ReplayOutcome`, and the
  `ProofReplayer` trait.
- A `DeterministicReplayer` implementation that wraps
  [`ay-lrat-check`](../ay-lrat-check) to re-validate proofs end-to-end.
- LRAT loading that auto-detects text vs binary format and reuses the
  `ay-lrat-check` parser — no duplicated parsing code.
- Sequential DRAT replay for proofs whose additions pass RUP; RAT-only steps
  are rejected rather than accepted without checking.
- Unit tests covering valid LRAT, corrupted bytes, parseable-but-unsound
  LRAT, and deterministic repetition.

## Usage

```rust
use ay_replay::{DeterministicReplayer, ProofReplayer, ReplayInput, ReplayOutcome};

let cnf = b"p cnf 1 2\n1 0\n-1 0\n";
let proof = b"3 0 1 2 0\n"; // derive empty clause from units 1 and 2

let mut replayer = DeterministicReplayer::new();
let plan = replayer.load_lrat(&ReplayInput { cnf, proof })?;
match replayer.replay(&plan) {
    ReplayOutcome::Success { trace } => {
        println!("OK: {} steps, {} derived", trace.steps_replayed, trace.checker_stats.derived);
    }
    ReplayOutcome::Diverged(msg) => eprintln!("replay diverged: {msg}"),
    ReplayOutcome::InvalidProof(msg) => eprintln!("bad proof: {msg}"),
}
# Ok::<(), ay_replay::ReplayError>(())
```

## Relationship to other crates

| Crate | Role vs. ay-replay |
|-------|--------------------|
| `ay-proof` | Emits LRAT; ay-replay consumes it |
| `ay-lrat-check` | LRAT verifier used under the hood |
| `ay-proof-common` | DIMACS + literal primitives |

## License

Apache-2.0 — see workspace root `LICENSE`.
