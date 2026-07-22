# ay-proof-complexity

Proof-complexity primitives for AY: classical hard-formula generators plus a
cheap per-instance structural feature vector that downstream benchmarking and
regression-diff tooling can attach to every row.

The crate is intentionally self-contained — it depends only on `ay-sat`'s CNF
type (via `crate::cnf::Cnf`) and `serde`. No SMT or SAT solving happens here.

## What it computes

All features are derived in a single O(clauses * average_width) pass over the
CNF clause database. Every number is finite and non-negative.

| Field | Type | Meaning |
|-------|------|---------|
| `num_vars` | `u32` | Declared variable count. |
| `num_clauses` | `u32` | Clause count. |
| `clause_width_max` | `u32` | Longest clause. |
| `clause_width_mean` | `f64` | Average clause width (0.0 for empty formula). |
| `xor_density` | `f64` ∈ [0,1] | Fraction of width-3 clauses that fit a 3-XOR polarity pattern — the larger of the (even-positives, odd-positives) counts divided by total clauses. Width-3 parity encodings (see `parity`) land at 1.0; random 3-CNF stays below 0.5. |
| `cardinality_density` | `f64` ∈ [0,1] | Fraction of clauses that are width-2, all-negative literals — the shape of an "at-most-one" cardinality constraint (see `pigeonhole`). |
| `modularity` | `f64` ∈ [0,1] | Community-structure proxy: `1 - (bucket_spread_weight / total_width)` with variables bucketed by `var_id % ceil(sqrt(num_vars))`. Higher = more community structure. |
| `vig_density` | `f64` ∈ [0,1] | Density of the variable-interaction graph (VIG), `2*E/(V*(V-1))`, where an edge `{u,v}` exists when some clause mentions both variables. `0.0` for `num_vars < 2`. |
| `treewidth_approx` | `Option<f64>` | Min-degree elimination upper bound on `tw(VIG)` (Bodlaender 1993; Bodlaender & Koster 2010). Computed on a deterministic subsample when `num_vars > 1024`. `None` only when the VIG has no vertices. |
| `pigeonhole_score` | `f64` ∈ [0,1] | PHP-style encoding fingerprint: product of (a) fraction of variables participating in a width-2 all-negative AMO clause, and (b) `min(1, amo_pair_count / alo_wide_count)` where `alo_wide_count` is the number of all-positive clauses of width `>= 2`. Saturates at `1.0` for `pigeonhole(n)`. |

The densities and scores are heuristics, not exact decoders. They are chosen
to be deterministic, cheap, and discriminative between the families the crate
already generates (`pigeonhole`, `parity`, `tseitin`, `random_k_cnf`,
`ordering_principle`).

### Extended features (treewidth, pigeonhole, VIG density)

- `vig_density` is the raw interaction-graph density, independent of the
  clause-level modularity proxy. Pigeonhole and ordering-principle instances
  have high VIG density (all-to-all interaction); long-cycle Tseitin formulas
  are near the inverse `1/V`.
- `treewidth_approx` runs the min-degree elimination heuristic: iteratively
  pick a minimum-degree vertex, record its current degree, clique its
  neighbours, and repeat. The maximum recorded degree is a valid upper bound
  on `tw(G)` (Bodlaender 1993). For paths we recover `tw = 1`; for `K_n`
  we recover `tw = n - 1`; for industrial VIGs the bound is typically
  loose but correlates with hardness.
- `pigeonhole_score` is a fingerprint, not a decision procedure: it returns
  `1.0` on `pigeonhole(n)`, `0.0` on pure parity/XOR formulas, and `< 0.2`
  on random 3-CNF.

## Generated baseline dataset

The example generator writes
the development design notes locally (58 instances).
That generated result is not shipped as benchmark evidence. Every line has
`{name, family, params, features}`. The generated corpus is:

| Family              | Instances | Parameters |
|---------------------|-----------|------------|
| `php`               | 8         | k = 3..10  |
| `parity`            | 17        | n = 4..20 |
| `tseitin`           | 10        | cycles (n=4..12), grids (2x3, 3x3, 3x4), complete graphs (n=4, 5) |
| `random-k-cnf`      | 16        | k=3; n ∈ {20, 30, 50, 80}; ratios 2.0..4.5 around the 3-SAT threshold |
| `ordering-principle`| 7         | n = 4..10  |

Regenerate with:

```bash
cargo run --example baseline_dataset -p ay-proof-complexity --release
```

The generator is deterministic (seeded), so a given source revision produces
the same rows. Preserve the generated file with commit and environment
provenance before using it as evidence.

## Example

```rust
use ay_proof_complexity::{parity, ProofComplexityFeatures};

let cnf = parity(3);
let f = ProofComplexityFeatures::from_cnf(&cnf);
assert_eq!(f.num_clauses, 4);
assert!((f.xor_density - 1.0).abs() < 1e-9);
```

## Wiring into `ay-bench`

Features are exposed to the benchmark harness through two entry points:

1. `ay bench features <FILE>` — prints `ProofComplexityFeatures` (plus a
   `family` hint and `extract_ms` timing) as pretty JSON. Currently accepts
   `.cnf` / `.dimacs`; other formats return a typed error.
2. `ay bench run --with-features` — during a regular benchmark run, each
   benchmark file is parsed and its features are written alongside the usual
   runtime/verdict columns in `.ay-bench/results.sqlite`. The columns are
   added by an idempotent `ALTER TABLE` migration, so pre-existing stores
   upgrade in place and rows without features continue to roundtrip as
   `NULL`.

The per-row schema extends `ResultRow` with the seven optional fields
(`family`, `clause_width_max`, `clause_width_mean`, `xor_density`,
`cardinality_density`, `modularity`, `feature_extract_ms`). Downstream tools
(diff, scoring) ignore the new columns unless they opt in.

## References

- Ansotegui, Bonet, Levy (2012), *The Community Structure of SAT Formulas*
  — motivation for `modularity`.
- Haken (1985), *The intractability of resolution* — pigeonhole lower bounds,
  motivation for `cardinality_density` and `pigeonhole_score`.
- Urquhart (1987), *Hard examples for resolution* — Tseitin / parity
  formulas, motivation for `xor_density`.
- Bodlaender (1993), *A Tourist Guide Through Treewidth* — min-degree
  elimination heuristic used by `treewidth_approx`.
- Bodlaender & Koster (2010), *Treewidth Computations I. Upper Bounds*,
  *Information and Computation* — survey of practical treewidth upper-bound
  heuristics.
- Biere, Heule, van Maaren, Walsh (2021), *Handbook of Satisfiability*,
  chapter on instance features.
