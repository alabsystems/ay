# ay-approx-bcp

**Status:** Standalone filter kernel. `ay-sat` can run it behind the
`approx-bcp-filter` feature as a measurement-only observer; no solver work
is skipped from an approximate verdict yet.

Approximate BCP pre-filter that uses 64-bit per-clause signatures to
skip clauses that provably cannot be unit or falsified under the
current partial assignment. The intended optimization places the filter
in front of exact watch-literal BCP. The current observer instead compares
the approximate verdict with an exact classification and records counters.

## Algebra

Each literal `l` (DIMACS-signed, non-zero) is hashed by splitmix to a
single-bit position in a 64-bit word:

```text
bit(l)  =  1u64 << (splitmix64(2*|l| ^ sign(l)) mod 64)
```

Per-clause signature:

```text
clause_sig   =  OR_{l ∈ clause}  bit(l)
```

Running assignment signature (OR of bits of *currently-falsified*
literals):

```text
assignment   =  OR_{l is false under trail}  bit(l)
```

The filter returns "may be unit or falsified" iff:

```text
popcount( clause_sig & !assignment )   ≤   1
```

### Soundness

Provided the assignment mask includes the signature bit of every
currently falsified literal, `popcount(clause_sig & !assignment)` is a
**lower bound** on the number of clause literals not currently falsified.
Hash collisions can only reduce the popcount. So:

* **popcount ≥ 2** ⟹ at least 2 clause literals are not falsified ⟹
  clause is neither unit nor falsified ⟹ safe to skip.
* **popcount ≤ 1** ⟹ we cannot rule out unit/falsified ⟹ fall through
  to the exact pass.

The property `clause is actually unit or falsified ⟹ filter returns
true` is checked over 10 000 deterministic pseudo-random 3-SAT samples in
`src/tests.rs::filter_never_false_negative`.

## API sketch

```rust
use ay_approx_bcp::{ClauseSignature, AssignmentMask, may_be_unit_or_falsified};

let clause_sig = ClauseSignature::from_literals(&[-1, 2, 3]);
let mut mask = AssignmentMask::empty();
mask.insert_falsified_literal(-1);
mask.insert_falsified_literal(2);

if may_be_unit_or_falsified(clause_sig, mask) {
    // fall through to exact watch-literal BCP
}
```

See `src/lib.rs` for the full public surface.

## Integration status

1. With `ay-sat/approx-bcp-filter`, the solver rebuilds an
   `AssignmentMask` from the current trail at restart boundaries and
   compares the filter with exact clause classification. This is an
   observer only.
2. A future pruning path may skip clauses only after preserving that
   exact-mask invariant. Because the bitmap is lossy, the simple sound
   backtrack policy is to rebuild it; incremental removal would require
   per-bit reference counts.
3. `FilterMetrics` records standalone skip-rate measurements. SIMD and
   cost-model work should follow evidence that pruning pays for itself.

Out of scope here: 128-bit signatures and dynamic re-hashing.

## Non-negotiables

* **Standalone.**  No `ay-sat` dependency — the crate is driven by
  DIMACS-style `i32` literals and exposes only pure functions.
* **Soundness tested.**  `cargo test -p ay-approx-bcp` runs the 10 000-
  sample deterministic randomized property test plus focused unit tests.
* **No `unsafe`.**  `#![forbid(unsafe_code)]` at the crate root.
