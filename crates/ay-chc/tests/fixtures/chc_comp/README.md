# Vendored CHC-COMP benchmark fixtures

These `.smt2` files are verbatim copies of individual benchmarks from the
CHC-COMP benchmark repositories. They are vendored so that every regression
that depends on them is **hermetic**: `cargo test -p ay-chc` runs them on a
fresh checkout with no network, no download, and no environment setup.

## Why vendored and not downloaded

A test that needs a multi-gigabyte external corpus is a test that does not run.
The two CHC-COMP-25 regressions here need three specific files totalling ~140 KB
out of a ~1.2 GB corpus, so the corpus dependency bought nothing but an
`#[ignore]` — and an ignored test is unenforced coverage that rots silently.

The repository policy is enforced mechanically: `ay-quality-gate` fails on any
`#[ignore]` in workspace-owned Rust source. Do not re-introduce one here. If a
regression needs a new benchmark, **vendor the single file** using the refresh
procedure below.

Vendor only what a test actually reads. This directory is for individual named
benchmarks, not for corpus subsets — bulk corpora belong under `benchmarks/`
and are fetched with `ay corpus download`.

## Layout

| Path | Upstream source |
|---|---|
| `hcai/svcomp/O0/` | `hcai-bench/svcomp/O0/` |
| `solidity/` | `solidity/no_adts/unit_tests/abi/` |
| `kind2/`, `llreve/`, `reve/` | the correspondingly named upstream trees |

Local paths flatten the upstream directory names (`hcai-bench` → `hcai`); the
table above is the mapping.

## Provenance

All CHC-COMP-25 files come from
<https://github.com/chc-comp/chc-comp25-benchmarks> pinned at commit
`ddd279cab0717db6effe69baad451a8eb04ffd86`, the same commit
`benchmarks/corpora.toml` pins for the `chc-comp-2025-benchmarks` and
`chc-comp-2025-extra-small-lia-fixtures` corpora. Upstream states the benchmarks
were preprocessed with the CHC-COMP formatter and carry benchexec metadata whose
expected verdict is `true` (all solvers reporting agreed on `sat`) or `false`
(all agreed on `unsat`).

Upstream publishes no top-level licence file. These are competition benchmarks
redistributed for regression testing; confirm terms before redistributing them
outside this repository.

## Refreshing or adding a fixture

`benchmarks/corpora.toml` carries a dedicated entry for this purpose —
`chc-comp-2025-extra-small-lia-fixtures` — whose whole job is to clone upstream
so individual fixtures can be copied across. A blobless clone avoids pulling the
full corpus:

```bash
git clone --filter=blob:none --no-checkout \
  https://github.com/chc-comp/chc-comp25-benchmarks.git /tmp/chc25
git -C /tmp/chc25 checkout ddd279cab0717db6effe69baad451a8eb04ffd86 -- <upstream/path/to.smt2>
cp /tmp/chc25/<upstream/path/to.smt2> crates/ay-chc/tests/fixtures/chc_comp/<local/path>/
```

Then reference it with `include_str!` — never `std::fs::read_to_string` on a
`benchmarks/` path, which is what forces the `#[ignore]`:

```rust
const MY_FIXTURE: &str =
    include_str!("../tests/fixtures/chc_comp/<local/path>/<name>.smt2");
```

Note the `include_str!` path is relative to the **source file**, so it differs
between `src/` unit tests (`../tests/fixtures/...`, or `../../` from a
subdirectory) and `tests/` integration tests (`../fixtures/...`).

If you bump the pinned commit, bump it in `benchmarks/corpora.toml` too and
re-copy every fixture listed above, so the pin and the fixtures cannot drift.

## Consumers

- `crates/ay-chc/tests/group_soundness/kind_soundness.rs` — `hcai/svcomp/O0/O0_id_*`, `O0_sum_*`, `kind2/*`
- `crates/ay-chc/tests/group_misc/cyclic_array_bmc_unsafe_swaparray.rs` — `llreve/*`
- `crates/ay-chc/tests/group_soundness/query_safety_free_vars_022c.rs` — `reve/*`

### Staged, not yet wired

`solidity/abi_encode_array_slice.sol_0_no_adts_000.smt2` and
`solidity/abi_encode_packed_array_slice.sol_0_no_adts_000.smt2` were vendored on
2026-07-25 to de-`#[ignore]`
`crates/ay-chc/src/bmc/tests.rs::nested_select_candidate_refutes_both_chccomp25_array_slice_targets`.

**That test fails when actually run against these benchmarks**, so the wiring
was not landed. It currently reads the corpus from `benchmarks/` and returns
early when it is absent — and `benchmarks/chc/chc-comp25-benchmarks/` is
gitignored — so it asserts nothing on any checkout that lacks the 1.2 GB
corpus, and is `#[ignore]`d on those that have it.

Observed against the fixtures above (identical to upstream at the pinned commit,
verified byte-for-byte):

| Test | Expected | Actual |
|---|---|---|
| `nested_select_candidate_refutes_...` | replay-validated `Unsafe` | `Unknown` |

Not a budget effect: it still fails with the budgets raised to 120 s and BMC
depth raised to 64 (it concludes in ~2 s at the committed budgets). Once the
underlying capability holds, swap the test to `include_str!` on the fixtures
above and delete its `#[ignore]` and early-return.

`hcai/svcomp/O0/O0_lu.cmp_true-unreach-call_000.smt2` is also staged, for
`crates/ay-chc/src/adaptive_tests.rs::test_reduced_lia_array_interval_model_solves_hcai_lu_cmp`
— but for the opposite reason: **the capability now works and the test is still
not wired, because it cannot be made to pass reliably.**

The root cause was that `IntervalPropagator` had no Boolean reasoning at all, so
on SeaHorn-style guarded CNF (`(or (not g) (= x 0))` plus reified loop guards
like `(not (= (<= 6 h) g))`) it derived no bound whatsoever and the reduced
LIA-array route returned `None`. That is fixed — see
`crates/ay-chc/src/transform/interval_propagation.rs`. Unloaded, the route now
derives `main@_bb2 arg1 in [0,6]` / `main@_bb arg1 in [0,7]` and returns
`Safe` / `FullVerification` in ~0.5 s, and the model passes independent
original-clause validation under `strict_proofs`.

It is a **wall-clock race**, not a capability gap. `IntervalPropagator`'s pass
budget is `PassBudget::new(Instant::now() + Duration::from_secs(1),
PASS_WORK_BUDGET)` — a hardcoded one-second wall deadline alongside a
1,000,000-unit fuel cap — and
`REDUCED_LIA_ARRAY_ROUTE_BUDGET` clamps the route to 3 s no matter what the
caller passes. Under CPU contention the pass blows the wall deadline before it
exhausts its fuel, fails closed to identity, and the route declines. Reproduced
standalone against 24 busy cores: the route declines in 2.06 s, and raising the
*caller's* budget to 60 s does not help because of the clamp. It also failed
inside `cargo test -p ay-chc`'s own parallelism while passing in isolation.

Wiring it would therefore add a test that fails on any loaded machine. The
fix belongs in the pass: make it bounded by its deterministic fuel cap rather
than by wall-clock, which is also what the repo's own measurement discipline
asks for. That change alters solver behaviour on every problem and needs a
corpus differential before landing, so it is left as follow-up. Once the pass is
deterministic, wire this test the same way as the others and delete its
`#[ignore]`.
